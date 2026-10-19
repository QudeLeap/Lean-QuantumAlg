/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BasisMap
import all QuantumAlg.Util.ModularMultiplicationDomain
import all QuantumAlg.Util.ZModUnits
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate
import all QuantumAlg.Primitives.MAU.Multiplication
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate

/-!
# Uniform fixed-layout VBE multiply-accumulate circuit

This module folds the VBE controlled modular-add route over every wire of one
actual multiplier register.  Each bit controls a concrete constant
load/add/unload program on the same fixed layout [VBE95,
9511018.tex:333-367].  Program selection is independent of the input value;
semantic correctness and all resource projections use the same folded circuit.
-/

section

namespace QuantumAlg
namespace MAU.Multiplication.Accumulate
namespace VBECircuit

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- The complete multiplier word paired with the reusable VBE arithmetic
workspace.  No isolated classical multiplier bit or fixed-true control ancilla
is present. -/
structure Registers (n : Nat) where
  /-- The complete multiplier word whose bits control the fixed stages. -/
  multiplicand : PlainAdder.Word n
  /-- The shared VBE modular-add workspace used by every stage. -/
  arithmetic : MAU.Addition.VBECircuit.Registers n
deriving DecidableEq

/-- Product representation used to construct the fixed binary encoding. -/
abbrev RawRegisters (n : Nat) : Type :=
  PlainAdder.Word n × MAU.Addition.VBECircuit.Registers n

/-- Equivalence between the named register structure and its product layout. -/
def registersEquiv (n : Nat) : Registers n ≃ RawRegisters n where
  toFun := fun x => (x.multiplicand, x.arithmetic)
  invFun := fun x => { multiplicand := x.1, arithmetic := x.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- Product encoding before relabeling it to the named register structure. -/
def rawEncoding (n : Nat) : BinaryLabelEncoding (RawRegisters n) :=
  BinaryLabelEncoding.prod
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n)
    (MAU.Addition.VBECircuit.encoding n)

/-- One uniform `5*n+4` layout for the multiplier and arithmetic workspace. -/
def encoding (n : Nat) : BinaryLabelEncoding (Registers n) :=
  (rawEncoding n).relabel (registersEquiv n)

@[simp] lemma encoding_width (n : Nat) :
    (encoding n).width = 5 * n + 4 := by
  simp [encoding, rawEncoding,
    PlainAdder.Schedule.PowerOfTwo.wordEncoding,
    MAU.Addition.VBECircuit.AdderWidth]
  omega

/-- One multiplier wire in the full MAC layout. -/
def multiplicandBit (n : Nat) (bit : Fin n) : EncodedBit (encoding n) :=
  (BinaryLabelEncoding.prodLeftBit
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n)
    (MAU.Addition.VBECircuit.encoding n)
    (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)).relabel
      (registersEquiv n)

/-- The complete encoded multiplier word in the shared layout. -/
def multiplicandWord (n : Nat) : EncodedBit.Word (encoding n) n where
  bit := multiplicandBit n

/-- Lift an arithmetic-workspace bit past the complete multiplier word. -/
def liftArithmeticBit (n : Nat)
    (bit : EncodedBit (MAU.Addition.VBECircuit.encoding n)) :
    EncodedBit (encoding n) :=
  (BinaryLabelEncoding.prodRightBit
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n)
    (MAU.Addition.VBECircuit.encoding n) bit).relabel (registersEquiv n)

/-- Lifting arithmetic bits into the full MAC layout preserves wire
distinctness. -/
lemma liftArithmeticBit_ne (n : Nat)
    {left right : EncodedBit (MAU.Addition.VBECircuit.encoding n)}
    (hne : left.wire ≠ right.wire) :
    (liftArithmeticBit n left).wire ≠
      (liftArithmeticBit n right).wire := by
  intro h
  apply hne
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [liftArithmeticBit, EncodedBit.relabel,
    BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire] using hv

/-- Lift one arithmetic-workspace gate past the complete multiplier word. -/
def liftArithmeticGate (n : Nat) :
    EncodedBit.GateSpec (MAU.Addition.VBECircuit.encoding n) →
      EncodedBit.GateSpec (encoding n)
  | .x target => .x (liftArithmeticBit n target)
  | .cnot control target hct =>
      .cnot (liftArithmeticBit n control) (liftArithmeticBit n target)
        (liftArithmeticBit_ne n hct)
  | .toffoli controlA controlB target hab ha hb =>
      .toffoli (liftArithmeticBit n controlA)
        (liftArithmeticBit n controlB) (liftArithmeticBit n target)
        (liftArithmeticBit_ne n hab) (liftArithmeticBit_ne n ha)
        (liftArithmeticBit_ne n hb)

@[simp] private lemma event_liftArithmeticGate (n : Nat)
    (gate : EncodedBit.GateSpec (MAU.Addition.VBECircuit.encoding n)) :
    (EncodedBit.GateSpec.event .empty) (liftArithmeticGate n gate) =
      (EncodedBit.GateSpec.event .empty) gate := by
  cases gate <;> rfl

private lemma step_liftArithmeticGate (n : Nat)
    (gate : EncodedBit.GateSpec (MAU.Addition.VBECircuit.encoding n))
    (x : Registers n) :
    (liftArithmeticGate n gate).step x =
      { x with arithmetic := gate.step x.arithmetic } := by
  cases x with
  | mk multiplicand arithmetic =>
      cases gate with
      | x target =>
          rfl
      | cnot control target hct =>
          by_cases hcontrol : control.get arithmetic <;>
            simp [liftArithmeticGate, EncodedBit.GateSpec.step,
              EncodedBit.cnotStep, liftArithmeticBit, EncodedBit.relabel,
              BinaryLabelEncoding.prodRightBit, registersEquiv, hcontrol]
      | toffoli controlA controlB target hab ha hb =>
          by_cases hcontrols :
              controlA.get arithmetic && controlB.get arithmetic <;>
            simp [liftArithmeticGate, EncodedBit.GateSpec.step,
              EncodedBit.toffoliStep, liftArithmeticBit,
              EncodedBit.relabel, BinaryLabelEncoding.prodRightBit,
              registersEquiv, hcontrols]

private lemma stepList_liftArithmeticGates (n : Nat) :
    ∀ (gates : List
        (EncodedBit.GateSpec (MAU.Addition.VBECircuit.encoding n)))
      (x : Registers n),
      EncodedBit.GateSpec.stepList
          (gates.map (liftArithmeticGate n)) x =
        { x with
          arithmetic := EncodedBit.GateSpec.stepList gates x.arithmetic }
  | [], x => by cases x; rfl
  | gate :: rest, x => by
      change
        EncodedBit.GateSpec.stepList
            (rest.map (liftArithmeticGate n))
            ((liftArithmeticGate n gate).step x) =
          { x with
            arithmetic :=
              EncodedBit.GateSpec.stepList rest (gate.step x.arithmetic) }
      rw [step_liftArithmeticGate]
      simpa using stepList_liftArithmeticGates n rest
        { x with arithmetic := gate.step x.arithmetic }

/-- One lifted bit of the active-source register. -/
def activeSourceBit (n : Nat)
    (bit : Fin (MAU.Addition.VBECircuit.AdderWidth n)) :
    EncodedBit (encoding n) :=
  liftArithmeticBit n (MAU.Addition.VBECircuit.activeSourceBit n bit)

/-- The lifted active-source word in the complete MAC layout. -/
def activeSourceWord (n : Nat) :
    EncodedBit.Word (encoding n) (MAU.Addition.VBECircuit.AdderWidth n) where
  bit := activeSourceBit n

/-- The VBE reduction flag lifted into the complete MAC layout.  Clean
load/unload endpoints use this known-false wire as the null control of the
constant-schedule compiler. -/
def reductionFlagBit (n : Nat) : EncodedBit (encoding n) :=
  liftArithmeticBit n (MAU.Addition.VBECircuit.reductionFlagBit n)

/-- One lifted bit of the arithmetic target register. -/
def targetBit (n : Nat)
    (bit : Fin (MAU.Addition.VBECircuit.AdderWidth n)) :
    EncodedBit (encoding n) :=
  liftArithmeticBit n (MAU.Addition.VBECircuit.targetBit n bit)

/-- The lifted arithmetic target word in the complete MAC layout. -/
def targetWord (n : Nat) :
    EncodedBit.Word (encoding n) (MAU.Addition.VBECircuit.AdderWidth n) where
  bit := targetBit n

@[simp] lemma multiplicandBit_get (n : Nat) (bit : Fin n)
    (x : Registers n) :
    (multiplicandBit n bit).get x =
      x.multiplicand.val.testBit bit.val := by
  change
    (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get x.multiplicand =
      x.multiplicand.val.testBit bit.val
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit x.multiplicand

@[simp] lemma liftArithmeticBit_get (n : Nat)
    (bit : EncodedBit (MAU.Addition.VBECircuit.encoding n))
    (x : Registers n) :
    (liftArithmeticBit n bit).get x = bit.get x.arithmetic := by
  rfl

@[simp] lemma activeSourceBit_get (n : Nat)
    (bit : Fin (MAU.Addition.VBECircuit.AdderWidth n))
    (x : Registers n) :
    (activeSourceBit n bit).get x =
      x.arithmetic.activeSource.val.testBit bit.val := by
  change
    (MAU.Addition.VBECircuit.activeSourceBit n bit).get x.arithmetic =
      x.arithmetic.activeSource.val.testBit bit.val
  rw [MAU.Addition.VBECircuit.activeSourceBit_get,
    PlainAdder.Schedule.PowerOfTwo.wordBit_get]

@[simp] lemma targetBit_get (n : Nat)
    (bit : Fin (MAU.Addition.VBECircuit.AdderWidth n))
    (x : Registers n) :
    (targetBit n bit).get x = x.arithmetic.target.val.testBit bit.val := by
  change
    (MAU.Addition.VBECircuit.targetBit n bit).get x.arithmetic =
      x.arithmetic.target.val.testBit bit.val
  rw [MAU.Addition.VBECircuit.targetBit_get,
    PlainAdder.Schedule.PowerOfTwo.wordBit_get]

lemma multiplicand_activeSource_ne (n : Nat) (multiplierBit : Fin n) :
    ∀ sourceBit,
      (multiplicandBit n multiplierBit).wire ≠
        ((activeSourceWord n).bit sourceBit).wire := by
  intro sourceBit h
  have hv := congrArg Fin.val h
  have hlt :
      (PlainAdder.Schedule.PowerOfTwo.wordBit n multiplierBit).wire.val <
        (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width :=
    (PlainAdder.Schedule.PowerOfTwo.wordBit n multiplierBit).wire.isLt
  simp [multiplicandBit, activeSourceWord, activeSourceBit,
    liftArithmeticBit, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hv
  omega

lemma activeSource_pairwise_ne (n : Nat) :
    ∀ left right,
      left ≠ right →
        ((activeSourceWord n).bit left).wire ≠
          ((activeSourceWord n).bit right).wire := by
  intro left right hne h
  have hv := congrArg Fin.val h
  have hraw :
      (MAU.Addition.VBECircuit.activeSourceBit n left).wire.val =
        (MAU.Addition.VBECircuit.activeSourceBit n right).wire.val := by
    simpa [activeSourceWord, activeSourceBit, liftArithmeticBit,
      EncodedBit.relabel, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.prodRightWire] using hv
  exact MAU.Addition.VBECircuit.activeSource_pairwise_ne n left right hne
    (Fin.ext hraw)

@[simp] lemma reductionFlagBit_get (n : Nat) (x : Registers n) :
    (reductionFlagBit n).get x = x.arithmetic.reductionFlag := by
  rfl

/-- Lifting the VBE arithmetic workspace past the complete multiplier word
preserves every separation internal to that workspace. -/
lemma activeSource_liftArithmetic_ne (n : Nat)
    (observed : EncodedBit (MAU.Addition.VBECircuit.encoding n))
    (hne : ∀ bit,
      ((MAU.Addition.VBECircuit.activeSourceWord n).bit bit).wire ≠
        observed.wire) :
    ∀ bit,
      ((activeSourceWord n).bit bit).wire ≠
        (liftArithmeticBit n observed).wire := by
  intro bit h
  change
    (BinaryLabelEncoding.prodRightBit
      (PlainAdder.Schedule.PowerOfTwo.wordEncoding n)
      (MAU.Addition.VBECircuit.encoding n)
      (MAU.Addition.VBECircuit.activeSourceBit n bit)).wire =
    (BinaryLabelEncoding.prodRightBit
      (PlainAdder.Schedule.PowerOfTwo.wordEncoding n)
      (MAU.Addition.VBECircuit.encoding n) observed).wire at h
  have hv := congrArg Fin.val h
  change
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width +
        (MAU.Addition.VBECircuit.activeSourceBit n bit).wire.val =
      (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width +
        observed.wire.val at hv
  have hval :
      (MAU.Addition.VBECircuit.activeSourceBit n bit).wire.val =
        observed.wire.val := by
    omega
  apply hne bit
  apply Fin.ext
  simpa only [MAU.Addition.VBECircuit.activeSourceWord] using hval

lemma reductionFlag_activeSource_ne (n : Nat) :
    ∀ bit,
      (reductionFlagBit n).wire ≠ ((activeSourceWord n).bit bit).wire := by
  intro bit
  exact Ne.symm <| activeSource_liftArithmetic_ne n
    (MAU.Addition.VBECircuit.reductionFlagBit n)
    (fun sourceBit => Ne.symm
      (MAU.Addition.VBECircuit.reductionFlag_activeSource_ne n sourceBit))
    bit

/-- A small natural fits the same way in the low word and its one-bit-wider
VBE target word. -/
lemma widenWord_natCast_of_lt (n value : Nat) (hvalue : value < 2 ^ n) :
    MAU.Addition.VBECircuit.widenWord n
        (value : PlainAdder.Word n) =
      (value : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) := by
  apply ZMod.val_injective
  rw [MAU.Addition.VBECircuit.widenWord_val,
    ZMod.val_natCast_of_lt hvalue]
  have hpow : 2 ^ n < 2 ^ (MAU.Addition.VBECircuit.AdderWidth n) := by
    simp [MAU.Addition.VBECircuit.AdderWidth, pow_succ]
  exact (ZMod.val_natCast_of_lt (lt_trans hvalue hpow)).symm

/-- Named full-layout state with an arbitrary active source and otherwise
clean VBE work registers. -/
def workspaceState (n : Nat) (multiplicand active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n))
    (flag : Bool) : Registers n where
  multiplicand := multiplicand
  arithmetic := MAU.Addition.VBECircuit.sourceSwapCleanState n
    active parked target flag

/-- Canonical physical embedding used by the bitwise MAC prefix proof. -/
def cleanState (n N : Nat) (multiplicand : PlainAdder.Word n)
    (accumulator : Nat) : Registers n :=
  workspaceState n multiplicand 0 (N : PlainAdder.Word n)
    (accumulator : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth n)) false

/-- Actual constant loaded at multiplier position `bit`. -/
def stageConstant (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    PlainAdder.Word n :=
  (Nat.FixedWidth.ModularAccumulate.stageConstantResidue N a.val bit.val : PlainAdder.Word n)

/-- Encoded label of the constant selected at one multiplier position. -/
def stageConstantLabel (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    Fin (2 ^ MAU.Addition.VBECircuit.AdderWidth n) :=
  PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv
    (MAU.Addition.VBECircuit.AdderWidth n)
    (MAU.Addition.VBECircuit.widenWord n (stageConstant n N a bit))

lemma stageConstantLabel_testBit (n N : Nat) (a : PlainAdder.Word n)
    (stageBit : Fin n)
    (wordBit : Fin (MAU.Addition.VBECircuit.AdderWidth n)) :
    (stageConstantLabel n N a stageBit).val.testBit wordBit.val =
      (MAU.Addition.VBECircuit.widenWord n
        (stageConstant n N a stageBit)).val.testBit wordBit.val := by
  unfold stageConstantLabel
  rw [← PlainAdder.Schedule.PowerOfTwo.wordBit_get]
  simp [PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit]

/-! ### One real single-controlled modular-add stage -/

/-- Concrete controlled-XOR program that loads one selected stage constant. -/
def stageLoadProgram (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  EncodedBit.Word.controlledXorConstantProgram
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)

/-- Label action of the controlled stage-constant load. -/
def stageLoadStep (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    Registers n → Registers n :=
  EncodedBit.Word.controlledXorConstantStep
    (multiplicandBit n bit) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)

lemma stageLoad_realizes (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    UnitaryCircuit.Realizes (encoding n) (stageLoadProgram n N a bit) environment
      (stageLoadStep n N a bit) :=
  EncodedBit.Word.controlledXorConstant_realizes
    (environment := environment)
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)

/-- Loading into a zero active source selects the fixed stage constant using
the actual multiplier wire, while preserving the complete multiplier and every
other VBE arithmetic field. -/
lemma stageLoadStep_cleanEndpoint (n N : Nat) (a x : PlainAdder.Word n)
    (bit : Fin n) (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n))
    (flag : Bool) :
    stageLoadStep n N a bit (workspaceState n x 0 parked target flag) =
      workspaceState n x
        (if x.val.testBit bit.val then stageConstant n N a bit else 0)
        parked target flag := by
  let input := workspaceState n x 0 parked target flag
  let loaded : PlainAdder.Word n :=
    if x.val.testBit bit.val then stageConstant n N a bit else 0
  have hactive :
      (stageLoadStep n N a bit input).arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord n loaded := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro sourceBit
    rw [← activeSourceBit_get n sourceBit
      (stageLoadStep n N a bit input)]
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_target
        (multiplicandBit n bit) (activeSourceWord n)
        (stageConstantLabel n N a bit)
        (multiplicand_activeSource_ne n bit) sourceBit
        (fun other hother =>
          activeSource_pairwise_ne n other sourceBit hother) input
    have hconstant := stageConstantLabel_testBit n N a bit sourceBit
    have hzeroBit :
        (MAU.Addition.VBECircuit.widenWord n
          (0 : PlainAdder.Word n)).val.testBit sourceBit.val = false := by
      rw [MAU.Addition.VBECircuit.widenWord_val]
      simp
    calc
      (activeSourceBit n sourceBit).get
          (stageLoadStep n N a bit input) =
          (activeSourceBit n sourceBit).get
            (workspaceState n x loaded parked target flag) := by
        cases hcontrol : x.val.testBit bit.val <;>
          cases hconstantBit :
            (MAU.Addition.VBECircuit.widenWord n
              (stageConstant n N a bit)).val.testBit sourceBit.val <;>
          simpa [stageLoadStep, activeSourceWord, input, workspaceState, loaded,
            MAU.Addition.VBECircuit.sourceSwapCleanState, hcontrol,
            hconstant, hconstantBit, hzeroBit] using hread
      _ = (MAU.Addition.VBECircuit.widenWord n loaded).val.testBit
          sourceBit.val :=
        activeSourceBit_get n sourceBit
          (workspaceState n x loaded parked target flag)
  have hmultiplicand :
      (stageLoadStep n N a bit input).multiplicand = x := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro observedBit
    rw [← multiplicandBit_get n observedBit]
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (multiplicandBit n bit) (activeSourceWord n)
        (stageConstantLabel n N a bit)
        (multiplicand_activeSource_ne n bit)
        (multiplicandBit n observedBit)
        (fun sourceBit =>
          Ne.symm (multiplicand_activeSource_ne n observedBit sourceBit)) input
    simpa [stageLoadStep, input, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have htarget :
      (stageLoadStep n N a bit input).arithmetic.target = target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro targetIndex
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (multiplicandBit n bit) (activeSourceWord n)
        (stageConstantLabel n N a bit)
        (multiplicand_activeSource_ne n bit)
        (liftArithmeticBit n
          (MAU.Addition.VBECircuit.targetBit n targetIndex))
        (activeSource_liftArithmetic_ne n
          (MAU.Addition.VBECircuit.targetBit n targetIndex)
          (fun sourceBit =>
            MAU.Addition.VBECircuit.activeSource_target_ne n sourceBit
              targetIndex)) input
    simpa [stageLoadStep, input, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hcarry :
      (stageLoadStep n N a bit input).arithmetic.carry = false := by
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (multiplicandBit n bit) (activeSourceWord n)
        (stageConstantLabel n N a bit)
        (multiplicand_activeSource_ne n bit)
        (liftArithmeticBit n (MAU.Addition.VBECircuit.carryBit n))
        (activeSource_liftArithmetic_ne n
          (MAU.Addition.VBECircuit.carryBit n)
          (MAU.Addition.VBECircuit.activeSource_carry_ne n)) input
    simpa [stageLoadStep, input, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hparked :
      (stageLoadStep n N a bit input).arithmetic.parkedSource = parked := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro parkedBit
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (multiplicandBit n bit) (activeSourceWord n)
        (stageConstantLabel n N a bit)
        (multiplicand_activeSource_ne n bit)
        (liftArithmeticBit n
          (MAU.Addition.VBECircuit.parkedSourceBit n parkedBit))
        (activeSource_liftArithmetic_ne n
          (MAU.Addition.VBECircuit.parkedSourceBit n parkedBit)
          (fun sourceBit =>
            MAU.Addition.VBECircuit.activeSource_parked_ne n sourceBit
              parkedBit)) input
    simpa [stageLoadStep, input, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hwork :
      (stageLoadStep n N a bit input).arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth n) := by
    change (stageLoadStep n N a bit input).arithmetic.carryWork = 0
    apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    rw [← MAU.Addition.VBECircuit.carryWorkBit_get n workBit
      (stageLoadStep n N a bit input).arithmetic]
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (multiplicandBit n bit) (activeSourceWord n)
        (stageConstantLabel n N a bit)
        (multiplicand_activeSource_ne n bit)
        (liftArithmeticBit n
          (MAU.Addition.VBECircuit.carryWorkBit n workBit))
        (activeSource_liftArithmetic_ne n
          (MAU.Addition.VBECircuit.carryWorkBit n workBit)
          (fun sourceBit =>
            MAU.Addition.VBECircuit.activeSource_carryWork_ne n sourceBit
              workBit)) input
    have hread' :
        (MAU.Addition.VBECircuit.carryWorkBit n workBit).get
            (stageLoadStep n N a bit input).arithmetic =
          (MAU.Addition.VBECircuit.carryWorkBit n workBit).get
            input.arithmetic := by
      simpa [stageLoadStep] using hread
    rw [hread', MAU.Addition.VBECircuit.carryWorkBit_get]
    simp [input, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState,
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]
  have hflag :
      (stageLoadStep n N a bit input).arithmetic.reductionFlag = flag := by
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (multiplicandBit n bit) (activeSourceWord n)
        (stageConstantLabel n N a bit)
        (multiplicand_activeSource_ne n bit)
        (liftArithmeticBit n
          (MAU.Addition.VBECircuit.reductionFlagBit n))
        (activeSource_liftArithmetic_ne n
          (MAU.Addition.VBECircuit.reductionFlagBit n)
          (fun sourceBit => Ne.symm
            (MAU.Addition.VBECircuit.reductionFlag_activeSource_ne n
              sourceBit))) input
    simpa [stageLoadStep, input, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  change stageLoadStep n N a bit input = _
  have harithmetic :
      (stageLoadStep n N a bit input).arithmetic =
        MAU.Addition.VBECircuit.sourceSwapCleanState n loaded parked target
          flag := by
    apply (MAU.Addition.VBECircuit.registersEquiv n).injective
    change
      (((({ left :=
              (stageLoadStep n N a bit input).arithmetic.activeSource,
            right := (stageLoadStep n N a bit input).arithmetic.target,
            carry := (stageLoadStep n N a bit input).arithmetic.carry } :
          PlainAdder.Data (MAU.Addition.VBECircuit.AdderWidth n)),
          (stageLoadStep n N a bit input).arithmetic.parkedSource),
        (stageLoadStep n N a bit input).arithmetic.carryWork),
        (stageLoadStep n N a bit input).arithmetic.reductionFlag) =
      (((({ left := MAU.Addition.VBECircuit.widenWord n loaded,
            right := target,
            carry := false } :
          PlainAdder.Data (MAU.Addition.VBECircuit.AdderWidth n)), parked),
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth n)), flag)
    rw [hactive, htarget, hcarry, hparked, hwork, hflag]
  apply (registersEquiv n).injective
  change
    ((stageLoadStep n N a bit input).multiplicand,
      (stageLoadStep n N a bit input).arithmetic) =
    (x, MAU.Addition.VBECircuit.sourceSwapCleanState n loaded parked target
      flag)
  rw [hmultiplicand, harithmetic]

/-! ### Constant-schedule stage load -/

/-- Exact fixed-schedule gates used to load one selected stage constant. -/
def uniformStageLoadGates (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) : List (EncodedBit.GateSpec (encoding n)) :=
  EncodedBit.Word.constantScheduleGates
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

/-- Fixed-schedule load: every classical source bit emits exactly three CNOTs.
The clean VBE reduction flag is used only as a known-false null control, so the
physical width is unchanged. -/
def uniformStageLoadProgram (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  EncodedBit.Word.constantScheduleProgram
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

/-- Folded action of the fixed-schedule load. -/
def uniformStageLoadStep (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) : Registers n → Registers n :=
  EncodedBit.Word.constantScheduleStep
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

lemma uniformStageLoad_realizes (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) :
    UnitaryCircuit.Realizes (encoding n) (uniformStageLoadProgram n N a bit) environment
      (uniformStageLoadStep n N a bit) :=
  EncodedBit.Word.constantSchedule_realizes
    (environment := environment)
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

/-- On the clean VBE subspace, the fixed schedule has the same constant-load
semantics as the optimized compiler. -/
lemma uniformStageLoadStep_cleanEndpoint
    (n N : Nat) (a x : PlainAdder.Word n) (bit : Fin n)
    (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) :
    uniformStageLoadStep n N a bit
        (workspaceState n x 0 parked target false) =
      workspaceState n x
        (if x.val.testBit bit.val then stageConstant n N a bit else 0)
        parked target false := by
  let input := workspaceState n x 0 parked target false
  have hzero : (reductionFlagBit n).get input = false := by
    rfl
  have hschedule :=
    EncodedBit.Word.constantScheduleStep_eq_controlledXorConstantStep_of_zeroControl_false
      (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
      (stageConstantLabel n N a bit)
      (multiplicand_activeSource_ne n bit)
      (reductionFlag_activeSource_ne n) input hzero
  change uniformStageLoadStep n N a bit input = _
  rw [uniformStageLoadStep, hschedule]
  simpa [input, stageLoadStep] using
    stageLoadStep_cleanEndpoint n N a x bit parked target false

/-- Lifted modular-add action that preserves the complete multiplier word. -/
def liftedModularAddStep (n N : Nat) : Registers n → Registers n :=
  fun x => {
    x with
    arithmetic := MAU.Addition.VBECircuit.modularAddStep n N x.arithmetic }

/-- The complete modular-add primitive schedule lifted past the multiplier
word, retaining every source GateSpec. -/
def liftedModularAddGates (n N : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (MAU.Addition.VBECircuit.modularAddGates n N).map
    (liftArithmeticGate n)

/-- The lifted gate list agrees pointwise with the established modular-add
action on the arithmetic workspace. -/
lemma liftedModularAddStep_eq_gateList (n N : Nat) (x : Registers n) :
    EncodedBit.GateSpec.stepList (liftedModularAddGates n N) x =
      liftedModularAddStep n N x := by
  rw [liftedModularAddGates, stepList_liftArithmeticGates]
  rw [MAU.Addition.VBECircuit.modularAddStep_eq_gateList]
  rfl

/-- Actual modular-add circuit lifted past the complete multiplier word. -/
def liftedModularAddProgram (n N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (liftedModularAddGates n N)

/-- Direct realization of modular addition in the full MAC layout. -/
lemma liftedModularAdd_realizes (n N : Nat) :
    UnitaryCircuit.Realizes (encoding n) (liftedModularAddProgram n N) environment
      (liftedModularAddStep n N) := by
  exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty (liftedModularAddGates n N)
    (liftedModularAddStep_eq_gateList n N)

/-! ### Constant-schedule stage unload -/

/-- Exact reverse gate list used to unload one selected stage constant. -/
def uniformStageUnloadGates (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) : List (EncodedBit.GateSpec (encoding n)) :=
  (uniformStageLoadGates n N a bit).reverse

/-- Exact reverse of the fixed-schedule load gate list. -/
def uniformStageUnloadProgram (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  EncodedBit.Word.constantScheduleUnloadProgram
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

/-- Folded action of the reverse fixed-schedule gate list. -/
def uniformStageUnloadStep (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) : Registers n → Registers n :=
  EncodedBit.Word.constantScheduleUnloadStep
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

lemma uniformStageUnload_realizes (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) :
    UnitaryCircuit.Realizes (encoding n) (uniformStageUnloadProgram n N a bit) environment
      (uniformStageUnloadStep n N a bit) :=
  EncodedBit.Word.constantScheduleUnload_realizes
    (environment := environment)
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

/-- The reverse fixed schedule clears the clean loaded source exactly. -/
lemma uniformStageUnloadStep_cleanEndpoint
    (n N : Nat) (a x : PlainAdder.Word n) (bit : Fin n)
    (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) :
    uniformStageUnloadStep n N a bit
        (workspaceState n x
          (if x.val.testBit bit.val then stageConstant n N a bit else 0)
          parked target false) =
      workspaceState n x 0 parked target false := by
  let input := workspaceState n x 0 parked target false
  have hload :=
    uniformStageLoadStep_cleanEndpoint n N a x bit parked target
  have hinverse := EncodedBit.Word.stepList_reverse_constantScheduleGates
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n) input
  change uniformStageUnloadStep n N a bit
      (uniformStageLoadStep n N a bit input) = input at hinverse
  rw [hload] at hinverse
  simpa [input] using hinverse

/-- Reverse controlled-XOR program that clears the selected stage constant. -/
def stageUnloadProgram (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  EncodedBit.Word.controlledXorConstantUnloadProgram
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)

/-- Label action of the reverse stage-constant unload. -/
def stageUnloadStep (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    Registers n → Registers n :=
  EncodedBit.Word.controlledXorConstantUnloadStep
    (multiplicandBit n bit) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)

lemma stageUnload_realizes
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    UnitaryCircuit.Realizes (encoding n) (stageUnloadProgram n N a bit) environment
      (stageUnloadStep n N a bit) :=
  EncodedBit.Word.controlledXorConstantUnload_realizes
    (environment := environment)
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)

/-- The reverse-list unload removes exactly the active source created by the
matching single-controlled load. -/
lemma stageUnloadStep_cleanEndpoint (n N : Nat) (a x : PlainAdder.Word n)
    (bit : Fin n) (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n))
    (flag : Bool) :
    stageUnloadStep n N a bit
        (workspaceState n x
          (if x.val.testBit bit.val then stageConstant n N a bit else 0)
          parked target flag) =
      workspaceState n x 0 parked target flag := by
  let input := workspaceState n x 0 parked target flag
  have hload := stageLoadStep_cleanEndpoint n N a x bit parked target flag
  have hinverse :=
    EncodedBit.Word.controlledXorConstantUnloadStep_after_controlledXorConstantStep
      (multiplicandBit n bit) (activeSourceWord n)
      (stageConstantLabel n N a bit)
      (multiplicand_activeSource_ne n bit) input
  change stageUnloadStep n N a bit (stageLoadStep n N a bit input) = input at hinverse
  rw [hload] at hinverse
  simpa [input] using hinverse

/-- Complete load/add/unload primitive list for one multiplier bit. -/
def stageGates (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    List (EncodedBit.GateSpec (encoding n)) :=
  uniformStageLoadGates n N a bit ++
    liftedModularAddGates n N ++
    uniformStageUnloadGates n N a bit

/-- Ordered load, modular-add, and unload programs for one multiplier bit. -/
def stagePrograms (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    List (UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum) :=
  [ uniformStageLoadProgram n N a bit,
    liftedModularAddProgram n N,
    uniformStageUnloadProgram n N a bit ]

/-- Ordered semantic actions corresponding to `stagePrograms`. -/
def stageSteps (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    List (Registers n → Registers n) :=
  [ uniformStageLoadStep n N a bit,
    liftedModularAddStep n N,
    uniformStageUnloadStep n N a bit ]

lemma stageStages_realize
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    List.Forall₂
      (fun program step => UnitaryCircuit.Realizes (encoding n) program environment step)
      (stagePrograms n N a bit) (stageSteps n N a bit) := by
  unfold stagePrograms stageSteps
  exact .cons (uniformStageLoad_realizes n N a bit) <|
    .cons (liftedModularAdd_realizes n N) <|
    .cons (uniformStageUnload_realizes n N a bit) .nil

/-- Composite label action of one load/add/unload stage. -/
def stageStep (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    Registers n → Registers n :=
  UnitaryCircuit.Realizes.stepList (stageSteps n N a bit)

/-- The flattened stage gates agree pointwise with the established three-part
stage action. -/
lemma stageStep_eq_gateList (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) (x : Registers n) :
    EncodedBit.GateSpec.stepList (stageGates n N a bit) x =
      stageStep n N a bit x := by
  simp only [stageGates, EncodedBit.GateSpec.stepList_append]
  rw [liftedModularAddStep_eq_gateList]
  rfl

/-- Concrete concatenated program for one multiplier-bit stage. -/
def stageProgram (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  (stagePrograms n N a bit).foldr UnitaryCircuit.seq
    (UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum)



















/-- The strict event schedule of one uniform stage is independent of its
compiled classical multiplicand. -/
lemma stageGates_events_eq (n N : Nat)
    (left right : PlainAdder.Word n) (bit : Fin n) :
    (stageGates n N left bit).map (EncodedBit.GateSpec.event .empty) =
      (stageGates n N right bit).map (EncodedBit.GateSpec.event .empty) := by
  have hload := EncodedBit.Word.constantScheduleGates_events_eq
    .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N left bit) (stageConstantLabel n N right bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)
  simpa [stageGates, uniformStageLoadGates, uniformStageUnloadGates,
    List.map_append, List.map_reverse] using congrArg
      (fun loadEvents =>
        loadEvents ++
          (liftedModularAddGates n N).map (EncodedBit.GateSpec.event .empty) ++
          loadEvents.reverse)
      hload





/-- The fixed-schedule load has the same strict event pool for every
multiplier constant. -/
lemma uniformStageLoadProgram_eventCost_eq (n N : Nat)
    (left right : PlainAdder.Word n) (bit : Fin n) :
    (uniformStageLoadProgram n N left bit).eventCost =
      (uniformStageLoadProgram n N right bit).eventCost := by
  exact EncodedBit.Word.constantScheduleProgram_eventCost_eq
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N left bit) (stageConstantLabel n N right bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

/-- The fixed-schedule load has the same strict event critical path for every
multiplier constant. -/
lemma uniformStageLoadProgram_eventDepth_eq (n N : Nat)
    (left right : PlainAdder.Word n) (bit : Fin n) :
    (uniformStageLoadProgram n N left bit).eventDepth =
      (uniformStageLoadProgram n N right bit).eventDepth := by
  exact EncodedBit.Word.constantScheduleProgram_eventDepth_eq
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N left bit) (stageConstantLabel n N right bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)





/-- The reverse fixed schedule has the same strict event pool for every
multiplier constant. -/
lemma uniformStageUnloadProgram_eventCost_eq (n N : Nat)
    (left right : PlainAdder.Word n) (bit : Fin n) :
    (uniformStageUnloadProgram n N left bit).eventCost =
      (uniformStageUnloadProgram n N right bit).eventCost := by
  exact EncodedBit.Word.constantScheduleUnloadProgram_eventCost_eq
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N left bit) (stageConstantLabel n N right bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

/-- The reverse fixed schedule has the same strict event critical path for
every multiplier constant. -/
lemma uniformStageUnloadProgram_eventDepth_eq (n N : Nat)
    (left right : PlainAdder.Word n) (bit : Fin n) :
    (uniformStageUnloadProgram n N left bit).eventDepth =
      (uniformStageUnloadProgram n N right bit).eventDepth := by
  exact EncodedBit.Word.constantScheduleUnloadProgram_eventDepth_eq
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N left bit) (stageConstantLabel n N right bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)





/-- One complete load/add/unload stage has a strict event pool independent of
its compiled multiplier constant. -/
lemma stageProgram_eventCost_eq (n N : Nat)
    (left right : PlainAdder.Word n) (bit : Fin n) :
    (stageProgram n N left bit).eventCost =
      (stageProgram n N right bit).eventCost := by
  change
    (uniformStageLoadProgram n N left bit).eventCost +
        ((liftedModularAddProgram n N).eventCost +
          ((uniformStageUnloadProgram n N left bit).eventCost + 0)) =
      (uniformStageLoadProgram n N right bit).eventCost +
        ((liftedModularAddProgram n N).eventCost +
          ((uniformStageUnloadProgram n N right bit).eventCost + 0))
  rw [uniformStageLoadProgram_eventCost_eq n N left right bit,
    uniformStageUnloadProgram_eventCost_eq n N left right bit]

/-- One complete load/add/unload stage has a strict event critical path
independent of its compiled multiplier constant. -/
lemma stageProgram_eventDepth_eq (n N : Nat)
    (left right : PlainAdder.Word n) (bit : Fin n) :
    (stageProgram n N left bit).eventDepth =
      (stageProgram n N right bit).eventDepth := by
  change
    DepthExpr.seq (uniformStageLoadProgram n N left bit).eventDepth
        (DepthExpr.seq (liftedModularAddProgram n N).eventDepth
          (DepthExpr.seq
            (uniformStageUnloadProgram n N left bit).eventDepth .id)) =
      DepthExpr.seq (uniformStageLoadProgram n N right bit).eventDepth
        (DepthExpr.seq (liftedModularAddProgram n N).eventDepth
          (DepthExpr.seq
            (uniformStageUnloadProgram n N right bit).eventDepth .id))
  rw [uniformStageLoadProgram_eventDepth_eq n N left right bit,
    uniformStageUnloadProgram_eventDepth_eq n N left right bit]

lemma stage_realizes (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    UnitaryCircuit.Realizes (encoding n) (stageProgram n N a bit) environment
      (stageStep n N a bit) :=
  UnitaryCircuit.Realizes.appendList (environment := environment) (encoding n)
    (QubitLayout.canonical _)
    (stagePrograms n N a bit)
    (stageSteps n N a bit) (stageStages_realize n N a bit)

/-- One exact load/add/unload stage conditionally contributes the fixed
`a * 2^bit` residue and restores every work register. -/
lemma stageStep_cleanEndpoint (n N : Nat) (a x : PlainAdder.Word n)
    (bit : Fin n) (accumulator : Nat)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (haccumulator : accumulator < N) :
    stageStep n N a bit (cleanState n N x accumulator) =
      cleanState n N x
        ((accumulator +
          Nat.FixedWidth.ModularAccumulate.selectedBitContribution N a.val x.val bit.val) % N) := by
  let selected : PlainAdder.Word n :=
    if x.val.testBit bit.val then stageConstant n N a bit else 0
  let accumulatorWord : PlainAdder.Word n :=
    (accumulator : PlainAdder.Word n)
  let result :=
    (accumulator +
      Nat.FixedWidth.ModularAccumulate.selectedBitContribution N a.val x.val bit.val) % N
  have haccumulatorPow : accumulator < 2 ^ n :=
    lt_trans haccumulator hN
  have haccumulatorWordVal : accumulatorWord.val = accumulator := by
    exact ZMod.val_natCast_of_lt haccumulatorPow
  have hstageConstantVal :
      (stageConstant n N a bit).val =
        Nat.FixedWidth.ModularAccumulate.stageConstantResidue N a.val bit.val := by
    unfold stageConstant
    apply ZMod.val_natCast_of_lt
    exact lt_trans (Nat.FixedWidth.ModularAccumulate.stageConstantResidue_lt hNpos) hN
  have hselectedVal :
      selected.val =
        Nat.FixedWidth.ModularAccumulate.selectedBitContribution N a.val x.val bit.val := by
    cases hbit : x.val.testBit bit.val <;>
      simp [selected, Nat.FixedWidth.ModularAccumulate.selectedBitContribution_eq_if, hbit,
        hstageConstantVal]
  have hselectedLt : selected.val < N := by
    rw [hselectedVal]
    exact Nat.FixedWidth.ModularAccumulate.selectedBitContribution_lt hNpos
  have htarget :
      MAU.Addition.VBECircuit.widenWord n accumulatorWord =
        (accumulator : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) := by
    simpa [accumulatorWord] using
      widenWord_natCast_of_lt n accumulator haccumulatorPow
  have hmod := MAU.Addition.VBECircuit.modularAddStep_cleanEndpoint
    n N selected accumulatorWord hNpos hN hselectedLt
      (by simpa [haccumulatorWordVal] using haccumulator)
  let s0 := cleanState n N x accumulator
  let s1 := workspaceState n x selected (N : PlainAdder.Word n)
    (accumulator : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth n)) false
  let s2 := workspaceState n x selected (N : PlainAdder.Word n)
    ((selected.val + accumulatorWord.val) % N :
      PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) false
  let s3 := cleanState n N x result
  have hs1 : uniformStageLoadStep n N a bit s0 = s1 := by
    simpa [s0, s1, cleanState, selected] using
      uniformStageLoadStep_cleanEndpoint n N a x bit
        (N : PlainAdder.Word n)
        (accumulator : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n))
  have hs2 : liftedModularAddStep n N s1 = s2 := by
    apply (registersEquiv n).injective
    change
      (x, MAU.Addition.VBECircuit.modularAddStep n N
        (MAU.Addition.VBECircuit.sourceSwapCleanState n selected
          (N : PlainAdder.Word n)
          (accumulator : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) false)) =
      (x, MAU.Addition.VBECircuit.sourceSwapCleanState n selected
        (N : PlainAdder.Word n)
        ((selected.val + accumulatorWord.val) % N :
          PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) false)
    simpa [htarget] using congrArg (fun arithmetic => (x, arithmetic)) hmod
  have hresult :
      (selected.val + accumulatorWord.val) % N = result := by
    simp [result, hselectedVal, haccumulatorWordVal, Nat.add_comm]
  have hs3 : uniformStageUnloadStep n N a bit s2 = s3 := by
    simpa [s2, s3, cleanState, selected, hresult] using
      uniformStageUnloadStep_cleanEndpoint n N a x bit
        (N : PlainAdder.Word n)
        ((selected.val + accumulatorWord.val) % N :
          PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n))
  change stageStep n N a bit s0 = _
  have hstages : stageStep n N a bit s0 = s3 := by
    simp only [stageStep, stageSteps, UnitaryCircuit.Realizes.stepList,
      hs1, hs2, hs3, id_eq]
  rw [hstages]

/-! ### Uniform full-multiplier fold -/

/-- One actual three-part program for each multiplier wire, in increasing
little-endian bit-index order. -/
def macPrograms (n N : Nat) (a : PlainAdder.Word n) :
    List (UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum) :=
  List.ofFn fun bit : Fin n => stageProgram n N a bit

/-- Semantic schedule aligned entry-for-entry with `macPrograms`. -/
def macSteps (n N : Nat) (a : PlainAdder.Word n) :
    List (Registers n → Registers n) :=
  List.ofFn fun bit : Fin n => stageStep n N a bit

/-- Complete multiply-accumulate primitive list, flattened in increasing
multiplier-bit order. -/
def macGates (n N : Nat) (a : PlainAdder.Word n) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (List.ofFn fun bit : Fin n => bit).flatMap
    (stageGates n N a)

/-! ### Strict-event size bounds -/

/-- One flattened load/add/unload stage has a linear gate-list bound. -/
lemma stageGates_length_le (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) :
    (stageGates n N a bit).length ≤ 54 * n + 51 := by
  have hload : (uniformStageLoadGates n N a bit).length =
      3 * (n + 1) := by
    exact EncodedBit.Word.constantScheduleGates_length
      (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
      (stageConstantLabel n N a bit)
      (multiplicand_activeSource_ne n bit)
      (reductionFlag_activeSource_ne n)
  have hadd : (liftedModularAddGates n N).length ≤ 48 * n + 45 := by
    simp only [liftedModularAddGates, List.length_map]
    exact MAU.Addition.VBECircuit.modularAddGates_length_le n N
  have hunload : (uniformStageUnloadGates n N a bit).length =
      3 * (n + 1) := by
    simp [uniformStageUnloadGates, hload]
  simp only [stageGates, List.length_append]
  omega

private lemma primitiveMultiplicity_sums_eq_length
    {Data : Type} {dataEncoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec dataEncoding)) :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum +
        (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum +
        (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      gates.length := by
  have h := EncodedBit.GateSpec.primitiveEventCount_programList
    (QubitLayout.canonical dataEncoding.width) .empty gates
  unfold EncodedBit.GateSpec.primitiveEventCount at h
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum] at h
  exact h

private lemma uniformStageLoadGates_cnotMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    ((uniformStageLoadGates n N a bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * (n + 1) := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact EncodedBit.Word.constantScheduleProgram_cnot_eventCount
    (QubitLayout.canonical _) .empty
    (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
    (stageConstantLabel n N a bit)
    (multiplicand_activeSource_ne n bit)
    (reductionFlag_activeSource_ne n)

private lemma uniformStageLoadGates_toffoliMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    ((uniformStageLoadGates n N a bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  have htotal := primitiveMultiplicity_sums_eq_length
    (uniformStageLoadGates n N a bit)
  have hc := uniformStageLoadGates_cnotMultiplicity_sum n N a bit
  have hlen : (uniformStageLoadGates n N a bit).length = 3 * (n + 1) :=
    EncodedBit.Word.constantScheduleGates_length
      (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
      (stageConstantLabel n N a bit)
      (multiplicand_activeSource_ne n bit)
      (reductionFlag_activeSource_ne n)
  omega

private lemma uniformStageLoadGates_xMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    ((uniformStageLoadGates n N a bit).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  have htotal := primitiveMultiplicity_sums_eq_length
    (uniformStageLoadGates n N a bit)
  have hc := uniformStageLoadGates_cnotMultiplicity_sum n N a bit
  have hlen : (uniformStageLoadGates n N a bit).length = 3 * (n + 1) :=
    EncodedBit.Word.constantScheduleGates_length
      (multiplicandBit n bit) (reductionFlagBit n) (activeSourceWord n)
      (stageConstantLabel n N a bit)
      (multiplicand_activeSource_ne n bit)
      (reductionFlag_activeSource_ne n)
  omega

private lemma liftedModularAddGates_events_eq_source (n N : Nat) :
    (liftedModularAddGates n N).map (EncodedBit.GateSpec.event .empty) =
      (MAU.Addition.VBECircuit.modularAddGates n N).map
        (EncodedBit.GateSpec.event .empty) := by
  simp [liftedModularAddGates, List.map_map]

private lemma liftedModularAddGates_toffoliMultiplicity_sum
    (n N : Nat) :
    ((liftedModularAddGates n N).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 30 * n := by
  rw [EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (liftedModularAddGates_events_eq_source n N)]
  exact MAU.Addition.VBECircuit.modularAddGates_toffoliMultiplicity_sum n N

private lemma liftedModularAddGates_cnotMultiplicity_sum_le
    (n N : Nat) :
    ((liftedModularAddGates n N).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤ 18 * n + 14 := by
  rw [EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (liftedModularAddGates_events_eq_source n N)]
  exact MAU.Addition.VBECircuit.modularAddGates_cnotMultiplicity_sum_le n N

private lemma liftedModularAddGates_xMultiplicity_sum (n N : Nat) :
    ((liftedModularAddGates n N).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 := by
  rw [EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    (liftedModularAddGates_events_eq_source n N)]
  exact MAU.Addition.VBECircuit.modularAddGates_xMultiplicity_sum n N

lemma stageGates_toffoliMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    ((stageGates n N a bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 30 * n := by
  simp [stageGates, uniformStageUnloadGates,
    uniformStageLoadGates_toffoliMultiplicity_sum,
    liftedModularAddGates_toffoliMultiplicity_sum]

lemma stageGates_cnotMultiplicity_sum_le
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    ((stageGates n N a bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤ 24 * n + 20 := by
  have hload := uniformStageLoadGates_cnotMultiplicity_sum n N a bit
  have hadd := liftedModularAddGates_cnotMultiplicity_sum_le n N
  simp only [stageGates, uniformStageUnloadGates, List.map_append,
    List.sum_append, List.map_reverse, List.sum_reverse]
  omega

lemma stageGates_xMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    ((stageGates n N a bit).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 := by
  simp [stageGates, uniformStageUnloadGates,
    uniformStageLoadGates_xMultiplicity_sum,
    liftedModularAddGates_xMultiplicity_sum]

private lemma flatMap_stageGates_toffoliMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) :
    ∀ bits : List (Fin n),
      (((bits.flatMap (stageGates n N a)).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum) =
        bits.length * (30 * n)
  | [] => by simp
  | bit :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons]
      rw [stageGates_toffoliMultiplicity_sum,
        flatMap_stageGates_toffoliMultiplicity_sum n N a rest]
      ring

private lemma flatMap_stageGates_cnotMultiplicity_sum_le
    (n N : Nat) (a : PlainAdder.Word n) :
    ∀ bits : List (Fin n),
      (((bits.flatMap (stageGates n N a)).map
          EncodedBit.GateSpec.cnotMultiplicity).sum) ≤
        bits.length * (24 * n + 20)
  | [] => by simp
  | bit :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons]
      have hstage := stageGates_cnotMultiplicity_sum_le n N a bit
      have hrest := flatMap_stageGates_cnotMultiplicity_sum_le n N a rest
      calc
        ((stageGates n N a bit).map
              EncodedBit.GateSpec.cnotMultiplicity).sum +
            ((rest.flatMap (stageGates n N a)).map
              EncodedBit.GateSpec.cnotMultiplicity).sum ≤
            (24 * n + 20) + rest.length * (24 * n + 20) :=
          Nat.add_le_add hstage hrest
        _ = rest.length.succ * (24 * n + 20) := by
          let stageBound := 24 * n + 20
          change stageBound + rest.length * stageBound =
            rest.length.succ * stageBound
          rw [Nat.succ_mul]
          exact Nat.add_comm _ _

private lemma flatMap_stageGates_xMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) :
    ∀ bits : List (Fin n),
      (((bits.flatMap (stageGates n N a)).map
          EncodedBit.GateSpec.xMultiplicity).sum) = bits.length
  | [] => by simp
  | bit :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons]
      rw [stageGates_xMultiplicity_sum,
        flatMap_stageGates_xMultiplicity_sum n N a rest]
      omega

lemma macGates_toffoliMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) :
    ((macGates n N a).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 30 * n ^ 2 := by
  have h := flatMap_stageGates_toffoliMultiplicity_sum n N a
    (List.ofFn fun bit : Fin n => bit)
  simp only [List.length_ofFn] at h
  rw [show n * (30 * n) = 30 * n ^ 2 by ring] at h
  simpa [macGates] using h

lemma macGates_cnotMultiplicity_sum_le
    (n N : Nat) (a : PlainAdder.Word n) :
    ((macGates n N a).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤ 24 * n ^ 2 + 20 * n := by
  have h := flatMap_stageGates_cnotMultiplicity_sum_le n N a
    (List.ofFn fun bit : Fin n => bit)
  simp only [macGates, List.length_ofFn] at h ⊢
  nlinarith

lemma macGates_xMultiplicity_sum
    (n N : Nat) (a : PlainAdder.Word n) :
    ((macGates n N a).map EncodedBit.GateSpec.xMultiplicity).sum = n := by
  simpa [macGates] using flatMap_stageGates_xMultiplicity_sum n N a
    (List.ofFn fun bit : Fin n => bit)

private lemma flatMap_stageGates_length_le (n N : Nat)
    (a : PlainAdder.Word n) :
    ∀ bits : List (Fin n),
      (bits.flatMap (stageGates n N a)).length ≤
        bits.length * (54 * n + 51)
  | [] => by simp
  | bit :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hstage := stageGates_length_le n N a bit
      have hrest := flatMap_stageGates_length_le n N a rest
      calc
        (stageGates n N a bit).length +
              (rest.flatMap (stageGates n N a)).length ≤
            (54 * n + 51) + rest.length * (54 * n + 51) :=
          Nat.add_le_add hstage hrest
        _ = rest.length.succ * (54 * n + 51) := by
          rw [Nat.succ_mul rest.length (54 * n + 51)]
          ac_rfl

/-- The flattened full-MAC gate list has the corresponding quadratic bound. -/
lemma macGates_length_le (n N : Nat) (a : PlainAdder.Word n) :
    (macGates n N a).length ≤ 54 * n ^ 2 + 51 * n := by
  have h := flatMap_stageGates_length_le n N a
    (List.ofFn fun bit : Fin n => bit)
  simp only [macGates, List.length_ofFn] at h ⊢
  calc
    ((List.ofFn fun bit : Fin n => bit).flatMap
        (stageGates n N a)).length ≤ n * (54 * n + 51) := h
    _ = 54 * n ^ 2 + 51 * n := by ring





private lemma map_event_flatMap_stageGates_eq (n N : Nat)
    (left right : PlainAdder.Word n) :
    ∀ bits : List (Fin n),
      (bits.flatMap (stageGates n N left)).map (EncodedBit.GateSpec.event .empty) =
        (bits.flatMap (stageGates n N right)).map (EncodedBit.GateSpec.event .empty)
  | [] => rfl
  | bit :: rest => by
      simp only [List.flatMap_cons, List.map_append]
      rw [stageGates_events_eq n N left right bit,
        map_event_flatMap_stageGates_eq n N left right rest]

/-- The complete MAC strict event schedule is independent of the compiled
classical multiplicand. -/
lemma macGates_events_eq (n N : Nat)
    (left right : PlainAdder.Word n) :
    (macGates n N left).map (EncodedBit.GateSpec.event .empty) =
      (macGates n N right).map (EncodedBit.GateSpec.event .empty) := by
  exact map_event_flatMap_stageGates_eq n N left right
    (List.ofFn fun bit : Fin n => bit)

@[simp] lemma macPrograms_length (n N : Nat) (a : PlainAdder.Word n) :
    (macPrograms n N a).length = n := by
  simp [macPrograms]

@[simp] lemma macSteps_length (n N : Nat) (a : PlainAdder.Word n) :
    (macSteps n N a).length = n := by
  simp [macSteps]

lemma macSteps_get (n N : Nat) (a : PlainAdder.Word n) (bit : Fin n) :
    (macSteps n N a).get
        ⟨bit.val, by simp [macSteps]⟩ =
      stageStep n N a bit := by
  change
    (List.ofFn (fun bit : Fin n => stageStep n N a bit)).get
        ⟨bit.val, by simp⟩ =
      stageStep n N a bit
  rw [List.get_ofFn]
  congr 1

lemma macStages_realize (n N : Nat) (a : PlainAdder.Word n) :
    List.Forall₂
      (fun program step => UnitaryCircuit.Realizes (encoding n) program environment step)
      (macPrograms n N a) (macSteps n N a) := by
  apply List.forall₂_of_length_eq_of_get
  · rw [macPrograms_length, macSteps_length]
  · intro i hprogram hstep
    let bit : Fin n := ⟨i, by
      rw [macSteps_length] at hstep
      exact hstep⟩
    change
      UnitaryCircuit.Realizes (encoding n)
        ((List.ofFn
          (fun bit : Fin n => stageProgram n N a bit)).get ⟨i, hprogram⟩) environment
        ((List.ofFn
          (fun bit : Fin n => stageStep n N a bit)).get ⟨i, hstep⟩)
    rw [List.get_ofFn, List.get_ofFn]
    exact stage_realizes n N a bit

/-- The input-independent concrete program for all multiplier bits. -/
def macProgram (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  (macPrograms n N a).foldr UnitaryCircuit.seq
    (UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum)











/-- Pairwise strict-event-pool equality is preserved by sequential list
folding. -/
lemma appendList_eventCost_eq_of_forall₂ {width : Nat}
    {left right : List (UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      (width)).toQuantum)}
    (h : List.Forall₂
      (fun first second => first.eventCost = second.eventCost)
      left right) :
    (left.foldr UnitaryCircuit.seq
      (UnitaryCircuit.identity AlgorithmGate.model .empty
        (QubitLayout.canonical width).toQuantum)).eventCost =
      (right.foldr UnitaryCircuit.seq
        (UnitaryCircuit.identity AlgorithmGate.model .empty
          (QubitLayout.canonical width).toQuantum)).eventCost := by
  induction h with
  | nil => rfl
  | cons hhead _htail ih =>
      simp only [UnitaryCircuit.eventCost] at hhead ih
      change _ + _ = _ + _
      rw [hhead, ih]

/-- Pairwise strict-event-depth equality is preserved by sequential list
folding. -/
lemma appendList_eventDepth_eq_of_forall₂ {width : Nat}
    {left right : List (UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      (width)).toQuantum)}
    (h : List.Forall₂
      (fun first second => first.eventDepth = second.eventDepth)
      left right) :
    (left.foldr UnitaryCircuit.seq
      (UnitaryCircuit.identity AlgorithmGate.model .empty
        (QubitLayout.canonical width).toQuantum)).eventDepth =
      (right.foldr UnitaryCircuit.seq
        (UnitaryCircuit.identity AlgorithmGate.model .empty
          (QubitLayout.canonical width).toQuantum)).eventDepth := by
  induction h with
  | nil => rfl
  | cons hhead _htail ih =>
      simp only [UnitaryCircuit.eventDepth] at hhead ih
      change DepthExpr.seq _ _ = DepthExpr.seq _ _
      rw [hhead, ih]





/-- The actual MAC program has a strict event pool independent of its
compiled constant. -/
lemma macProgram_eventCost_eq (n N : Nat)
    (left right : PlainAdder.Word n) :
    (macProgram n N left).eventCost =
      (macProgram n N right).eventCost := by
  apply appendList_eventCost_eq_of_forall₂
  apply List.forall₂_of_length_eq_of_get
  · simp [macPrograms]
  · intro i hleft hright
    change
      ((List.ofFn (fun bit : Fin n => stageProgram n N left bit)).get
          ⟨i, hleft⟩).eventCost =
        ((List.ofFn (fun bit : Fin n => stageProgram n N right bit)).get
          ⟨i, hright⟩).eventCost
    rw [List.get_ofFn, List.get_ofFn]
    exact stageProgram_eventCost_eq n N left right
      ⟨i, by simpa using hleft⟩

/-- The actual MAC program has a strict event critical path independent of
its compiled constant. -/
lemma macProgram_eventDepth_eq (n N : Nat)
    (left right : PlainAdder.Word n) :
    (macProgram n N left).eventDepth =
      (macProgram n N right).eventDepth := by
  apply appendList_eventDepth_eq_of_forall₂
  apply List.forall₂_of_length_eq_of_get
  · simp [macPrograms]
  · intro i hleft hright
    change
      ((List.ofFn (fun bit : Fin n => stageProgram n N left bit)).get
          ⟨i, hleft⟩).eventDepth =
        ((List.ofFn (fun bit : Fin n => stageProgram n N right bit)).get
          ⟨i, hright⟩).eventDepth
    rw [List.get_ofFn, List.get_ofFn]
    exact stageProgram_eventDepth_eq n N left right
      ⟨i, by simpa using hleft⟩

/-- Folded semantics of the exact full-multiplier program. -/
def macStep (n N : Nat) (a : PlainAdder.Word n) : Registers n → Registers n :=
  UnitaryCircuit.Realizes.stepList (macSteps n N a)

private lemma stepList_flatMap_stageGates (n N : Nat)
    (a : PlainAdder.Word n) :
    ∀ (bits : List (Fin n)) (x : Registers n),
      EncodedBit.GateSpec.stepList
          (bits.flatMap (stageGates n N a)) x =
        UnitaryCircuit.Realizes.stepList
          (bits.map (stageStep n N a)) x
  | [], _ => rfl
  | bit :: rest, x => by
      change
        EncodedBit.GateSpec.stepList
            (stageGates n N a bit ++
              rest.flatMap (stageGates n N a)) x =
          UnitaryCircuit.Realizes.stepList
            (rest.map (stageStep n N a))
            (stageStep n N a bit x)
      rw [EncodedBit.GateSpec.stepList_append]
      rw [stageStep_eq_gateList]
      exact stepList_flatMap_stageGates n N a rest
        (stageStep n N a bit x)

/-- The flattened MAC primitive list agrees pointwise with the established
full-multiplier semantic fold. -/
lemma macStep_eq_gateList (n N : Nat) (a : PlainAdder.Word n)
    (x : Registers n) :
    EncodedBit.GateSpec.stepList (macGates n N a) x =
      macStep n N a x := by
  simpa only [macGates, macStep, macSteps, List.map_ofFn,
    Function.comp_def] using
    stepList_flatMap_stageGates n N a
      (List.ofFn fun bit : Fin n => bit) x

lemma mac_realizes (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit.Realizes (encoding n) (macProgram n N a) environment
      (macStep n N a) :=
  UnitaryCircuit.Realizes.appendList (environment := environment) (encoding n)
    (QubitLayout.canonical _)
    (macPrograms n N a)
    (macSteps n N a) (macStages_realize n N a)

/-- Prefix of the actual multiplier-bit schedule. -/
def macPrefixStep (n N : Nat) (a : PlainAdder.Word n) (bits : Nat) :
    Registers n → Registers n :=
  UnitaryCircuit.Realizes.stepList ((macSteps n N a).take bits)

@[simp] lemma macPrefixStep_zero (n N : Nat) (a : PlainAdder.Word n)
    (x : Registers n) :
    macPrefixStep n N a 0 x = x :=
  rfl

lemma macPrefixStep_succ (n N : Nat) (a : PlainAdder.Word n)
    (bit : Fin n) (x : Registers n) :
    macPrefixStep n N a (bit.val + 1) x =
      stageStep n N a bit (macPrefixStep n N a bit.val x) := by
  unfold macPrefixStep
  let schedule := macSteps n N a
  have hlen : bit.val < schedule.length := by
    rw [macSteps_length]
    exact bit.isLt
  rw [UnitaryCircuit.Realizes.stepList_take_succ schedule bit.val hlen]
  have hget :
      schedule.get ⟨bit.val, hlen⟩ = stageStep n N a bit := by
    simpa [schedule] using macSteps_get n N a bit
  rw [hget]

lemma macPrefixStep_full (n N : Nat) (a : PlainAdder.Word n) :
    macPrefixStep n N a n = macStep n N a := by
  funext x
  unfold macPrefixStep macStep
  rw [List.take_of_length_le]
  simp

/-- Prefix invariant: after `k` stages, the clean target contains the modular
sum selected by exactly the first `k` multiplier bits. -/
lemma macPrefixStep_cleanEndpoint (n N : Nat) (a x : PlainAdder.Word n)
    (initial : Nat) (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hinitial : initial < N) :
    ∀ bits, ∀ _hbits : bits ≤ n,
      macPrefixStep n N a bits (cleanState n N x initial) =
        cleanState n N x
          (Nat.FixedWidth.ModularAccumulate.accumulateSelected N a.val x.val initial bits) := by
  intro bits
  induction bits with
  | zero =>
      intro _hbits
      rw [Nat.FixedWidth.ModularAccumulate.accumulateSelected_zero, Nat.mod_eq_of_lt hinitial]
      rfl
  | succ bits ih =>
      intro hbitsSucc
      have hbitsLt : bits < n := Nat.lt_of_succ_le hbitsSucc
      let bit : Fin n := ⟨bits, hbitsLt⟩
      have ihBits := ih (Nat.le_of_lt hbitsLt)
      rw [show bits + 1 = bit.val + 1 by rfl,
        macPrefixStep_succ n N a bit, ihBits]
      have haccumulator :
          Nat.FixedWidth.ModularAccumulate.accumulateSelected N a.val x.val initial bits < N :=
        Nat.FixedWidth.ModularAccumulate.accumulateSelected_lt hNpos
      simpa [bit, Nat.FixedWidth.ModularAccumulate.accumulateSelected_succ] using
        stageStep_cleanEndpoint n N a x bit
          (Nat.FixedWidth.ModularAccumulate.accumulateSelected N a.val x.val initial bits)
          hNpos hN haccumulator

/-- Full-width clean endpoint of the exact uniform VBE MAC program. -/
lemma macStep_cleanEndpoint (n N : Nat) (a x : PlainAdder.Word n)
    (initial : Nat) (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hinitial : initial < N) :
    macStep n N a (cleanState n N x initial) =
      cleanState n N x ((initial + a.val * x.val) % N) := by
  calc
    macStep n N a (cleanState n N x initial) =
        macPrefixStep n N a n (cleanState n N x initial) := by
      rw [macPrefixStep_full]
    _ = cleanState n N x
          (Nat.FixedWidth.ModularAccumulate.accumulateSelected N a.val x.val initial n) :=
      macPrefixStep_cleanEndpoint n N a x initial hNpos hN hinitial n
        (Nat.le_refl n)
    _ = cleanState n N x ((initial + a.val * x.val) % N) := by
      rw [Nat.FixedWidth.ModularAccumulate.accumulateSelected_eq_add_mul_mod_of_lt_two_pow
        (ZMod.val_lt x)]

/-! ### High-level MAC bridge, actual inverse, and resources -/

/-- Embed high-level MAC data into the complete physical layout.  The logical
flag is retained, so this function is an embedding on all data; the circuit
endpoint below separately requires the public clean-flag precondition. -/
def cleanEmbedding (n N : Nat) (x : MAU.Multiplication.Accumulate.Data N) :
    Registers n :=
  workspaceState n
    (x.multiplicand.val : PlainAdder.Word n)
    0
    (N : PlainAdder.Word n)
    (x.accumulator.val : PlainAdder.Word
    (MAU.Addition.VBECircuit.AdderWidth n))
    x.flag

/-- Under the layout bound, the explicit high-level-to-physical map is
injective; in particular, `cleanEmbedding` does not erase the logical flag. -/
lemma cleanEmbedding_injective (n N : Nat)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    Function.Injective (cleanEmbedding n N) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  intro x y hxy
  have hmultiplicandCast :
      (x.multiplicand.val : PlainAdder.Word n) =
        (y.multiplicand.val : PlainAdder.Word n) := by
    have h := congrArg (fun state => state.multiplicand) hxy
    simpa [cleanEmbedding, workspaceState] using h
  have hmultiplicandVal := congrArg ZMod.val hmultiplicandCast
  have hxmultiplicand :
      ((x.multiplicand.val : Nat) : PlainAdder.Word n).val =
        x.multiplicand.val :=
    ZMod.val_natCast_of_lt (lt_trans (ZMod.val_lt x.multiplicand) hN)
  have hymultiplicand :
      ((y.multiplicand.val : Nat) : PlainAdder.Word n).val =
        y.multiplicand.val :=
    ZMod.val_natCast_of_lt (lt_trans (ZMod.val_lt y.multiplicand) hN)
  rw [hxmultiplicand, hymultiplicand] at hmultiplicandVal
  have hmultiplicand : x.multiplicand = y.multiplicand := by
    apply ZMod.val_injective
    exact hmultiplicandVal
  have haccumulatorCast :
      (x.accumulator.val : PlainAdder.Word
        (MAU.Addition.VBECircuit.AdderWidth n)) =
      (y.accumulator.val : PlainAdder.Word
        (MAU.Addition.VBECircuit.AdderWidth n)) := by
    have h := congrArg (fun state => state.arithmetic.target) hxy
    simpa [cleanEmbedding, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using h
  have haccumulatorVal := congrArg ZMod.val haccumulatorCast
  have hpow :
      2 ^ n < 2 ^ (MAU.Addition.VBECircuit.AdderWidth n) := by
    simp [MAU.Addition.VBECircuit.AdderWidth, pow_succ]
  have hxaccumulator :
      ((x.accumulator.val : Nat) : PlainAdder.Word
        (MAU.Addition.VBECircuit.AdderWidth n)).val =
        x.accumulator.val :=
    ZMod.val_natCast_of_lt
      (lt_trans (lt_trans (ZMod.val_lt x.accumulator) hN) hpow)
  have hyaccumulator :
      ((y.accumulator.val : Nat) : PlainAdder.Word
        (MAU.Addition.VBECircuit.AdderWidth n)).val =
        y.accumulator.val :=
    ZMod.val_natCast_of_lt
      (lt_trans (lt_trans (ZMod.val_lt y.accumulator) hN) hpow)
  rw [hxaccumulator, hyaccumulator] at haccumulatorVal
  have haccumulator : x.accumulator = y.accumulator := by
    apply ZMod.val_injective
    exact haccumulatorVal
  have hflag : x.flag = y.flag := by
    have h := congrArg (fun state => state.arithmetic.reductionFlag) hxy
    simpa [cleanEmbedding, workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using h
  exact MAU.Multiplication.Accumulate.Data.ext hmultiplicand haccumulator hflag

/-- The physical full-register endpoint realizes the public `Data.addScaled`
statement on clean inputs. -/
lemma macStep_cleanEmbedding (n N : Nat) (a : ZMod N)
    (x : MAU.Multiplication.Accumulate.Data N)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hx : x.FlagClean) :
    macStep n N (a.val : PlainAdder.Word n) (cleanEmbedding n N x) =
      cleanEmbedding n N (x.addScaled a) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  let aWord : PlainAdder.Word n := (a.val : PlainAdder.Word n)
  let xWord : PlainAdder.Word n :=
    (x.multiplicand.val : PlainAdder.Word n)
  have haWordVal : aWord.val = a.val := by
    exact ZMod.val_natCast_of_lt (lt_trans (ZMod.val_lt a) hN)
  have hxWordVal : xWord.val = x.multiplicand.val := by
    exact ZMod.val_natCast_of_lt
      (lt_trans (ZMod.val_lt x.multiplicand) hN)
  have haccumulator :
      (x.addScaled a).accumulator.val =
        (x.accumulator.val + a.val * x.multiplicand.val) % N := by
    rw [MAU.Multiplication.Accumulate.Data.addScaled_accumulator,
      ZMod.val_add, ZMod.val_mul, Nat.add_mod_mod]
  have hxFlag : x.flag = false := hx
  have hinput :
      cleanEmbedding n N x = cleanState n N xWord x.accumulator.val := by
    simp only [cleanEmbedding, cleanState, xWord]
    rw [hxFlag]
  have houtput :
      cleanState n N xWord
          ((x.accumulator.val + aWord.val * xWord.val) % N) =
        cleanEmbedding n N (x.addScaled a) := by
    simp only [cleanEmbedding, cleanState,
      MAU.Multiplication.Accumulate.Data.addScaled_multiplicand,
      MAU.Multiplication.Accumulate.Data.addScaled_flag]
    rw [hxFlag, haccumulator, haWordVal, hxWordVal]
  rw [hinput]
  rw [macStep_cleanEndpoint n N aWord xWord x.accumulator.val hNpos hN
    (ZMod.val_lt x.accumulator)]
  exact houtput

/-- The true inverse program is the reversed list of the exact forward gates. -/
def macInverseGates (n N : Nat) (a : PlainAdder.Word n) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (macGates n N a).reverse

/-- The actual adjoint circuit retained for existing inverse-application
lemmas.  Its local GateSpec seam is `macInverseGates`. -/
def macInverseProgram (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  (macProgram n N a).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

instance registersNonempty (n : Nat) : Nonempty (Registers n) :=
  ⟨workspaceState n 0 0 0 0 false⟩

/-- Semantic inverse of the finite full-register MAC permutation. -/
def macInverseStep (n N : Nat) (a : PlainAdder.Word n) :
    Registers n → Registers n :=
  Function.invFun (macStep n N a)

lemma macStep_macInverseStep (n N : Nat) (a : PlainAdder.Word n) :
    Function.RightInverse (macInverseStep n N a) (macStep n N a) := by
  let environment : OracleModel.empty.Interpretation := OracleModel.emptyInterpretation
  let _ : Finite (Registers n) :=
    Finite.of_injective (encoding n).encode (encoding n).encode_injective
  unfold macInverseStep
  exact Function.rightInverse_invFun
    (Finite.surjective_of_injective (mac_realizes (environment := environment) n N a).injective)

/-- Reversing the exact flattened MAC gate list agrees pointwise with the
established inverse permutation. -/
lemma macInverseStep_eq_gateList (n N : Nat) (a : PlainAdder.Word n)
    (x : Registers n) :
    EncodedBit.GateSpec.stepList (macInverseGates n N a) x =
      macInverseStep n N a x := by
  let environment : OracleModel.empty.Interpretation := OracleModel.emptyInterpretation
  have hreverse :
      EncodedBit.GateSpec.stepList (macGates n N a)
          (EncodedBit.GateSpec.stepList (macInverseGates n N a) x) = x := by
    simpa [macInverseGates] using
      EncodedBit.GateSpec.stepList_reverse_stepList
        (macGates n N a).reverse x
  apply (mac_realizes (environment := environment) n N a).injective
  calc
    macStep n N a
        (EncodedBit.GateSpec.stepList (macInverseGates n N a) x) = x := by
      rw [← macStep_eq_gateList]
      exact hreverse
    _ = macStep n N a (macInverseStep n N a x) :=
      (macStep_macInverseStep n N a x).symm

/-- The actual adjoint MAC circuit realizes the inverse full-register
permutation induced by the forward circuit. -/
lemma macInverse_realizes (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit.Realizes (encoding n) (macInverseProgram n N a) environment
      (macInverseStep n N a) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse (mac_realizes (environment := environment) n N a)
    (by
      rw [macInverseProgram, UnitaryCircuit.dagger_matrix]
      rw [Subsingleton.elim
        ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment) environment]
      exact Unitary.star_eq_inv _)
    (macStep_macInverseStep n N a)







/-- Typed circuit obtained from the actual reverse-list program. -/
def macInverseCircuit (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  macInverseProgram n N a

/-- Applying the reverse-list program to a clean forward endpoint restores the
complete encoded physical state, not merely the high-level accumulator. -/
lemma macInverseProgram_cleanEndpoint (n N : Nat) (a : ZMod N)
    (x : MAU.Multiplication.Accumulate.Data N)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hx : x.FlagClean) :
    (macInverseProgram n N (a.val : PlainAdder.Word n)).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
            ((encoding n).encode (cleanEmbedding n N (x.addScaled a))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
          ((encoding n).encode (cleanEmbedding n N x))) := by
  have hforward :=
    (mac_realizes (environment := environment) n N (a.val : PlainAdder.Word n)).apply_encoded_ket
      (cleanEmbedding n N x)
  rw [macStep_cleanEmbedding n N a x hNpos hN hx] at hforward
  rw [← hforward]
  simpa only [macInverseProgram] using
    UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (macProgram n N (a.val : PlainAdder.Word n))
      (macInverseProgram n N (a.val : PlainAdder.Word n))
      (by
        rw [macInverseProgram, UnitaryCircuit.dagger_matrix]
        rw [Subsingleton.elim
          ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment) environment]
        exact Unitary.star_eq_inv _)
      (NormalizedVector.ket
        ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
          ((encoding n).encode (cleanEmbedding n N x))))

/-- On clean forward endpoints, the semantic inverse permutation restores the
complete physical register. -/
lemma macInverseStep_cleanEndpoint (n N : Nat) (a : ZMod N)
    (x : MAU.Multiplication.Accumulate.Data N)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hx : x.FlagClean) :
    macInverseStep n N (a.val : PlainAdder.Word n)
        (cleanEmbedding n N (x.addScaled a)) =
      cleanEmbedding n N x := by
  let environment : OracleModel.empty.Interpretation := OracleModel.emptyInterpretation
  have hrealizes :=
    (macInverse_realizes (environment := environment) n N (a.val : PlainAdder.Word
      n)).apply_encoded_ket
      (cleanEmbedding n N (x.addScaled a))
  rw [macInverseProgram_cleanEndpoint n N a x hNpos hN hx] at hrealizes
  apply (encoding n).encode_injective
  apply (QubitLayout.canonical (encoding n).width).basisEquiv.symm.injective
  exact NormalizedVector.ket_injective hrealizes.symm

/-- Typed circuit of the exact folded VBE multiply-accumulate program. -/
def macCircuit (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((encoding
      n).width)).toQuantum :=
  macProgram n N a

/-- Ordered strict events of the exact multiply-accumulate circuit. -/
def macEventTrace (n N : Nat) (a : PlainAdder.Word n) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (macCircuit n N a).eventTrace

/-- Strict event pool of the exact multiply-accumulate circuit. -/
def macEventCost (n N : Nat) (a : PlainAdder.Word n) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (macCircuit n N a).eventCost

/-- Strict symbolic event critical path of the multiply-accumulate circuit. -/
def macEventDepth (n N : Nat) (a : PlainAdder.Word n) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (macCircuit n N a).eventDepth

/-- Evaluated MAC depth under literal strict-event durations. -/
def macEvaluatedEventDepth (n N : Nat) (a : PlainAdder.Word n)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) : Nat :=
  (macCircuit n N a).evaluatedEventDepth assign

/-- MAC depth selected by one literal event coordinate. -/
def macEventQueryDepth (n N : Nat) (a : PlainAdder.Word n)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  (macCircuit n N a).eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the MAC event pool. -/
def macEventGateCount (n N : Nat) (a : PlainAdder.Word n)
    (label : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count
    (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) label)
    (macCircuit n N a).eventCost

/-- Linearizing MAC event depth recovers its exact strict event pool. -/
lemma macCircuit_resourcesFromEventDepth_eq_eventCost
    (n N : Nat) (a : PlainAdder.Word n) :
    (macCircuit n N a).resourcesFromEventDepth =
      (macCircuit n N a).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (macCircuit n N a)











/-- Exact fixed-layout footprint from the same witness encoding.
The modulus and multiplier remain explicit to match the sibling resource
projections, while the fixed encoding makes the result depend only on `n`. -/
@[nolint unusedArguments]
def macQubitCount (n _N : Nat) (_a : PlainAdder.Word n) : Nat :=
  (encoding n).width

@[simp] lemma macQubitCount_eq (n N : Nat) (a : PlainAdder.Word n) :
    macQubitCount n N a = 5 * n + 4 := by
  simp [macQubitCount]



/-- Normalized-ket correctness for the same physical circuit whose exact
resources are projected above. -/
lemma macCircuit_applyNormalized_clean_ket (n N : Nat) (a : ZMod N)
    (x : MAU.Multiplication.Accumulate.Data N)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hx : x.FlagClean) :
    (macCircuit n N (a.val : PlainAdder.Word n)).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
            ((encoding n).encode (cleanEmbedding n N x)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
          ((encoding n).encode (cleanEmbedding n N (x.addScaled a)))) := by
  simpa only [macCircuit,
    macStep_cleanEmbedding n N a x hNpos hN hx] using
    (mac_realizes (environment := environment) n N (a.val : PlainAdder.Word n)).apply_encoded_ket
      (cleanEmbedding n N x)

end

end VBECircuit
end MAU.Multiplication.Accumulate
end QuantumAlg

end
