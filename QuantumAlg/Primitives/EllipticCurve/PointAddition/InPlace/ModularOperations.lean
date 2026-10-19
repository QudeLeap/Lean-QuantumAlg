/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Montgomery.Operations

/-!
# Width-neutral modular operations for the in-place point schedule

The straight-line program interleaves multiplication and inversion with
modular additions, subtractions, and negation; the source implementation uses
Montgomery arithmetic [RNSL17, ECDLP.tex:391,514-530,687].  This module
routes those operations through the same compact arithmetic carrier.  Live
point words are parked only in the existing branch-history word and every
route is reversed at the operation boundary; no register is appended.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace ModularOperations

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- A literal constant xor updates one structural word port to the word
specified by its output bits. -/
private lemma xorConstantStep_eq_set_of_testBit
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (port : Arithmetic.BlockBank.WordPort encoding width)
    (constant : Fin (2 ^ width)) (state : Data)
    (value : Word width)
    (hvalue : ∀ bit : Fin width, value.val.testBit bit.val =
      ((port.read state).val.testBit bit.val ^^
        constant.val.testBit bit.val)) :
    EncodedBit.Word.xorConstantStep port.word constant state =
      port.set state value := by
  have hframe :
      port.set (EncodedBit.Word.xorConstantStep port.word constant state) 0 =
        port.set state 0 := by
    unfold EncodedBit.Word.xorConstantStep
    apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project := fun next => port.set next 0)
    intro gate hgate
    rw [EncodedBit.Word.xorConstantGates] at hgate
    rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
    exact port.clear_flip bit
  have hresult :
      port.read (EncodedBit.Word.xorConstantStep port.word constant state) =
        value := by
    apply word_eq_of_testBit_eq
    intro bit
    rw [← port.get_bit bit
      (EncodedBit.Word.xorConstantStep port.word constant state)]
    rw [EncodedBit.Word.xorConstantStep_get_target port.word constant bit
      (fun other hne => port.pairwise_ne other bit hne)]
    rw [port.get_bit bit state]
    exact (hvalue bit).symm
  calc
    EncodedBit.Word.xorConstantStep port.word constant state =
        port.set
          (port.set
            (EncodedBit.Word.xorConstantStep port.word constant state) 0)
          (port.read
            (EncodedBit.Word.xorConstantStep port.word constant state)) := by
              rw [port.set_set, port.set_read]
    _ = port.set (port.set state 0) value := by rw [hframe, hresult]
    _ = port.set state value := by rw [port.set_set]

/-! ## Constant updates of mutable x -/

/-- Route a possibly-live `t0` into the existing low history half, put
mutable `x1` in the compact public target, and load one classical residue as
the retained update source. -/
def constantXPrefixGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  RegisterRouting.saveT0LowGates fieldTail.succ counterWidth ++
    RegisterRouting.historyLowToT0Gates fieldTail.succ counterWidth ++
    RegisterRouting.swapXT0Gates fieldTail.succ counterWidth ++
    MontgomeryOperations.normalizeGates fieldTail.succ counterWidth p hp ++
    EncodedBit.Word.xorConstantGates
      (RegisterRouting.rCoefficientWord fieldTail.succ counterWidth) constant

/-- Canonical target-update boundary reached by the constant-x prefix. -/
def constantXBoundary
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth :=
  let initial := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      initial t0
  { savedT0 with arithmetic :=
      (CompactCorrection.targetUpdateState fieldTail counterWidth
        savedT0.arithmetic
        (CompactCorrection.widenFixedWord fieldTail.succ constant)
        (CompactCorrection.widenFixedWord fieldTail.succ 0)
        (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
        mutableX) }

/-- The reversible constant-x prefix reaches the certified target-update
boundary without losing a live `t0`. -/
lemma constantXPrefixGates_stepList
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 constant : Word fieldTail.succ) :
    EncodedBit.GateSpec.stepList
        (constantXPrefixGates fieldTail counterWidth p hp constant)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 constant := by
  let initial := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      initial t0
  let clearedT0 :=
    (RegisterRouting.t0Port fieldTail.succ counterWidth).set savedT0 0
  let swapped :=
    { clearedT0 with arithmetic :=
      { clearedT0.arithmetic with
        core := { clearedT0.arithmetic.core with
          v := clearedT0.arithmetic.target }
        target := clearedT0.arithmetic.core.v } }
  let normalized :=
    (RegisterRouting.activeBit fieldTail.succ counterWidth).flip
      ((RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).set
        ((RegisterRouting.uPort fieldTail.succ counterWidth).set swapped 0)
        (MontgomeryOperations.modulusWord fieldTail.succ p hp))
  have hsaveT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveT0LowGates fieldTail.succ counterWidth) initial =
        savedT0 := by
    simpa only [RegisterRouting.saveT0LowGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
          ⟨bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth sourceBit
            ⟨targetBit.val, by omega⟩))
        initial t0 (by rfl)
        (by
          simp [initial, MontgomeryOperations.cleanState,
            RegisterRouting.historyLowPort, MK.initialRegisters])
  have hclearT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.historyLowToT0Gates fieldTail.succ counterWidth)
          savedT0 = clearedT0 := by
    simpa only [RegisterRouting.historyLowToT0Gates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
            ⟨bit.val, by omega⟩))
        (fun sourceBit targetBit =>
          RegisterRouting.t0_history_ne fieldTail.succ counterWidth targetBit
            ⟨sourceBit.val, by omega⟩)
        savedT0 (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hswap :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.swapXT0Gates fieldTail.succ counterWidth)
          clearedT0 = swapped := by
    exact RegisterRouting.swapXT0Gates_stepList fieldTail.succ counterWidth
      clearedT0
  have hu :
      (RegisterRouting.uPort fieldTail.succ counterWidth).read swapped =
        MontgomeryOperations.modulusWord fieldTail.succ p hp := by
    change (RegisterRouting.uPort fieldTail.succ counterWidth).read initial =
      ⟨p, hp⟩
    rfl
  have hs :
      (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
        swapped = 1 := by
    change (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
      initial = 1
    simp [initial, MontgomeryOperations.cleanState,
      RegisterRouting.sCoefficientPort, MK.initialRegisters]
  have hnormalize :
      EncodedBit.GateSpec.stepList
          (MontgomeryOperations.normalizeGates fieldTail.succ counterWidth p hp)
          swapped = normalized :=
    MontgomeryOperations.normalizeGates_stepList fieldTail.succ counterWidth p
      hp swapped hu hs
  have hrClean :
      (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).read
        normalized = 0 := by
    change (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).read
      initial = 0
    simp [initial, MontgomeryOperations.cleanState,
      RegisterRouting.rCoefficientPort, MK.initialRegisters]
  have hload :
      EncodedBit.GateSpec.stepList
          (EncodedBit.Word.xorConstantGates
            (RegisterRouting.rCoefficientWord fieldTail.succ counterWidth)
            constant) normalized =
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).set
          normalized constant := by
    change EncodedBit.Word.xorConstantStep
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).word
        constant normalized = _
    apply xorConstantStep_eq_set_of_testBit
    intro bit
    rw [hrClean]
    simp
  simp only [constantXPrefixGates,
    EncodedBit.GateSpec.stepList_append]
  rw [hsaveT0, hclearT0, hswap, hnormalize, hload]
  simp [constantXBoundary, normalized, swapped, clearedT0, savedT0, initial,
    MontgomeryOperations.cleanState, RegisterRouting.activeBit_flip,
    RegisterRouting.uPort, RegisterRouting.t0Port,
    RegisterRouting.sCoefficientPort_set,
    RegisterRouting.rCoefficientPort_set,
    CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
    CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
    MK.initialRegisters, MK.Compact.cleanSharedWork,
    MontgomeryOperations.modulusWord]

/-- Native constant subtraction on mutable `x1`, preserving a possibly-live
`t0` and restoring every borrowed compact field. -/
def subtractConstantXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := constantXPrefixGates fieldTail counterWidth p hp constant
  prep ++
    ArithmeticLift.gates fieldTail.succ counterWidth
      (CompactCorrection.targetUpdateGates fieldTail counterWidth p) ++
    prep.reverse

/-- Native constant addition on mutable `x1`, using the exact reverse target
update ledger. -/
def addConstantXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := constantXPrefixGates fieldTail counterWidth p hp constant
  prep ++
    ArithmeticLift.gates fieldTail.succ counterWidth
      (CompactCorrection.targetUpdateGates fieldTail counterWidth p).reverse ++
    prep.reverse

def subtractConstantXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (subtractConstantXGates fieldTail counterWidth p hp constant)

def addConstantXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (addConstantXGates fieldTail counterWidth p hp constant)

lemma subtractConstantXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 constant : Word fieldTail.succ)
    (hx : mutableX.val < p) (hc : constant.val < p) :
    subtractConstantXStep fieldTail counterWidth p hp constant
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
          mutableX constant) t0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let result := CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
    mutableX constant
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ result t0
  let prep := constantXPrefixGates fieldTail counterWidth p hp constant
  let base :=
    ((RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      input t0).arithmetic
  have hinput := constantXPrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» mutableX t0 constant
  have houtput := constantXPrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» result t0 constant
  have hupdate := CompactCorrection.targetUpdateStep_state fieldTail
    counterWidth p base
    constant mutableX hpPos hp hc hx
  have hboundaryInput :
      (constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 constant).arithmetic =
        CompactCorrection.targetUpdateState fieldTail counterWidth base
          (CompactCorrection.widenFixedWord fieldTail.succ constant)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          mutableX := by
    rfl
  change EncodedBit.GateSpec.stepList
      (prep ++
        ArithmeticLift.gates fieldTail.succ counterWidth
          (CompactCorrection.targetUpdateGates fieldTail counterWidth p) ++
        prep.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList prep input =
      constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 constant by simpa [prep, input] using hinput]
  rw [ArithmeticLift.gates_stepList]
  change
    EncodedBit.GateSpec.stepList prep.reverse
      { constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0 constant with
        arithmetic := CompactCorrection.targetUpdateStep fieldTail
          counterWidth p
          (constantXBoundary fieldTail counterWidth p hp control mutableY
            «λ» mutableX t0 constant).arithmetic } = output
  rw [hboundaryInput, hupdate]
  have hboundary :
      { constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0 constant with
        arithmetic := CompactCorrection.targetUpdateState fieldTail
          counterWidth base
          (CompactCorrection.widenFixedWord fieldTail.succ constant)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          result } =
        EncodedBit.GateSpec.stepList prep output := by
    simpa [prep, output, result, base, input, constantXBoundary,
      CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
      CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
      MontgomeryOperations.cleanState, MK.initialRegisters,
      MK.Compact.cleanSharedWork] using houtput.symm
  rw [hboundary]
  exact EncodedBit.GateSpec.stepList_reverse_stepList prep output

lemma addConstantXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 constant : Word fieldTail.succ)
    (hx : mutableX.val < p) (hc : constant.val < p) :
    addConstantXStep fieldTail counterWidth p hp constant
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (CompactCorrection.modularSumFixedWord fieldTail p hpPos hp mutableX
          constant) t0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let result := CompactCorrection.modularSumFixedWord fieldTail p hpPos hp
    mutableX constant
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ result t0
  let prep := constantXPrefixGates fieldTail counterWidth p hp constant
  let base :=
    ((RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      input t0).arithmetic
  have hinput := constantXPrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» mutableX t0 constant
  have houtput := constantXPrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» result t0 constant
  have hupdate := CompactCorrection.targetUpdateReverseStep_state fieldTail
    counterWidth p base
    constant mutableX hpPos hp hc hx
  have hboundaryInput :
      (constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 constant).arithmetic =
        CompactCorrection.targetUpdateState fieldTail counterWidth base
          (CompactCorrection.widenFixedWord fieldTail.succ constant)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          mutableX := by
    rfl
  change EncodedBit.GateSpec.stepList
      (prep ++
        ArithmeticLift.gates fieldTail.succ counterWidth
          (CompactCorrection.targetUpdateGates fieldTail counterWidth p).reverse ++
        prep.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList prep input =
      constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 constant by simpa [prep, input] using hinput]
  rw [ArithmeticLift.gates_stepList]
  change
    EncodedBit.GateSpec.stepList prep.reverse
      { constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0 constant with
        arithmetic := CompactCorrection.targetUpdateReverseStep fieldTail
          counterWidth p
          (constantXBoundary fieldTail counterWidth p hp control mutableY
            «λ» mutableX t0 constant).arithmetic } = output
  rw [hboundaryInput, hupdate]
  have hboundary :
      { constantXBoundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0 constant with
        arithmetic := CompactCorrection.targetUpdateState fieldTail
          counterWidth base
          (CompactCorrection.widenFixedWord fieldTail.succ constant)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          result } =
        EncodedBit.GateSpec.stepList prep output := by
    simpa [prep, output, result, base, input, constantXBoundary,
      CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
      CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
      MontgomeryOperations.cleanState, MK.initialRegisters,
      MK.Compact.cleanSharedWork] using houtput.symm
  rw [hboundary]
  exact EncodedBit.GateSpec.stepList_reverse_stepList prep output

lemma subtractConstantX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (subtractConstantXGates fieldTail counterWidth p hp constant)) environment
      (subtractConstantXStep fieldTail counterWidth p hp constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma addConstantX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (addConstantXGates fieldTail counterWidth p hp constant)) environment
      (addConstantXStep fieldTail counterWidth p hp constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

/-! ## Variable updates between mutable x and t0 -/

/-- Route mutable `x1` into the retained coefficient and clear its physical
word, leaving `t0` as the public update target. -/
def t0FromXPrefixGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  RegisterRouting.xToCoefficientGates fieldTail.succ counterWidth ++
    RegisterRouting.coefficientToXGates fieldTail.succ counterWidth ++
    MontgomeryOperations.normalizeGates fieldTail.succ counterWidth p hp

def t0FromXBoundary
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth :=
  let initial := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  { initial with arithmetic :=
      (CompactCorrection.targetUpdateState fieldTail counterWidth
        initial.arithmetic
        (CompactCorrection.widenFixedWord fieldTail.succ mutableX)
        (CompactCorrection.widenFixedWord fieldTail.succ 0)
        (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
        t0) }

lemma t0FromXPrefixGates_stepList
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ) :
    EncodedBit.GateSpec.stepList
        (t0FromXPrefixGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      t0FromXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 := by
  let initial := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let loaded :=
    (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).set
      initial mutableX
  let cleared :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set loaded 0
  let normalized :=
    (RegisterRouting.activeBit fieldTail.succ counterWidth).flip
      ((RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).set
        ((RegisterRouting.uPort fieldTail.succ counterWidth).set cleared 0)
        (MontgomeryOperations.modulusWord fieldTail.succ p hp))
  have hload :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.xToCoefficientGates fieldTail.succ counterWidth)
          initial = loaded := by
    simpa only [RegisterRouting.xToCoefficientGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.mutableXPort fieldTail.succ counterWidth)
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ
          counterWidth bit bit)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            sourceBit targetBit))
        initial mutableX (by rfl)
        (by
          simp [initial, MontgomeryOperations.cleanState,
            RegisterRouting.rCoefficientPort, MK.initialRegisters])
  have hclear :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.coefficientToXGates fieldTail.succ counterWidth)
          loaded = cleared := by
    simpa only [RegisterRouting.coefficientToXGates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth)
        (RegisterRouting.mutableXPort fieldTail.succ counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            bit bit))
        (fun sourceBit targetBit =>
          RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            targetBit sourceBit)
        loaded (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hu :
      (RegisterRouting.uPort fieldTail.succ counterWidth).read cleared =
        MontgomeryOperations.modulusWord fieldTail.succ p hp := by
    change (RegisterRouting.uPort fieldTail.succ counterWidth).read initial =
      ⟨p, hp⟩
    rfl
  have hs :
      (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
        cleared = 1 := by
    change (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
      initial = 1
    simp [initial, MontgomeryOperations.cleanState,
      RegisterRouting.sCoefficientPort, MK.initialRegisters]
  have hnormalize := MontgomeryOperations.normalizeGates_stepList
    fieldTail.succ counterWidth p hp cleared hu hs
  simp only [t0FromXPrefixGates, EncodedBit.GateSpec.stepList_append]
  rw [hload, hclear, hnormalize]
  simp [t0FromXBoundary, cleared, loaded, initial,
    MontgomeryOperations.cleanState, RegisterRouting.activeBit_flip,
    RegisterRouting.uPort, RegisterRouting.sCoefficientPort_set,
    RegisterRouting.rCoefficientPort_set, RegisterRouting.mutableXPort,
    CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
    CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
    MK.initialRegisters, MK.Compact.cleanSharedWork,
    MontgomeryOperations.modulusWord]

/-- Subtract mutable `x1` from `t0` while preserving `x1` and restoring all
borrowed work. -/
def subtractXFromT0Gates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := t0FromXPrefixGates fieldTail counterWidth p hp
  prep ++ ArithmeticLift.gates fieldTail.succ counterWidth
      (CompactCorrection.targetUpdateGates fieldTail counterWidth p) ++
    prep.reverse

def subtractXFromT0Step
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (subtractXFromT0Gates fieldTail counterWidth p hp)

lemma subtractXFromT0Step_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) (ht0 : t0.val < p) :
    subtractXFromT0Step fieldTail counterWidth p hp
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩ mutableX
        (CompactCorrection.modularDifferenceWord fieldTail p hpPos hp t0
          mutableX) := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let result := CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
    t0 mutableX
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX result
  let prep := t0FromXPrefixGates fieldTail counterWidth p hp
  let base := input.arithmetic
  have hinput := t0FromXPrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» mutableX t0
  have houtput := t0FromXPrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» mutableX result
  have hupdate := CompactCorrection.targetUpdateStep_state fieldTail
    counterWidth p base mutableX t0 hpPos hp hx ht0
  have hboundaryInput :
      (t0FromXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0).arithmetic =
        CompactCorrection.targetUpdateState fieldTail counterWidth base
          (CompactCorrection.widenFixedWord fieldTail.succ mutableX)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          t0 := by
    rfl
  change EncodedBit.GateSpec.stepList
      (prep ++ ArithmeticLift.gates fieldTail.succ counterWidth
        (CompactCorrection.targetUpdateGates fieldTail counterWidth p) ++
        prep.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList prep input =
      t0FromXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 by simpa [prep, input] using hinput]
  rw [ArithmeticLift.gates_stepList]
  change EncodedBit.GateSpec.stepList prep.reverse
    { t0FromXBoundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 with
      arithmetic := CompactCorrection.targetUpdateStep fieldTail counterWidth p
        (t0FromXBoundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0).arithmetic } = output
  rw [hboundaryInput, hupdate]
  have hboundary :
      { t0FromXBoundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0 with
        arithmetic := CompactCorrection.targetUpdateState fieldTail counterWidth
          base (CompactCorrection.widenFixedWord fieldTail.succ mutableX)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          result } = EncodedBit.GateSpec.stepList prep output := by
    simpa [prep, output, result, base, input, t0FromXBoundary,
      CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
      CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
      MontgomeryOperations.cleanState, MK.initialRegisters,
      MK.Compact.cleanSharedWork] using houtput.symm
  rw [hboundary]
  exact EncodedBit.GateSpec.stepList_reverse_stepList prep output

/-- Route live `t0` into the retained coefficient, exchange the x/t0 words,
and clear the physical active-source word.  The public update target is now
the original mutable `x1`. -/
def xFromT0PrefixGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  RegisterRouting.t0ToCoefficientGates fieldTail.succ counterWidth ++
    RegisterRouting.swapXT0Gates fieldTail.succ counterWidth ++
    RegisterRouting.coefficientToXGates fieldTail.succ counterWidth ++
    MontgomeryOperations.normalizeGates fieldTail.succ counterWidth p hp

def xFromT0Boundary
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth :=
  let initial := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  { initial with arithmetic :=
      (CompactCorrection.targetUpdateState fieldTail counterWidth
        initial.arithmetic
        (CompactCorrection.widenFixedWord fieldTail.succ t0)
        (CompactCorrection.widenFixedWord fieldTail.succ 0)
        (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
        mutableX) }

lemma xFromT0PrefixGates_stepList
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ) :
    EncodedBit.GateSpec.stepList
        (xFromT0PrefixGates fieldTail counterWidth p hp)
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 := by
  let initial := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let loaded :=
    (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).set
      initial t0
  let swapped :=
    { loaded with arithmetic :=
      { loaded.arithmetic with
        core := { loaded.arithmetic.core with v := loaded.arithmetic.target }
        target := loaded.arithmetic.core.v } }
  let cleared :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set swapped 0
  let normalized :=
    (RegisterRouting.activeBit fieldTail.succ counterWidth).flip
      ((RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).set
        ((RegisterRouting.uPort fieldTail.succ counterWidth).set cleared 0)
        (MontgomeryOperations.modulusWord fieldTail.succ p hp))
  have hload :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.t0ToCoefficientGates fieldTail.succ counterWidth)
          initial = loaded := by
    simpa only [RegisterRouting.t0ToCoefficientGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.t0_rCoefficient_ne fieldTail.succ
          counterWidth bit bit)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.t0_rCoefficient_ne fieldTail.succ counterWidth
            sourceBit targetBit))
        initial t0 (by rfl)
        (by
          simp [initial, MontgomeryOperations.cleanState,
            RegisterRouting.rCoefficientPort, MK.initialRegisters])
  have hswap :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.swapXT0Gates fieldTail.succ counterWidth) loaded =
        swapped := by
    exact RegisterRouting.swapXT0Gates_stepList fieldTail.succ counterWidth
      loaded
  have hclear :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.coefficientToXGates fieldTail.succ counterWidth)
          swapped = cleared := by
    simpa only [RegisterRouting.coefficientToXGates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth)
        (RegisterRouting.mutableXPort fieldTail.succ counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            bit bit))
        (fun sourceBit targetBit =>
          RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            targetBit sourceBit)
        swapped (by
          calc
            (RegisterRouting.rCoefficientPort fieldTail.succ
                counterWidth).read swapped =
                (RegisterRouting.rCoefficientPort fieldTail.succ
                  counterWidth).read loaded := by rfl
            _ = t0 := Arithmetic.BlockBank.WordPort.read_set _ _ _
            _ = (RegisterRouting.mutableXPort fieldTail.succ
                counterWidth).read swapped := by rfl)
  have hu :
      (RegisterRouting.uPort fieldTail.succ counterWidth).read cleared =
        MontgomeryOperations.modulusWord fieldTail.succ p hp := by
    change (RegisterRouting.uPort fieldTail.succ counterWidth).read initial =
      ⟨p, hp⟩
    rfl
  have hs :
      (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
        cleared = 1 := by
    change (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
      initial = 1
    simp [initial, MontgomeryOperations.cleanState,
      RegisterRouting.sCoefficientPort, MK.initialRegisters]
  have hnormalize := MontgomeryOperations.normalizeGates_stepList
    fieldTail.succ counterWidth p hp cleared hu hs
  simp only [xFromT0PrefixGates, EncodedBit.GateSpec.stepList_append]
  rw [hload, hswap, hclear, hnormalize]
  simp [xFromT0Boundary, cleared, swapped, loaded, initial,
    MontgomeryOperations.cleanState, RegisterRouting.activeBit_flip,
    RegisterRouting.uPort, RegisterRouting.sCoefficientPort_set,
    RegisterRouting.rCoefficientPort_set, RegisterRouting.mutableXPort,
    CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
    CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
    MK.initialRegisters, MK.Compact.cleanSharedWork,
    MontgomeryOperations.modulusWord]

def subtractT0FromXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := xFromT0PrefixGates fieldTail counterWidth p hp
  prep ++ ArithmeticLift.gates fieldTail.succ counterWidth
      (CompactCorrection.targetUpdateGates fieldTail counterWidth p) ++
    prep.reverse

def addT0ToXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := xFromT0PrefixGates fieldTail counterWidth p hp
  prep ++ ArithmeticLift.gates fieldTail.succ counterWidth
      (CompactCorrection.targetUpdateGates fieldTail counterWidth p).reverse ++
    prep.reverse

def subtractT0FromXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (subtractT0FromXGates fieldTail counterWidth p hp)

def addT0ToXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (addT0ToXGates fieldTail counterWidth p hp)

lemma subtractT0FromXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) (ht0 : t0.val < p) :
    subtractT0FromXStep fieldTail counterWidth p hp
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (CompactCorrection.modularDifferenceWord fieldTail p hpPos hp mutableX
          t0) t0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let result := CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
    mutableX t0
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ result t0
  let prep := xFromT0PrefixGates fieldTail counterWidth p hp
  let base := input.arithmetic
  have hinput := xFromT0PrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» mutableX t0
  have houtput := xFromT0PrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» result t0
  have hupdate := CompactCorrection.targetUpdateStep_state fieldTail
    counterWidth p base t0 mutableX hpPos hp ht0 hx
  have hboundaryInput :
      (xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0).arithmetic =
        CompactCorrection.targetUpdateState fieldTail counterWidth base
          (CompactCorrection.widenFixedWord fieldTail.succ t0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          mutableX := by
    rfl
  change EncodedBit.GateSpec.stepList
      (prep ++ ArithmeticLift.gates fieldTail.succ counterWidth
        (CompactCorrection.targetUpdateGates fieldTail counterWidth p) ++
        prep.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList prep input =
      xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 by simpa [prep, input] using hinput]
  rw [ArithmeticLift.gates_stepList]
  change EncodedBit.GateSpec.stepList prep.reverse
    { xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 with
      arithmetic := CompactCorrection.targetUpdateStep fieldTail counterWidth p
        (xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0).arithmetic } = output
  rw [hboundaryInput, hupdate]
  have hboundary :
      { xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0 with
        arithmetic := CompactCorrection.targetUpdateState fieldTail counterWidth
          base (CompactCorrection.widenFixedWord fieldTail.succ t0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          result } = EncodedBit.GateSpec.stepList prep output := by
    simpa [prep, output, result, base, input, xFromT0Boundary,
      CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
      CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
      MontgomeryOperations.cleanState, MK.initialRegisters,
      MK.Compact.cleanSharedWork] using houtput.symm
  rw [hboundary]
  exact EncodedBit.GateSpec.stepList_reverse_stepList prep output

lemma addT0ToXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) (ht0 : t0.val < p) :
    addT0ToXStep fieldTail counterWidth p hp
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (CompactCorrection.modularSumFixedWord fieldTail p hpPos hp mutableX t0)
        t0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let result := CompactCorrection.modularSumFixedWord fieldTail p hpPos hp
    mutableX t0
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ result t0
  let prep := xFromT0PrefixGates fieldTail counterWidth p hp
  let base := input.arithmetic
  have hinput := xFromT0PrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» mutableX t0
  have houtput := xFromT0PrefixGates_stepList fieldTail counterWidth p hp
    control mutableY «λ» result t0
  have hupdate := CompactCorrection.targetUpdateReverseStep_state fieldTail
    counterWidth p base t0 mutableX hpPos hp ht0 hx
  have hboundaryInput :
      (xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0).arithmetic =
        CompactCorrection.targetUpdateState fieldTail counterWidth base
          (CompactCorrection.widenFixedWord fieldTail.succ t0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          mutableX := by
    rfl
  change EncodedBit.GateSpec.stepList
      (prep ++ ArithmeticLift.gates fieldTail.succ counterWidth
        (CompactCorrection.targetUpdateGates fieldTail counterWidth p).reverse ++
        prep.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList prep input =
      xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 by simpa [prep, input] using hinput]
  rw [ArithmeticLift.gates_stepList]
  change EncodedBit.GateSpec.stepList prep.reverse
    { xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
        mutableX t0 with
      arithmetic := CompactCorrection.targetUpdateReverseStep fieldTail
        counterWidth p
        (xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0).arithmetic } = output
  rw [hboundaryInput, hupdate]
  have hboundary :
      { xFromT0Boundary fieldTail counterWidth p hp control mutableY «λ»
          mutableX t0 with
        arithmetic := CompactCorrection.targetUpdateState fieldTail counterWidth
          base (CompactCorrection.widenFixedWord fieldTail.succ t0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
          result } = EncodedBit.GateSpec.stepList prep output := by
    simpa [prep, output, result, base, input, xFromT0Boundary,
      CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
      CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
      MontgomeryOperations.cleanState, MK.initialRegisters,
      MK.Compact.cleanSharedWork] using houtput.symm
  rw [hboundary]
  exact EncodedBit.GateSpec.stepList_reverse_stepList prep output

/-! ## Coordinate exchange and y-coordinate constants -/

/-- Exchange mutable `x1` and `y1` through the already-clean `t0` word. -/
def swapXYGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  RegisterRouting.swapXT0Gates fieldWidth counterWidth ++
    RegisterRouting.swapYT0Gates fieldWidth counterWidth ++
    RegisterRouting.swapXT0Gates fieldWidth counterWidth

/-- The three-swap route exchanges exactly the two mutable coordinates and
returns `t0` to zero. -/
lemma swapXYGates_cleanEndpoint
    (fieldWidth counterWidth p : Nat) (hp : p < 2 ^ fieldWidth)
    (control : Bool) (mutableY «λ» mutableX : Word fieldWidth) :
    EncodedBit.GateSpec.stepList (swapXYGates fieldWidth counterWidth)
        (MontgomeryOperations.cleanState fieldWidth counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldWidth counterWidth control
        mutableX «λ» ⟨p, hp⟩ mutableY 0 := by
  simp only [swapXYGates, EncodedBit.GateSpec.stepList_append]
  rw [RegisterRouting.swapXT0Gates_stepList,
    RegisterRouting.swapYT0Gates_stepList,
    RegisterRouting.swapXT0Gates_stepList]
  rfl

/-- Constant subtraction on mutable `y1`, obtained by reversibly exchanging
the coordinates and reusing the certified constant-x ledger. -/
def subtractConstantYGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let swap := swapXYGates fieldTail.succ counterWidth
  swap ++ subtractConstantXGates fieldTail counterWidth p hp constant ++
    swap.reverse

/-- Constant addition on mutable `y1` with the same clean carrier contract. -/
def addConstantYGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let swap := swapXYGates fieldTail.succ counterWidth
  swap ++ addConstantXGates fieldTail counterWidth p hp constant ++
    swap.reverse

def subtractConstantYStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (subtractConstantYGates fieldTail counterWidth p hp constant)

def addConstantYStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (addConstantYGates fieldTail counterWidth p hp constant)

lemma subtractConstantYStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX constant : Word fieldTail.succ)
    (hy : mutableY.val < p) (hc : constant.val < p) :
    subtractConstantYStep fieldTail counterWidth p hp constant
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        (CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
          mutableY constant) «λ» ⟨p, hp⟩ mutableX 0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX 0
  let result := CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
    mutableY constant
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control result «λ» ⟨p, hp⟩ mutableX 0
  let swap := swapXYGates fieldTail.succ counterWidth
  have hinput := swapXYGates_cleanEndpoint fieldTail.succ counterWidth p hp
    control mutableY «λ» mutableX
  have hmiddle := subtractConstantXStep_cleanEndpoint fieldTail counterWidth p
    hpPos hp control mutableX «λ» mutableY 0 constant hy hc
  have houtput := swapXYGates_cleanEndpoint fieldTail.succ counterWidth p hp
    control result «λ» mutableX
  change EncodedBit.GateSpec.stepList
      (swap ++ subtractConstantXGates fieldTail counterWidth p hp constant ++
        swap.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList swap input =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ mutableY 0 by
    simpa [swap, input] using hinput]
  rw [show EncodedBit.GateSpec.stepList
      (subtractConstantXGates fieldTail counterWidth p hp constant)
      (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ mutableY 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ result 0 by
    simpa [subtractConstantXStep, result] using hmiddle]
  rw [show MontgomeryOperations.cleanState fieldTail.succ counterWidth control
      mutableX «λ» ⟨p, hp⟩ result 0 =
      EncodedBit.GateSpec.stepList swap output by
    simpa [swap, output, result] using houtput.symm]
  exact EncodedBit.GateSpec.stepList_reverse_stepList swap output

lemma addConstantYStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX constant : Word fieldTail.succ)
    (hy : mutableY.val < p) (hc : constant.val < p) :
    addConstantYStep fieldTail counterWidth p hp constant
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        (CompactCorrection.modularSumFixedWord fieldTail p hpPos hp mutableY
          constant) «λ» ⟨p, hp⟩ mutableX 0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX 0
  let result := CompactCorrection.modularSumFixedWord fieldTail p hpPos hp
    mutableY constant
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control result «λ» ⟨p, hp⟩ mutableX 0
  let swap := swapXYGates fieldTail.succ counterWidth
  have hinput := swapXYGates_cleanEndpoint fieldTail.succ counterWidth p hp
    control mutableY «λ» mutableX
  have hmiddle := addConstantXStep_cleanEndpoint fieldTail counterWidth p hpPos
    hp control mutableX «λ» mutableY 0 constant hy hc
  have houtput := swapXYGates_cleanEndpoint fieldTail.succ counterWidth p hp
    control result «λ» mutableX
  change EncodedBit.GateSpec.stepList
      (swap ++ addConstantXGates fieldTail counterWidth p hp constant ++
        swap.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList swap input =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ mutableY 0 by
    simpa [swap, input] using hinput]
  rw [show EncodedBit.GateSpec.stepList
      (addConstantXGates fieldTail counterWidth p hp constant)
      (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ mutableY 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ result 0 by
    simpa [addConstantXStep, result] using hmiddle]
  rw [show MontgomeryOperations.cleanState fieldTail.succ counterWidth control
      mutableX «λ» ⟨p, hp⟩ result 0 =
      EncodedBit.GateSpec.stepList swap output by
    simpa [swap, output, result] using houtput.symm]
  exact EncodedBit.GateSpec.stepList_reverse_stepList swap output

/-! ## In-place modular negation -/

/-- Negate mutable `x1` through two reversible modular shears and one exact
word exchange.  The initially clean `t0` word is returned to zero. -/
def negateXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  subtractXFromT0Gates fieldTail counterWidth p hp ++
    addT0ToXGates fieldTail counterWidth p hp ++
    RegisterRouting.swapXT0Gates fieldTail.succ counterWidth

def negateXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList (negateXGates fieldTail counterWidth p hp)

lemma negateXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX : Word fieldTail.succ)
    (hx : mutableX.val < p) :
    negateXStep fieldTail counterWidth p hp
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0
          mutableX) 0 := by
  let neg := CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0
    mutableX
  have hneg : neg.val < p := by
    simp [neg, CompactCorrection.modularDifferenceWord_val,
      Nat.mod_lt _ hpPos]
  have hsum :
      CompactCorrection.modularSumFixedWord fieldTail p hpPos hp mutableX neg =
        0 := by
    apply Fin.ext
    simp only [CompactCorrection.modularSumFixedWord_val, neg,
      CompactCorrection.modularDifferenceWord_val, Fin.val_zero]
    by_cases hx0 : mutableX.val = 0
    · simp [hx0]
    · have hsub : p - mutableX.val < p := by omega
      rw [Nat.zero_add, Nat.mod_eq_of_lt hsub]
      have hadd : mutableX.val + (p - mutableX.val) = p := by omega
      rw [hadd, Nat.mod_self]
  have hfirst := subtractXFromT0Step_cleanEndpoint fieldTail counterWidth p
    hpPos hp control mutableY «λ» mutableX 0 hx (by simp [hpPos])
  have hsecond := addT0ToXStep_cleanEndpoint fieldTail counterWidth p hpPos hp
    control mutableY «λ» mutableX neg hx hneg
  simp only [negateXStep, negateXGates,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList
      (subtractXFromT0Gates fieldTail counterWidth p hp)
      (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩ mutableX neg by
    simpa [subtractXFromT0Step, neg] using hfirst]
  rw [show EncodedBit.GateSpec.stepList
      (addT0ToXGates fieldTail counterWidth p hp)
      (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩ mutableX neg) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩ 0 neg by
    simpa [addT0ToXStep, hsum] using hsecond]
  rw [RegisterRouting.swapXT0Gates_stepList]
  rfl

lemma subtractXFromT0_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (subtractXFromT0Gates fieldTail counterWidth p hp)) environment
      (subtractXFromT0Step fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma subtractT0FromX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (subtractT0FromXGates fieldTail counterWidth p hp)) environment
      (subtractT0FromXStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma addT0ToX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (addT0ToXGates fieldTail counterWidth p hp)) environment
      (addT0ToXStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma subtractConstantY_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (subtractConstantYGates fieldTail counterWidth p hp constant)) environment
      (subtractConstantYStep fieldTail counterWidth p hp constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma addConstantY_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (addConstantYGates fieldTail counterWidth p hp constant)) environment
      (addConstantYStep fieldTail counterWidth p hp constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma negateX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (negateXGates fieldTail counterWidth p hp)) environment
      (negateXStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

end
end ModularOperations
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
