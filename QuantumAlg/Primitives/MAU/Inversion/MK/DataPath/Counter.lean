/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule.ZeroTestValue
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.NumberTheory.Binary.GCD.FixedRound
import all QuantumAlg.Primitives.MAU.Inversion.MK.Layout

/-!
# Counter data path

This focused leaf is part of the exact fixed-round binary-GCD inversion
realization.  It is exported only through the canonical `MAU.Inversion.MK`
aggregate.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-- Padding-counter value bit lifted over the dedicated counter-increment work
object. -/
def liftedCounterIncrementCounterBit
    (n counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (registersWithCounterIncrementWorkEncoding n counterWidth) :=
  liftRegisterBitToCounterIncrementWork n counterWidth
    (RegisterBits.counterBit n counterWidth
      (WireAddress.littleEndianWire bit))

/-- Padding-counter value word lifted over the dedicated counter-increment
work object. -/
def liftedCounterIncrementCounterWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCounterIncrementWorkEncoding n counterWidth)
      counterWidth where
  bit := liftedCounterIncrementCounterBit n counterWidth

/-- Getter normalization for the lifted counter-increment source word. -/
lemma liftedCounterIncrementSourceWord_get_testBit
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    ((liftedCounterIncrementSourceWord n counterWidth).bit bit).get x =
      x.2.1.val.testBit bit.val := by
  simp [liftedCounterIncrementSourceWord, liftedCounterIncrementSourceBit,
    counterIncrementSourceBit, liftCounterIncrementWorkBit,
    counterIncrementWorkEncoding, wordEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    WireAddress.bitIndex_littleEndianWire]

/-- Getter normalization for the lifted padding-counter value word. -/
lemma liftedCounterIncrementCounterWord_get_testBit
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    ((liftedCounterIncrementCounterWord n counterWidth).bit bit).get x =
      x.1.counter.val.testBit bit.val := by
  change
    (RegisterBits.counterBit n counterWidth
      (WireAddress.littleEndianWire bit)).get x.1 =
      x.1.counter.val.testBit bit.val
  simp [WireAddress.bitIndex_littleEndianWire]

/-- Getter normalization for the lifted counter-increment carry-in flag. -/
lemma liftedCounterIncrementCarryInBit_get
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (liftedCounterIncrementCarryInBit n counterWidth).get x =
      x.2.2.1 := by
  change (counterIncrementCarryInBit counterWidth).get x.2 = x.2.2.1
  change BinaryLabelEncoding.boolBit.get x.2.2.1 = x.2.2.1
  rfl

/-- The lifted counter-increment carry-work bits read false on clean work. -/
lemma liftedCounterIncrementCarryWorkBit_get_clean
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1))
    (x : Registers n counterWidth) :
    (liftedCounterIncrementCarryWorkBit n counterWidth bit).get
        (x, cleanCounterIncrementWork counterWidth) = false := by
  change
    (counterIncrementCarryWorkBit counterWidth bit).get
      (cleanCounterIncrementWork counterWidth) = false
  change
    (BinaryLabelEncoding.finIdentityBit (counterWidth - 1) bit).get
      (PlainAdder.Schedule.PowerOfTwo.cleanCarryWork counterWidth) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero
    (counterWidth - 1) bit

/-- Carry-work layout for incrementing the padding counter with a dedicated
source-one word and clean carry-work object. -/
def counterIncrementLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := registersWithCounterIncrementWorkEncoding n counterWidth)
      counterWidth where
  left := liftedCounterIncrementSourceWord n counterWidth
  right := liftedCounterIncrementCounterWord n counterWidth
  carryIn := liftedCounterIncrementCarryInBit n counterWidth
  workCarry := liftedCounterIncrementCarryWorkWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact liftCounterIncrementWorkBit_liftCounterIncrementWorkBit_wire_ne
      n counterWidth (counterIncrementSourceBit counterWidth i)
      (counterIncrementSourceBit counterWidth j)
      (counterIncrementSource_source_wire_ne counterWidth i j hij)
  rightRight_ne := by
    intro i j hij
    exact liftRegisterBit_counterIncrement_liftRegisterBit_wire_ne
      n counterWidth
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire i))
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire j))
      (counterValue_counterValue_wire_ne n counterWidth i j hij)
  leftRight_ne := by
    intro i j
    exact Ne.symm
      (liftRegisterBit_liftCounterIncrementWorkBit_wire_ne n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire j))
        (counterIncrementSourceBit counterWidth i))
  leftCarryIn_ne := by
    intro i
    exact liftCounterIncrementWorkBit_liftCounterIncrementWorkBit_wire_ne
      n counterWidth (counterIncrementSourceBit counterWidth i)
      (counterIncrementCarryInBit counterWidth)
      (counterIncrementSource_carryIn_wire_ne counterWidth i)
  rightCarryIn_ne := by
    intro i
    exact liftRegisterBit_liftCounterIncrementWorkBit_wire_ne
      n counterWidth
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire i))
      (counterIncrementCarryInBit counterWidth)
  leftWork_ne := by
    intro i j
    exact liftCounterIncrementWorkBit_liftCounterIncrementWorkBit_wire_ne
      n counterWidth (counterIncrementSourceBit counterWidth i)
      (counterIncrementCarryWorkBit counterWidth j)
      (counterIncrementSource_carryWork_wire_ne counterWidth i j)
  rightWork_ne := by
    intro i j
    exact liftRegisterBit_liftCounterIncrementWorkBit_wire_ne
      n counterWidth
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire i))
      (counterIncrementCarryWorkBit counterWidth j)
  carryInWork_ne := by
    intro j
    exact liftCounterIncrementWorkBit_liftCounterIncrementWorkBit_wire_ne
      n counterWidth (counterIncrementCarryInBit counterWidth)
      (counterIncrementCarryWorkBit counterWidth j)
      (counterIncrementCarryIn_carryWork_wire_ne counterWidth j)
  workWork_ne := by
    intro i j hij
    exact liftCounterIncrementWorkBit_liftCounterIncrementWorkBit_wire_ne
      n counterWidth (counterIncrementCarryWorkBit counterWidth i)
      (counterIncrementCarryWorkBit counterWidth j)
      (counterIncrementCarryWork_carryWork_wire_ne counterWidth i j hij)

/-- Folded carry/sum/cleanup gate list for the padding-counter incrementer. -/
def counterIncrementWithWorkGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCounterIncrementWorkEncoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (counterIncrementLayout n counterWidth)

/-- Base-gate program for the padding-counter incrementer with work. -/
def counterIncrementWithWorkProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCounterIncrementWorkEncoding n counterWidth).width).toQuantum :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram
    (counterIncrementLayout n counterWidth)

/-- Folded semantic action for the padding-counter incrementer with work. -/
def counterIncrementWithWorkStep (n counterWidth : Nat) :
    RegistersWithCounterIncrementWork n counterWidth ->
      RegistersWithCounterIncrementWork n counterWidth :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
    (counterIncrementLayout n counterWidth)

/-- The padding-counter incrementer realizes its folded bit-lens action with
the same base-gate object used for resource accounting. -/
lemma counterIncrementWithWork_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCounterIncrementWorkEncoding n counterWidth)
      (counterIncrementWithWorkProgram n counterWidth) environment
      (counterIncrementWithWorkStep n counterWidth) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes
    (counterIncrementLayout n counterWidth)

/-- The counter-increment schedule preserves any Kaliski-register readout
whose wire is disjoint from every padding-counter target bit. -/
lemma counterIncrementWithWorkStep_get_registerBit_of_counter_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hright :
      ∀ i : Fin counterWidth,
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire i)).wire ≠ observed.wire)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    observed.get (counterIncrementWithWorkStep n counterWidth x).1 =
      observed.get x.1 := by
  let liftedObserved :=
    liftRegisterBitToCounterIncrementWork n counterWidth observed
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (counterIncrementLayout n counterWidth) liftedObserved
      (fun i =>
        liftRegisterBit_counterIncrement_liftRegisterBit_wire_ne
          n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire i))
          observed (hright i))
      (fun j =>
        Ne.symm
          (liftRegisterBit_liftCounterIncrementWorkBit_wire_ne
            n counterWidth observed
            (counterIncrementCarryWorkBit counterWidth j)))
      x
  change liftedObserved.get (counterIncrementWithWorkStep n counterWidth x) =
    liftedObserved.get x
  simpa [counterIncrementWithWorkStep, counterIncrementLayout,
    liftedObserved, liftRegisterBitToCounterIncrementWork,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The counter-increment schedule preserves the `u` word. -/
lemma counterIncrementWithWorkStep_u
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.u = x.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.uValueBit n counterWidth bit)
      (fun i =>
        Ne.symm
          (RegisterBits.u_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire i)))
      x
  simpa using h

/-- The counter-increment schedule preserves the `v` word. -/
lemma counterIncrementWithWorkStep_v
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.v = x.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.vValueBit n counterWidth bit)
      (fun i =>
        Ne.symm
          (RegisterBits.v_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire i)))
      x
  simpa using h

/-- The counter-increment schedule preserves the `s` coefficient word. -/
lemma counterIncrementWithWorkStep_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.sCoeff =
      x.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.sCoeffValueBit n counterWidth bit)
      (fun i =>
        Ne.symm
          (RegisterBits.sCoeff_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire i)))
      x
  simpa using h

/-- The counter-increment schedule preserves the `r` coefficient word. -/
lemma counterIncrementWithWorkStep_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.rCoeff =
      x.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.rCoeffValueBit n counterWidth bit)
      (fun i =>
        Ne.symm
          (RegisterBits.rCoeff_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire i)))
      x
  simpa using h

/-- The counter-increment schedule preserves the comparison ancilla. -/
lemma counterIncrementWithWorkStep_compare
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.compare =
      x.1.compare := by
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.compareBit n counterWidth)
      (fun i =>
        Ne.symm
          (RegisterBits.compare_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
      x
  simpa [RegisterBits.compareBit_get] using h

/-- The counter-increment schedule preserves the first scratch bit. -/
lemma counterIncrementWithWorkStep_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.scratchA =
      x.1.scratchA := by
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.scratchABit n counterWidth)
      (fun i =>
        Ne.symm
          (RegisterBits.scratchA_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
      x
  simpa [RegisterBits.scratchABit_get] using h

/-- The counter-increment schedule preserves the second scratch bit. -/
lemma counterIncrementWithWorkStep_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.scratchB =
      x.1.scratchB := by
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.scratchBBit n counterWidth)
      (fun i =>
        Ne.symm
          (RegisterBits.scratchB_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
      x
  simpa [RegisterBits.scratchBBit_get] using h

/-- The counter-increment schedule preserves every stored history bit. -/
lemma counterIncrementWithWorkStep_history
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.history =
      x.1.history := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth
      (RegisterBits.historyBit n counterWidth
        (WireAddress.littleEndianWire bit))
      (fun i =>
        Ne.symm
          (RegisterBits.history_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire i)))
      x
  simpa [RegisterBits.historyBit_get] using h

/-- The counter-increment schedule preserves the active flag. -/
lemma counterIncrementWithWorkStep_active
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).1.active =
      x.1.active := by
  have h :=
    counterIncrementWithWorkStep_get_registerBit_of_counter_ne
      n counterWidth (RegisterBits.activeBit n counterWidth)
      (fun i =>
        Ne.symm
          (RegisterBits.active_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
      x
  simpa [RegisterBits.activeBit_get] using h

/-- The counter-increment schedule preserves the dedicated source-one work
word. -/
lemma counterIncrementWithWorkStep_get_source
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).2.1 = x.2.1 := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (counterIncrementLayout n counterWidth) bit x
  simpa [counterIncrementWithWorkStep, counterIncrementLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    liftedCounterIncrementSourceWord_get_testBit] using h

/-- The counter-increment schedule preserves the dedicated carry-in flag. -/
lemma counterIncrementWithWorkStep_get_carryIn
    (n counterWidth : Nat)
    (x : RegistersWithCounterIncrementWork n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth x).2.2.1 = x.2.2.1 := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (counterIncrementLayout n counterWidth) x
  simpa [counterIncrementWithWorkStep, counterIncrementLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    liftedCounterIncrementCarryInBit_get] using h

/-- On clean counter-increment work inputs, the forward carry stage computes
the propagated natural addition carry for `source + counter`. -/
lemma counterIncrement_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat) (j : Fin (counterWidth - 1))
    (x : RegistersWithCounterIncrementWork n counterWidth)
    (hcarry : (liftedCounterIncrementCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (counterWidth - 1),
        ((liftedCounterIncrementCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCounterIncrementCarryWorkWord n counterWidth).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (counterIncrementLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.2.1.val x.1.counter.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (counterIncrementLayout n counterWidth) x
  change
    ((liftedCounterIncrementCarryWorkWord n counterWidth).bit j).get stage =
      Nat.BinaryArithmetic.natAddCarry
        x.2.1.val x.1.counter.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin (counterWidth - 1), j.val = m ->
      ((liftedCounterIncrementCarryWorkWord n counterWidth).bit j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          x.2.1.val x.1.counter.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (counterIncrementLayout n counterWidth) j x hwork
        change
          ((liftedCounterIncrementCarryWorkWord n counterWidth).bit j).get
              stage =
            Nat.BinaryArithmetic.natAddCarry
              x.2.1.val x.1.counter.val (j.val + 1)
        change
          ((counterIncrementLayout n counterWidth).workCarry.bit j).get
              ((counterIncrementLayout n counterWidth).carryStageIndexStep x) =
            Nat.BinaryArithmetic.natAddCarry
              x.2.1.val x.1.counter.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (counterIncrementLayout n counterWidth) x
          rw [hdata]
          have hcarryData : x.2.2.1 = false := by
            simpa [liftedCounterIncrementCarryInBit_get] using hcarry
          simp [counterIncrementLayout,
            liftedCounterIncrementSourceWord_get_testBit,
            liftedCounterIncrementCounterWord_get_testBit,
            liftedCounterIncrementCarryInBit_get, hcarryData,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpRec' :
              ((counterIncrementLayout n counterWidth).workCarry.bit p).get
                  ((counterIncrementLayout n counterWidth).carryStageIndexStep
                    x) =
                Nat.BinaryArithmetic.natAddCarry
                  x.2.1.val x.1.counter.val (p.val + 1) := by
            simpa [stage, counterIncrementLayout] using hpRec
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hpRec', hpSucc]
          simp [counterIncrementLayout,
            liftedCounterIncrementSourceWord_get_testBit,
            liftedCounterIncrementCounterWord_get_testBit,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before each counter target sum is the propagated natural
carry for `source + counter` on clean carry/work inputs. -/
lemma counterIncrement_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : RegistersWithCounterIncrementWork n counterWidth)
    (hcarry : (liftedCounterIncrementCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (counterWidth - 1),
        ((liftedCounterIncrementCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (counterIncrementLayout n counterWidth) bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (counterIncrementLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.2.1.val x.1.counter.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (counterIncrementLayout n counterWidth) x
    rw [hdata]
    have hcarryData : x.2.2.1 = false := by
      simpa [liftedCounterIncrementCarryInBit_get] using hcarry
    simp [counterIncrementLayout, liftedCounterIncrementCarryInBit_get,
      hcarryData, Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : bit.val - 1 < counterWidth - 1 := by
      have hbit := bit.isLt
      omega
    let j : Fin (counterWidth - 1) := ⟨bit.val - 1, hjLt⟩
    have hworkCarry :=
      counterIncrement_carryStage_get_workCarry_natAddCarry
        n counterWidth j x hcarry hwork
    have hjSucc : j.val + 1 = bit.val := by
      dsimp [j]
      omega
    change
      ((liftedCounterIncrementCarryWorkWord n counterWidth).bit j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (counterIncrementLayout n counterWidth) x) =
        Nat.BinaryArithmetic.natAddCarry
          x.2.1.val x.1.counter.val bit.val
    rw [hworkCarry, hjSucc]

/-- On clean counter-increment work inputs, each counter target bit is written
as `counter + 1`. -/
lemma counterIncrementWithWorkStep_get_counter_add_testBit_of_clean
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : Registers n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth
        (x, cleanCounterIncrementWork counterWidth)).1.counter.val.testBit
        bit.val =
      (x.counter + (1 : Word counterWidth)).val.testBit bit.val := by
  let input : RegistersWithCounterIncrementWork n counterWidth :=
    (x, cleanCounterIncrementWork counterWidth)
  have hright :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (counterIncrementLayout n counterWidth) bit input
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hright
  have hcarry :
      (liftedCounterIncrementCarryInBit n counterWidth).get input = false := by
    simp [input, liftedCounterIncrementCarryInBit_get,
      cleanCounterIncrementWork]
  have hwork :
      ∀ k : Fin (counterWidth - 1),
        ((liftedCounterIncrementCarryWorkWord n counterWidth).bit k).get
          input = false := by
    intro k
    exact liftedCounterIncrementCarryWorkBit_get_clean n counterWidth k x
  have hcarryBit :=
    counterIncrement_carryBeforeSum_get_natAddCarry
      n counterWidth bit input hcarry hwork
  rw [hcarryBit] at hright
  calc
    (counterIncrementWithWorkStep n counterWidth
        (x, cleanCounterIncrementWork counterWidth)).1.counter.val.testBit
        bit.val =
        (((x.counter.val.testBit bit.val ^^
              (1 : Word counterWidth).val.testBit bit.val) ^^
            Nat.BinaryArithmetic.natAddCarry
              (1 : Word counterWidth).val x.counter.val bit.val)) := by
      simpa [input, counterIncrementWithWorkStep, counterIncrementLayout,
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        liftedCounterIncrementCounterWord_get_testBit,
        liftedCounterIncrementSourceWord_get_testBit,
        cleanCounterIncrementWork, Bool.xor_assoc] using hright
    _ = (x.counter + (1 : Word counterWidth)).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using
        (word_add_testBit_eq_xor3 counterWidth
          (1 : Word counterWidth) x.counter bit).symm

/-- On clean counter-increment work inputs, the counter field is incremented
modulo its width. -/
lemma counterIncrementWithWorkStep_counter_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth
        (x, cleanCounterIncrementWork counterWidth)).1.counter =
      wordIncrement counterWidth x.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [counterIncrementWithWorkStep_get_counter_add_testBit_of_clean]
  rw [word_add_one_eq_wordIncrement]

/-- On clean counter-increment work inputs, each temporary carry-work bit is
restored to false. -/
lemma counterIncrementWithWorkStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1))
    (x : Registers n counterWidth) :
    ((liftedCounterIncrementCarryWorkWord n counterWidth).bit bit).get
        (counterIncrementWithWorkStep n counterWidth
          (x, cleanCounterIncrementWork counterWidth)) = false := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (counterIncrementLayout n counterWidth) bit
      (x, cleanCounterIncrementWork counterWidth)
      (by
        intro k
        exact liftedCounterIncrementCarryWorkBit_get_clean
          n counterWidth k x)
  simpa [counterIncrementWithWorkStep, counterIncrementLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- On clean inputs, the dedicated counter-increment work object is restored. -/
lemma counterIncrementWithWorkStep_work_cleanEndpoint
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth
        (x, cleanCounterIncrementWork counterWidth)).2 =
      cleanCounterIncrementWork counterWidth := by
  apply Prod.ext
  · exact counterIncrementWithWorkStep_get_source n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  · apply Prod.ext
    · rw [counterIncrementWithWorkStep_get_carryIn]
    · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
      intro bit
      change
        ((liftedCounterIncrementCarryWorkWord n counterWidth).bit bit).get
          (counterIncrementWithWorkStep n counterWidth
            (x, cleanCounterIncrementWork counterWidth)) = false
      exact counterIncrementWithWorkStep_get_carryWork_clean
        n counterWidth bit x

/-- On clean inputs, the register endpoint is the original Kaliski register
with only the padding counter incremented. -/
lemma counterIncrementWithWorkStep_register_cleanEndpoint
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (counterIncrementWithWorkStep n counterWidth
        (x, cleanCounterIncrementWork counterWidth)).1 =
      { x with counter := wordIncrement counterWidth x.counter } := by
  let y :=
    (counterIncrementWithWorkStep n counterWidth
      (x, cleanCounterIncrementWork counterWidth)).1
  have hu : y.u = x.u :=
    counterIncrementWithWorkStep_u n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hv : y.v = x.v :=
    counterIncrementWithWorkStep_v n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hcompare : y.compare = x.compare :=
    counterIncrementWithWorkStep_compare n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hs : y.sCoeff = x.sCoeff :=
    counterIncrementWithWorkStep_sCoeff n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hr : y.rCoeff = x.rCoeff :=
    counterIncrementWithWorkStep_rCoeff n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hscratchA : y.scratchA = x.scratchA :=
    counterIncrementWithWorkStep_scratchA n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hscratchB : y.scratchB = x.scratchB :=
    counterIncrementWithWorkStep_scratchB n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hhistory : y.history = x.history :=
    counterIncrementWithWorkStep_history n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hactive : y.active = x.active :=
    counterIncrementWithWorkStep_active n counterWidth
      (x, cleanCounterIncrementWork counterWidth)
  have hcounter : y.counter = wordIncrement counterWidth x.counter :=
    counterIncrementWithWorkStep_counter_of_clean n counterWidth x
  change y = { x with counter := wordIncrement counterWidth x.counter }
  clear_value y
  rcases y with
    ⟨yu, yv, ycompare, ysCoeff, yrCoeff, yscratchA, yscratchB,
      yhistory, yactive, ycounter⟩
  rcases x with
    ⟨xu, xv, xcompare, xsCoeff, xrCoeff, xscratchA, xscratchB,
      xhistory, xactive, xcounter⟩
  simp at hu hv hcompare hs hr hscratchA hscratchB hhistory hactive hcounter
  simp [hu, hv, hcompare, hs, hr, hscratchA, hscratchB, hhistory, hactive,
    hcounter]

/-- Clean endpoint for the padding-counter incrementer with dedicated work. -/
lemma counterIncrementWithWorkStep_cleanEndpoint
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    counterIncrementWithWorkStep n counterWidth
        (x, cleanCounterIncrementWork counterWidth) =
      ({ x with counter := wordIncrement counterWidth x.counter },
        cleanCounterIncrementWork counterWidth) := by
  exact Prod.ext
    (counterIncrementWithWorkStep_register_cleanEndpoint n counterWidth x)
    (counterIncrementWithWorkStep_work_cleanEndpoint n counterWidth x)

/-- Distinct comparison-work carry bits occupy distinct wires. -/
lemma comparisonCarry_comparisonCarry_wire_ne
    (n : Nat) (left right : Fin n) (h : left ≠ right) :
    (comparisonCarryBit n left).wire ≠
      (comparisonCarryBit n right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [comparisonCarryBit, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
    using hval

/-- Distinct little-endian comparison-work value bits occupy distinct wires. -/
lemma comparisonCarryValue_comparisonCarryValue_wire_ne
    (n : Nat) (left right : Fin n) (h : left ≠ right) :
    (comparisonCarryValueBit n left).wire ≠
      (comparisonCarryValueBit n right).wire := by
  exact comparisonCarry_comparisonCarry_wire_ne n
    (WireAddress.littleEndianWire left)
    (WireAddress.littleEndianWire right)
    (littleEndianWire_ne h)

/-- `u` word lifted to the product register that carries comparison work. -/
def liftedUWord (n counterWidth : Nat) :
    EncodedBit.Word (registersWithComparisonWorkEncoding n counterWidth) n where
  bit := fun bit =>
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.uValueBit n counterWidth bit)

/-- A selected `u` register bit lifted over comparison work. -/
def liftedUBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftRegisterBitToComparisonWork n counterWidth
    (RegisterBits.uBit n counterWidth bit)

/-- `v` word lifted to the product register that carries comparison work. -/
def liftedVWord (n counterWidth : Nat) :
    EncodedBit.Word (registersWithComparisonWorkEncoding n counterWidth) n where
  bit := fun bit =>
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.vValueBit n counterWidth bit)

/-- A selected `v` register bit lifted over comparison work. -/
def liftedVBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftRegisterBitToComparisonWork n counterWidth
    (RegisterBits.vBit n counterWidth bit)

/-- `s` coefficient word lifted to the product register that carries
comparison work. -/
def liftedSCoeffWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithComparisonWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.sCoeffBit n counterWidth bit)

/-- `r` coefficient word lifted to the product register that carries
comparison work. -/
def liftedRCoeffWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithComparisonWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.rCoeffBit n counterWidth bit)

/-- Little-endian `s` coefficient value-word lifted to the product register
that carries comparison work. -/
def liftedSCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithComparisonWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.sCoeffValueBit n counterWidth bit)

/-- Little-endian `r` coefficient value-word lifted to the product register
that carries comparison work. -/
def liftedRCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithComparisonWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.rCoeffValueBit n counterWidth bit)

/-- Lifted comparison ancilla over the dedicated coefficient-adder work
object. -/
def coeffAdderCompareBit (n counterWidth : Nat) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedCompareBit n counterWidth)

/-- Lifted scratchA bit over the dedicated coefficient-adder work object. -/
def coeffAdderScratchABit (n counterWidth : Nat) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedScratchABit n counterWidth)

/-- Lifted scratchB bit over the dedicated coefficient-adder work object. -/
def coeffAdderScratchBBit (n counterWidth : Nat) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedScratchBBit n counterWidth)

/-- Lifted branch-history bit over the dedicated coefficient-adder work object. -/
def coeffAdderHistoryBit (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedHistoryBit n counterWidth bit)

/-- Lifted active flag over the dedicated coefficient-adder work object. -/
def coeffAdderActiveBit (n counterWidth : Nat) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedActiveBit n counterWidth)

/-- A little-endian padding-counter value bit lifted over comparison and
coefficient-adder work.  Active Kaliski data paths use this lens to state raw
counter preservation without passing through a semantic readout wrapper. -/
def coeffAdderCounterValueBit (n counterWidth : Nat)
    (bit : Fin counterWidth) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire bit)))

lemma coeffAdderCounterValueBit_get (n counterWidth : Nat)
    (bit : Fin counterWidth)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCounterValueBit n counterWidth bit).get x =
      x.1.1.counter.val.testBit bit.val := by
  change
    (RegisterBits.counterBit n counterWidth
      (WireAddress.littleEndianWire bit)).get x.1.1 = _
  rw [RegisterBits.counterBit_get,
    WireAddress.bitIndex_littleEndianWire]

lemma
    coeffAdderLiftedRegisterBit_counterValueBit_wire_ne
    (n counterWidth : Nat)
    (registerBit : EncodedBit (registerEncoding n counterWidth))
    (counterBit : Fin counterWidth)
    (hne : registerBit.wire ≠
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire counterBit)).wire) :
    (liftComparisonStateBitToCoeffAdderWork n counterWidth
      (liftRegisterBitToComparisonWork n counterWidth registerBit)).wire ≠
      (coeffAdderCounterValueBit n counterWidth counterBit).wire := by
  simpa [coeffAdderCounterValueBit] using
    liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth
      (liftRegisterBitToComparisonWork n counterWidth registerBit)
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire counterBit)))
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        registerBit
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire counterBit)) hne)

lemma
    liftedCoeffAdderCarryWorkBit_counterValueBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (counterBit : Fin counterWidth) :
    (liftedCoeffAdderCarryWorkBit n counterWidth workBit).wire ≠
      (coeffAdderCounterValueBit n counterWidth counterBit).wire := by
  simpa [liftedCoeffAdderCarryWorkBit, coeffAdderCounterValueBit] using
    Ne.symm (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire counterBit)))
      (coeffAdderCarryWorkBit n workBit))

/-- Active flag lifted to the extended full-round path workspace. -/
def fullRoundPathWorkActiveBit (tail counterWidth : Nat) :
    EncodedBit
      (registersWithFullRoundPathWorkEncoding tail.succ counterWidth) :=
  liftFullRoundWorkBitToPathWork tail counterWidth
    (liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderActiveBit tail.succ counterWidth))

/-- Active flag lifted to the full-round path/control-work workspace. -/
def fullRoundPathControlWorkActiveBit (tail counterWidth : Nat) :
    EncodedBit
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth) :=
  liftFullRoundPathWorkBitToControlWork tail counterWidth
    (fullRoundPathWorkActiveBit tail counterWidth)

/-- The lifted active flag and trailing path bit occupy distinct wires. -/
lemma fullRoundPathWorkActiveBit_wire_ne_pathBit
    (tail counterWidth : Nat) :
    (fullRoundPathWorkActiveBit tail counterWidth).wire ≠
      (fullRoundPathWorkPathBit tail counterWidth).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  simp [fullRoundPathWorkActiveBit, fullRoundPathWorkPathBit,
    liftFullRoundWorkBitToPathWork, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hval
  have hlt :
      (liftCoeffAdderStateBitToFullRoundWork tail counterWidth
        (coeffAdderActiveBit tail.succ counterWidth)).wire.val <
        (registersWithFullRoundWorkEncoding tail.succ counterWidth).width :=
    (liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderActiveBit tail.succ counterWidth)).wire.isLt
  omega

/-- Single CNOT that latches the current active flag into the trailing path bit.
The caller is responsible for starting the path bit at `false`. -/
def fullRoundPathWorkOriginalActiveLatchGate
    (tail counterWidth : Nat) :
    EncodedBit.GateSpec
      (registersWithFullRoundPathWorkEncoding tail.succ counterWidth) :=
  EncodedBit.GateSpec.cnot
    (fullRoundPathWorkActiveBit tail counterWidth)
    (fullRoundPathWorkPathBit tail counterWidth)
    (fullRoundPathWorkActiveBit_wire_ne_pathBit tail counterWidth)

/-- Gate list for the original-active path latch. -/
def fullRoundPathWorkOriginalActiveLatchGates
    (tail counterWidth : Nat) :
    List
      (EncodedBit.GateSpec
        (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)) :=
  [fullRoundPathWorkOriginalActiveLatchGate tail counterWidth]

/-- Semantic step for latching the current active flag into the path bit. -/
def fullRoundPathWorkOriginalActiveLatchStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundPathWork tail.succ counterWidth ->
      RegistersWithFullRoundPathWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundPathWorkOriginalActiveLatchGates tail counterWidth)

/-- Actual circuit for the original-active path latch. -/
def fullRoundPathWorkOriginalActiveLatchProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundPathWorkEncoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundPathWorkOriginalActiveLatchGates tail counterWidth)

/-- The path-latch circuit realizes its gate-list step. -/
lemma fullRoundPathWorkOriginalActiveLatch_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
      (fullRoundPathWorkOriginalActiveLatchProgram tail counterWidth) environment
      (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (fullRoundPathWorkOriginalActiveLatchGates tail counterWidth)

/-- With a clean path bit, the latch stores the current active flag. -/
lemma fullRoundPathWorkOriginalActiveLatchStep_path_of_clean
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundPathWork tail.succ counterWidth)
    (hclean : (fullRoundPathWorkPathBit tail counterWidth).get x = false) :
    (fullRoundPathWorkPathBit tail counterWidth).get
        (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth x) =
      (fullRoundPathWorkActiveBit tail counterWidth).get x := by
  simp [fullRoundPathWorkOriginalActiveLatchStep,
    fullRoundPathWorkOriginalActiveLatchGates,
    fullRoundPathWorkOriginalActiveLatchGate,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.cnotStep_get_target, hclean]

/-- Original-active latch lifted over the path/control-work layout. -/
def fullRoundPathControlWorkOriginalActiveLatchStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  liftFullRoundPathWorkStepToControlWork tail.succ counterWidth
    (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth)

/-- Actual original-active latch circuit in the path/control workspace. -/
def fullRoundPathControlWorkOriginalActiveLatchProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundPathControlWorkEncoding
          tail.succ counterWidth).width).toQuantum :=
  liftFullRoundPathWorkProgramToControlWork tail.succ counterWidth
    (fullRoundPathWorkOriginalActiveLatchProgram tail counterWidth)

/-- The lifted original-active latch realizes the lifted semantic step. -/
lemma fullRoundPathControlWorkOriginalActiveLatch_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth)
      (fullRoundPathControlWorkOriginalActiveLatchProgram tail counterWidth) environment
      (fullRoundPathControlWorkOriginalActiveLatchStep tail counterWidth) :=
  liftFullRoundPathWorkProgramToControlWork_realizes tail.succ counterWidth
    (fullRoundPathWorkOriginalActiveLatch_realizes tail counterWidth)

/-- The lifted original-active latch preserves the control-work bit. -/
lemma fullRoundPathControlWorkOriginalActiveLatchStep_controlWork
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth) :
    (fullRoundPathControlWorkOriginalActiveLatchStep
      tail counterWidth x).2 = x.2 := by
  rfl

/-- The lifted original-active latch records source active in the path bit when
the path bit starts clean. -/
lemma fullRoundPathControlWorkOriginalActiveLatchStep_path_of_clean
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth)
    (hclean :
      (fullRoundPathControlWorkPathBit tail counterWidth).get x = false) :
    (fullRoundPathControlWorkPathBit tail counterWidth).get
        (fullRoundPathControlWorkOriginalActiveLatchStep tail counterWidth x) =
      (fullRoundPathControlWorkActiveBit tail counterWidth).get x := by
  change
    (fullRoundPathWorkPathBit tail counterWidth).get
        (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth x.1) =
      (fullRoundPathWorkActiveBit tail counterWidth).get x.1
  exact
    fullRoundPathWorkOriginalActiveLatchStep_path_of_clean
      tail counterWidth x.1 hclean

/-- If source active is false, the original-active latch is a no-op. -/
lemma fullRoundPathControlWorkOriginalActiveLatchStep_eq_self_of_active_false
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth)
    (hactive :
      (fullRoundPathControlWorkActiveBit tail counterWidth).get x = false) :
    fullRoundPathControlWorkOriginalActiveLatchStep tail counterWidth x =
      x := by
  have hactivePath :
      (fullRoundPathWorkActiveBit tail counterWidth).get x.1 = false := by
    simpa [fullRoundPathControlWorkActiveBit,
      liftFullRoundPathWorkBitToControlWork,
      BinaryLabelEncoding.prodLeftBit] using hactive
  unfold fullRoundPathControlWorkOriginalActiveLatchStep
    liftFullRoundPathWorkStepToControlWork
    fullRoundPathWorkOriginalActiveLatchStep
  simp only [fullRoundPathWorkOriginalActiveLatchGates,
    fullRoundPathWorkOriginalActiveLatchGate,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step]
  unfold EncodedBit.cnotStep
  simp [hactivePath]

/-- Selected `u` register bit lifted over the dedicated coefficient-adder work
object. -/
def coeffAdderUBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedUBit n counterWidth bit)

/-- Selected `v` register bit lifted over the dedicated coefficient-adder work
object. -/
def coeffAdderVBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedVBit n counterWidth bit)

/-- Lifted `u` value word over the dedicated coefficient-adder work object. -/
def coeffAdderUWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) n where
  bit := fun bit =>
    liftComparisonStateBitToCoeffAdderWork n counterWidth
      ((liftedUWord n counterWidth).bit bit)

/-- Lifted `v` value word over the dedicated coefficient-adder work object. -/
def coeffAdderVWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) n where
  bit := fun bit =>
    liftComparisonStateBitToCoeffAdderWork n counterWidth
      ((liftedVWord n counterWidth).bit bit)

/-- Lifted `s` coefficient word over the dedicated coefficient-adder work
object. -/
def coeffAdderSCoeffWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftComparisonStateBitToCoeffAdderWork n counterWidth
      ((liftedSCoeffWord n counterWidth).bit bit)

/-- Lifted `r` coefficient word over the dedicated coefficient-adder work
object. -/
def coeffAdderRCoeffWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftComparisonStateBitToCoeffAdderWork n counterWidth
      ((liftedRCoeffWord n counterWidth).bit bit)

/-- Lifted little-endian `s` coefficient value-word over the dedicated
coefficient-adder work object. -/
def coeffAdderSCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftComparisonStateBitToCoeffAdderWork n counterWidth
      ((liftedSCoeffValueWord n counterWidth).bit bit)

/-- Lifted little-endian `r` coefficient value-word over the dedicated
coefficient-adder work object. -/
def coeffAdderRCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) (n + 1) where
  bit := fun bit =>
    liftComparisonStateBitToCoeffAdderWork n counterWidth
      ((liftedRCoeffValueWord n counterWidth).bit bit)

/-- Getter normalization for the lifted `u` value word. -/
lemma coeffAdderUWord_get_testBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get x =
      x.1.1.u.val.testBit bit.val := by
  simp [coeffAdderUWord, liftedUWord,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit]

/-- Getter normalization for the lifted `v` value word. -/
lemma coeffAdderVWord_get_testBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get x =
      x.1.1.v.val.testBit bit.val := by
  simp [coeffAdderVWord, liftedVWord,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit]

/-- Getter normalization for the lifted comparison bit over the dedicated
coefficient-adder work object. -/
lemma coeffAdderCompareBit_get
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get x = x.1.1.compare := by
  simp [coeffAdderCompareBit, liftedCompareBit,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit]

/-- The little-endian zero `u` wire over coefficient-adder work reads the
low value bit of the concrete `u` register. -/
lemma coeffAdderUBit_get_littleEndian_zero
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x =
      x.1.1.u.val.testBit (0 : Nat) := by
  simpa [coeffAdderUBit, liftedUBit, RegisterBits.uValueBit,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using
      (RegisterBits.uValueBit_get tail.succ counterWidth
        (0 : Fin tail.succ) x.1.1)

/-- The little-endian zero `v` wire over coefficient-adder work reads the
low value bit of the concrete `v` register. -/
lemma coeffAdderVBit_get_littleEndian_zero
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x =
      x.1.1.v.val.testBit (0 : Nat) := by
  simpa [coeffAdderVBit, liftedVBit, RegisterBits.vValueBit,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using
      (RegisterBits.vValueBit_get tail.succ counterWidth
        (0 : Fin tail.succ) x.1.1)

/-- Getter normalization for the lifted little-endian `s` coefficient value
word. -/
lemma coeffAdderSCoeffValueWord_get_testBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x =
      x.1.1.sCoeff.val.testBit bit.val := by
  simp [coeffAdderSCoeffValueWord, liftedSCoeffValueWord,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit]

/-- Getter normalization for the lifted little-endian `r` coefficient value
word. -/
lemma coeffAdderRCoeffValueWord_get_testBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x =
      x.1.1.rCoeff.val.testBit bit.val := by
  simp [coeffAdderRCoeffValueWord, liftedRCoeffValueWord,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit]

/-- Comparison-work borrow/carry word lifted to the full comparison-work state. -/
def liftedComparisonCarryWord (n counterWidth : Nat) :
    EncodedBit.Word (registersWithComparisonWorkEncoding n counterWidth) n where
  bit := liftedComparisonCarryBit n counterWidth

/-- Lifted comparison-work carry bit over the dedicated coefficient-adder work
object. -/
def coeffAdderComparisonCarryBit
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftComparisonStateBitToCoeffAdderWork n counterWidth
    (liftedComparisonCarryBit n counterWidth bit)

lemma
    coeffAdderComparisonCarryBit_counterValueBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n)
    (counterBit : Fin counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).wire ≠
      (coeffAdderCounterValueBit n counterWidth counterBit).wire := by
  simpa [coeffAdderComparisonCarryBit, coeffAdderCounterValueBit,
    liftedComparisonCarryBit] using
    liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth
      (liftComparisonWorkBit n counterWidth
        (comparisonCarryValueBit n workBit))
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire counterBit)))
      (Ne.symm (liftRegisterBit_liftComparisonWorkBit_wire_ne
        n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire counterBit))
        (comparisonCarryValueBit n workBit)))

/-- Lifted comparison-work carry word over the dedicated coefficient-adder work
object. -/
def coeffAdderComparisonCarryWord (n counterWidth : Nat) :
    EncodedBit.Word (registersWithCoeffAdderWorkEncoding n counterWidth) n where
  bit := coeffAdderComparisonCarryBit n counterWidth

/-- Lifted comparison ancilla over the detector-plus-counter workspace. -/
def detectorCounterCompareBit (n counterWidth : Nat) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  liftComparisonStateBitToDetectorCounterWork n counterWidth
    (liftedCompareBit n counterWidth)

/-- Lifted active flag over the detector-plus-counter workspace. -/
def detectorCounterActiveBit (n counterWidth : Nat) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  liftComparisonStateBitToDetectorCounterWork n counterWidth
    (liftedActiveBit n counterWidth)

/-- Lifted comparison-work carry bit over the detector-plus-counter workspace. -/
def detectorCounterComparisonCarryBit
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  liftComparisonStateBitToDetectorCounterWork n counterWidth
    (liftedComparisonCarryBit n counterWidth bit)

/-- Padding-counter value bit lifted over the detector-plus-counter workspace. -/
def detectorCounterCounterBit
    (n counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  liftComparisonStateBitToDetectorCounterWork n counterWidth
    (liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire bit)))

/-- Padding-counter value word lifted over the detector-plus-counter workspace. -/
def detectorCounterCounterWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithDetectorCounterWorkEncoding n counterWidth)
      counterWidth where
  bit := detectorCounterCounterBit n counterWidth

/-- Source-one work word bit lifted over the detector-plus-counter workspace. -/
def detectorCounterIncrementSourceBit
    (n counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  liftCounterIncrementWorkBitToDetectorCounterWork n counterWidth
    (counterIncrementSourceBit counterWidth bit)

/-- Carry-in flag lifted over the detector-plus-counter workspace. -/
def detectorCounterIncrementCarryInBit (n counterWidth : Nat) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  liftCounterIncrementWorkBitToDetectorCounterWork n counterWidth
    (counterIncrementCarryInBit counterWidth)

/-- Counter-increment temporary carry-work bit lifted over the
detector-plus-counter workspace. -/
def detectorCounterIncrementCarryWorkBit
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  liftCounterIncrementWorkBitToDetectorCounterWork n counterWidth
    (counterIncrementCarryWorkBit counterWidth bit)

/-- Source-one work word lifted over the detector-plus-counter workspace. -/
def detectorCounterIncrementSourceWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithDetectorCounterWorkEncoding n counterWidth)
      counterWidth where
  bit := detectorCounterIncrementSourceBit n counterWidth

/-- Temporary carry-work word lifted over the detector-plus-counter workspace. -/
def detectorCounterIncrementCarryWorkWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithDetectorCounterWorkEncoding n counterWidth)
      (counterWidth - 1) where
  bit := detectorCounterIncrementCarryWorkBit n counterWidth

/-- Getter normalization for the detector-counter source-one work word. -/
lemma detectorCounterIncrementSourceWord_get_testBit
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    ((detectorCounterIncrementSourceWord n counterWidth).bit bit).get x =
      x.2.1.val.testBit bit.val := by
  simp [detectorCounterIncrementSourceWord, detectorCounterIncrementSourceBit,
    liftCounterIncrementWorkBitToDetectorCounterWork,
    counterIncrementSourceBit, counterIncrementWorkEncoding, wordEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    WireAddress.bitIndex_littleEndianWire]

/-- Getter normalization for the detector-counter padding-counter word. -/
lemma detectorCounterCounterWord_get_testBit
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    ((detectorCounterCounterWord n counterWidth).bit bit).get x =
      x.1.1.counter.val.testBit bit.val := by
  change
    (RegisterBits.counterBit n counterWidth
      (WireAddress.littleEndianWire bit)).get x.1.1 =
      x.1.1.counter.val.testBit bit.val
  simp [WireAddress.bitIndex_littleEndianWire]

/-- Getter normalization for the detector-counter carry-in flag. -/
lemma detectorCounterIncrementCarryInBit_get
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterIncrementCarryInBit n counterWidth).get x =
      x.2.2.1 := by
  change (counterIncrementCarryInBit counterWidth).get x.2 = x.2.2.1
  change BinaryLabelEncoding.boolBit.get x.2.2.1 = x.2.2.1
  rfl

/-- Detector-counter carry-work bits read false on clean counter-increment
work. -/
lemma detectorCounterIncrementCarryWorkBit_get_clean
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1))
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n) :
    (detectorCounterIncrementCarryWorkBit n counterWidth bit).get
        ((x, cmpWork), cleanCounterIncrementWork counterWidth) = false := by
  change
    (counterIncrementCarryWorkBit counterWidth bit).get
      (cleanCounterIncrementWork counterWidth) = false
  change
    (BinaryLabelEncoding.finIdentityBit (counterWidth - 1) bit).get
      (PlainAdder.Schedule.PowerOfTwo.cleanCarryWork counterWidth) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero
    (counterWidth - 1) bit

/-- Carry-work layout for incrementing the padding counter in the
detector-plus-counter workspace. -/
def detectorCounterIncrementLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := registersWithDetectorCounterWorkEncoding n counterWidth)
      counterWidth where
  left := detectorCounterIncrementSourceWord n counterWidth
  right := detectorCounterCounterWord n counterWidth
  carryIn := detectorCounterIncrementCarryInBit n counterWidth
  workCarry := detectorCounterIncrementCarryWorkWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact liftDetectorCounterWorkBit_liftDetectorCounterWorkBit_wire_ne
      n counterWidth (counterIncrementSourceBit counterWidth i)
      (counterIncrementSourceBit counterWidth j)
      (counterIncrementSource_source_wire_ne counterWidth i j hij)
  rightRight_ne := by
    intro i j hij
    exact liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
      n counterWidth
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire i)))
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire j)))
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire i))
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire j))
        (counterValue_counterValue_wire_ne n counterWidth i j hij))
  leftRight_ne := by
    intro i j
    exact Ne.symm
      (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
        n counterWidth
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire j)))
        (counterIncrementSourceBit counterWidth i))
  leftCarryIn_ne := by
    intro i
    exact liftDetectorCounterWorkBit_liftDetectorCounterWorkBit_wire_ne
      n counterWidth (counterIncrementSourceBit counterWidth i)
      (counterIncrementCarryInBit counterWidth)
      (counterIncrementSource_carryIn_wire_ne counterWidth i)
  rightCarryIn_ne := by
    intro i
    exact
      (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
        n counterWidth
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire i)))
        (counterIncrementCarryInBit counterWidth))
  leftWork_ne := by
    intro i j
    exact liftDetectorCounterWorkBit_liftDetectorCounterWorkBit_wire_ne
      n counterWidth (counterIncrementSourceBit counterWidth i)
      (counterIncrementCarryWorkBit counterWidth j)
      (counterIncrementSource_carryWork_wire_ne counterWidth i j)
  rightWork_ne := by
    intro i j
    exact
      (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
        n counterWidth
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire i)))
        (counterIncrementCarryWorkBit counterWidth j))
  carryInWork_ne := by
    intro j
    exact liftDetectorCounterWorkBit_liftDetectorCounterWorkBit_wire_ne
      n counterWidth (counterIncrementCarryInBit counterWidth)
      (counterIncrementCarryWorkBit counterWidth j)
      (counterIncrementCarryIn_carryWork_wire_ne counterWidth j)
  workWork_ne := by
    intro i j hij
    exact liftDetectorCounterWorkBit_liftDetectorCounterWorkBit_wire_ne
      n counterWidth (counterIncrementCarryWorkBit counterWidth i)
      (counterIncrementCarryWorkBit counterWidth j)
      (counterIncrementCarryWork_carryWork_wire_ne counterWidth i j hij)

/-- Gate list for inactive padding inside the detector-plus-counter workspace:
increment the padding counter with the dedicated clean counter-increment work
object. -/
def detectorCounterInactivePaddingGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithDetectorCounterWorkEncoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (detectorCounterIncrementLayout n counterWidth)

/-- Semantic action for the detector-plus-counter inactive padding gate list. -/
def detectorCounterInactivePaddingGateStep (n counterWidth : Nat) :
    RegistersWithDetectorCounterWork n counterWidth ->
      RegistersWithDetectorCounterWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (detectorCounterInactivePaddingGates n counterWidth)

/-- Actual detector-plus-counter inactive-padding circuit. -/
def detectorCounterInactivePaddingGateProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithDetectorCounterWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (detectorCounterInactivePaddingGates n counterWidth)

/-- The inactive-padding circuit realizes its gate-list action. -/
lemma detectorCounterInactivePaddingGate_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithDetectorCounterWorkEncoding n counterWidth)
      (detectorCounterInactivePaddingGateProgram n counterWidth) environment
      (detectorCounterInactivePaddingGateStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (detectorCounterInactivePaddingGates n counterWidth)

/-- The inactive-padding gate list is wire-disjoint from the active flag. -/
lemma detectorCounterInactivePaddingGates_bitDisjoint_active
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ detectorCounterInactivePaddingGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (detectorCounterActiveBit n counterWidth) gate := by
  intro gate hgate
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (detectorCounterIncrementLayout n counterWidth)
      (detectorCounterActiveBit n counterWidth)
      (fun i =>
        Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth (liftedActiveBit n counterWidth)
            (counterIncrementSourceBit counterWidth i)))
      (fun i =>
        liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
          n counterWidth
          (liftRegisterBitToComparisonWork n counterWidth
            (RegisterBits.counterBit n counterWidth
              (WireAddress.littleEndianWire i)))
          (liftedActiveBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.counterBit n counterWidth
              (WireAddress.littleEndianWire i))
            (RegisterBits.activeBit n counterWidth)
            (Ne.symm
              (RegisterBits.active_counter_wire_ne n counterWidth
                (WireAddress.littleEndianWire i)))))
      (Ne.symm
        (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
          n counterWidth (liftedActiveBit n counterWidth)
          (counterIncrementCarryInBit counterWidth)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth (liftedActiveBit n counterWidth)
            (counterIncrementCarryWorkBit counterWidth j)))
      gate hgate

/-- The inactive-padding gate list is wire-disjoint from any selected
comparison-work bit, which can serve as the clean control-work bit. -/
lemma detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n) :
    ∀ gate, gate ∈ detectorCounterInactivePaddingGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (detectorCounterComparisonCarryBit n counterWidth workBit) gate := by
  intro gate hgate
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (detectorCounterIncrementLayout n counterWidth)
      (detectorCounterComparisonCarryBit n counterWidth workBit)
      (fun i =>
        Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth (liftedComparisonCarryBit n counterWidth workBit)
            (counterIncrementSourceBit counterWidth i)))
      (fun i =>
        liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
          n counterWidth
          (liftRegisterBitToComparisonWork n counterWidth
            (RegisterBits.counterBit n counterWidth
              (WireAddress.littleEndianWire i)))
          (liftedComparisonCarryBit n counterWidth workBit)
          (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
            (RegisterBits.counterBit n counterWidth
              (WireAddress.littleEndianWire i))
            (comparisonCarryValueBit n workBit)))
      (Ne.symm
        (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
          n counterWidth (liftedComparisonCarryBit n counterWidth workBit)
          (counterIncrementCarryInBit counterWidth)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth (liftedComparisonCarryBit n counterWidth workBit)
            (counterIncrementCarryWorkBit counterWidth j)))
      gate hgate

/-- Active and a selected comparison-work carry bit are distinct in the
detector-plus-counter workspace. -/
lemma detectorCounterActiveBit_comparisonCarryBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (detectorCounterActiveBit n counterWidth).wire ≠
      (detectorCounterComparisonCarryBit n counterWidth workBit).wire :=
  liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
    n counterWidth (liftedActiveBit n counterWidth)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (comparisonCarryValueBit n workBit))

/-- Active-false-controlled inactive padding in the detector-plus-counter
workspace.  The active flag is flipped around a clean-work controlled padding
incrementer, so inactive inputs run the padding route and active inputs are
left untouched. -/
def detectorCounterActiveFalseControlledInactivePaddingGates
    (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)) :=
  [EncodedBit.GateSpec.x
    (detectorCounterActiveBit tail.succ counterWidth)] ++
  EncodedBit.GateSpec.controlledListWithWorkGates
    (detectorCounterActiveBit tail.succ counterWidth)
    (detectorCounterComparisonCarryBit tail.succ counterWidth (Fin.last tail))
    (detectorCounterInactivePaddingGates tail.succ counterWidth)
    (detectorCounterInactivePaddingGates_bitDisjoint_active
      tail.succ counterWidth)
    (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
      tail.succ counterWidth (Fin.last tail))
    (detectorCounterActiveBit_comparisonCarryBit_wire_ne
      tail.succ counterWidth (Fin.last tail)) ++
  [EncodedBit.GateSpec.x
    (detectorCounterActiveBit tail.succ counterWidth)]

/-- Semantic action for active-false-controlled inactive padding in the
detector-plus-counter workspace. -/
def detectorCounterActiveFalseControlledInactivePaddingStep
    (tail counterWidth : Nat) :
    RegistersWithDetectorCounterWork tail.succ counterWidth ->
      RegistersWithDetectorCounterWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth)

/-- Actual active-false-controlled inactive-padding circuit in the
detector-plus-counter workspace. -/
def detectorCounterActiveFalseControlledInactivePaddingProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithDetectorCounterWorkEncoding
          tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth)

/-- The controlled inactive-padding circuit realizes its gate-list action. -/
lemma detectorCounterActiveFalseControlledInactivePadding_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)
      (detectorCounterActiveFalseControlledInactivePaddingProgram
        tail counterWidth) environment
      (detectorCounterActiveFalseControlledInactivePaddingStep
        tail counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth)

/-- If active is false and the selected comparison-work bit is clean, the
active-false wrapper runs the inactive-padding gate list. -/
lemma
    detectorCounterActiveFalseControlledInactivePaddingStep_eq_padding_of_active_false_clean
    (tail counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork tail.succ counterWidth)
    (hactive :
      (detectorCounterActiveBit tail.succ counterWidth).get x = false)
    (hwork :
      (detectorCounterComparisonCarryBit tail.succ counterWidth
        (Fin.last tail)).get x = false) :
    detectorCounterActiveFalseControlledInactivePaddingStep
        tail counterWidth x =
      detectorCounterInactivePaddingGateStep tail.succ counterWidth x := by
  let active := detectorCounterActiveBit tail.succ counterWidth
  let work :=
    detectorCounterComparisonCarryBit tail.succ counterWidth (Fin.last tail)
  let gates := detectorCounterInactivePaddingGates tail.succ counterWidth
  have hactiveFlip : active.get (active.flip x) = true := by
    dsimp [active]
    rw [EncodedBit.get_flip_self, hactive]
    rfl
  have hworkFlip : work.get (active.flip x) = false := by
    dsimp [active, work]
    rw [EncodedBit.get_flip_of_wire_ne
      (detectorCounterActiveBit tail.succ counterWidth)
      (detectorCounterComparisonCarryBit tail.succ counterWidth
        (Fin.last tail))]
    · exact hwork
    · exact detectorCounterActiveBit_comparisonCarryBit_wire_ne
        tail.succ counterWidth (Fin.last tail)
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates active work gates
            (detectorCounterInactivePaddingGates_bitDisjoint_active
              tail.succ counterWidth)
            (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
              tail.succ counterWidth (Fin.last tail))
            (detectorCounterActiveBit_comparisonCarryBit_wire_ne
              tail.succ counterWidth (Fin.last tail)))
          (active.flip x) =
        EncodedBit.GateSpec.stepList gates (active.flip x) := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
        active work gates
        (detectorCounterInactivePaddingGates_bitDisjoint_active
          tail.succ counterWidth)
        (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
          tail.succ counterWidth (Fin.last tail))
        (detectorCounterActiveBit_comparisonCarryBit_wire_ne
          tail.succ counterWidth (Fin.last tail))
        (active.flip x) hactiveFlip hworkFlip
  have hcomm :
      EncodedBit.GateSpec.stepList gates (active.flip x) =
        active.flip (EncodedBit.GateSpec.stepList gates x) := by
    exact EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
      gates active
      (detectorCounterInactivePaddingGates_bitDisjoint_active
        tail.succ counterWidth) x
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates active work gates
          (detectorCounterInactivePaddingGates_bitDisjoint_active
            tail.succ counterWidth)
          (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
            tail.succ counterWidth (Fin.last tail))
          (detectorCounterActiveBit_comparisonCarryBit_wire_ne
            tail.succ counterWidth (Fin.last tail)) ++
        [EncodedBit.GateSpec.x active])
      (active.flip x) =
    detectorCounterInactivePaddingGateStep tail.succ counterWidth x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle, hcomm]
  simp [detectorCounterInactivePaddingGateStep, gates,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.flip_flip]

/-- If active is true, the active-false inactive-padding wrapper is a no-op. -/
lemma
    detectorCounterActiveFalseControlledInactivePaddingStep_eq_self_of_active_true
    (tail counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork tail.succ counterWidth)
    (hactive :
      (detectorCounterActiveBit tail.succ counterWidth).get x = true) :
    detectorCounterActiveFalseControlledInactivePaddingStep
        tail counterWidth x = x := by
  let active := detectorCounterActiveBit tail.succ counterWidth
  let work :=
    detectorCounterComparisonCarryBit tail.succ counterWidth (Fin.last tail)
  let gates := detectorCounterInactivePaddingGates tail.succ counterWidth
  have hactiveFlip : active.get (active.flip x) = false := by
    dsimp [active]
    rw [EncodedBit.get_flip_self, hactive]
    rfl
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates active work gates
            (detectorCounterInactivePaddingGates_bitDisjoint_active
              tail.succ counterWidth)
            (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
              tail.succ counterWidth (Fin.last tail))
            (detectorCounterActiveBit_comparisonCarryBit_wire_ne
              tail.succ counterWidth (Fin.last tail)))
          (active.flip x) =
        active.flip x := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        active work gates
        (detectorCounterInactivePaddingGates_bitDisjoint_active
          tail.succ counterWidth)
        (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
          tail.succ counterWidth (Fin.last tail))
        (detectorCounterActiveBit_comparisonCarryBit_wire_ne
          tail.succ counterWidth (Fin.last tail))
        (active.flip x) hactiveFlip
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates active work gates
          (detectorCounterInactivePaddingGates_bitDisjoint_active
            tail.succ counterWidth)
          (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
            tail.succ counterWidth (Fin.last tail))
          (detectorCounterActiveBit_comparisonCarryBit_wire_ne
            tail.succ counterWidth (Fin.last tail)) ++
        [EncodedBit.GateSpec.x active])
      (active.flip x) = x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle]
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.flip_flip]

/-- Embed a temporary carry-work index for an `n`-bit adder into the available
comparison carry-work word. -/
def coeffAdderComparisonCarryPrefixIndex (n : Nat) (bit : Fin (n - 1)) :
    Fin n :=
  ⟨bit.val, by
    have hbit := bit.isLt
    omega⟩

@[simp] lemma coeffAdderComparisonCarryPrefixIndex_val
    (n : Nat) (bit : Fin (n - 1)) :
    (coeffAdderComparisonCarryPrefixIndex n bit).val = bit.val :=
  rfl

lemma coeffAdderComparisonCarryPrefixIndex_ne
    (n : Nat) {left right : Fin (n - 1)} (h : left ≠ right) :
    coeffAdderComparisonCarryPrefixIndex n left ≠
      coeffAdderComparisonCarryPrefixIndex n right := by
  intro hp
  apply h
  apply Fin.ext
  exact congrArg (fun bit : Fin n => bit.val) hp

/-- Every source-adder prefix carry index is distinct from an index known to
be the final comparison carry. -/
lemma coeffAdderComparisonCarryPrefixIndex_ne_final
    (n : Nat) (finalBit : Fin n) (hfinal : finalBit.val + 1 = n)
    (prefixBit : Fin (n - 1)) :
    coeffAdderComparisonCarryPrefixIndex n prefixBit ≠ finalBit := by
  intro h
  have hval := congrArg Fin.val h
  simp only [coeffAdderComparisonCarryPrefixIndex_val] at hval
  have hprefix := prefixBit.isLt
  omega

/-- Prefix of the comparison carry-work word sized for an `n`-bit VBE
carry-work layout. -/
def coeffAdderComparisonCarryPrefixWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) (n - 1) where
  bit := fun bit =>
    coeffAdderComparisonCarryBit n counterWidth
      (coeffAdderComparisonCarryPrefixIndex n bit)

/-- The lifted comparison ancilla and a lifted `u` bit occupy distinct wires. -/
lemma liftedCompare_liftedUBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (liftedCompareBit n counterWidth).wire ≠
      (liftedUBit n counterWidth bit).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.uBit n counterWidth bit)
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))

/-- The lifted comparison ancilla and a lifted `v` bit occupy distinct wires. -/
lemma liftedCompare_liftedVBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (liftedCompareBit n counterWidth).wire ≠
      (liftedVBit n counterWidth bit).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.vBit n counterWidth bit)
    (Ne.symm (RegisterBits.v_compare_wire_ne n counterWidth bit))

/-- Lifted `u` and `v` bits occupy distinct wires. -/
lemma liftedUBit_liftedVBit_wire_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    (liftedUBit n counterWidth uIndex).wire ≠
      (liftedVBit n counterWidth vIndex).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.uBit n counterWidth uIndex)
    (RegisterBits.vBit n counterWidth vIndex)
    (RegisterBits.u_v_wire_ne n counterWidth uIndex vIndex)

/-- The lifted comparison ancilla and a lifted little-endian `u` value bit
occupy distinct wires. -/
lemma liftedCompare_liftedUWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (liftedCompareBit n counterWidth).wire ≠
      ((liftedUWord n counterWidth).bit bit).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.uValueBit n counterWidth bit)
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)))

/-- The lifted comparison ancilla and a lifted little-endian `v` value bit
occupy distinct wires. -/
lemma liftedCompare_liftedVWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (liftedCompareBit n counterWidth).wire ≠
      ((liftedVWord n counterWidth).bit bit).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.vValueBit n counterWidth bit)
    (Ne.symm (RegisterBits.v_compare_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)))

/-- The lifted comparison ancilla and a lifted `s` coefficient bit occupy
distinct wires. -/
lemma liftedCompare_liftedSCoeffWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (liftedCompareBit n counterWidth).wire ≠
      ((liftedSCoeffWord n counterWidth).bit bit).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.sCoeffBit n counterWidth bit)
    (RegisterBits.compare_sCoeff_wire_ne n counterWidth bit)

/-- The lifted comparison ancilla and a lifted `r` coefficient bit occupy
distinct wires. -/
lemma liftedCompare_liftedRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (liftedCompareBit n counterWidth).wire ≠
      ((liftedRCoeffWord n counterWidth).bit bit).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.rCoeffBit n counterWidth bit)
    (RegisterBits.compare_rCoeff_wire_ne n counterWidth bit)

/-- The lifted comparison ancilla and a lifted little-endian `s` coefficient
value bit occupy distinct wires. -/
lemma liftedCompare_liftedSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (liftedCompareBit n counterWidth).wire ≠
      ((liftedSCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [liftedSCoeffValueWord, liftedSCoeffWord,
    RegisterBits.sCoeffValueBit] using
    liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)

/-- The lifted comparison ancilla and a lifted little-endian `r` coefficient
value bit occupy distinct wires. -/
lemma liftedCompare_liftedRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (liftedCompareBit n counterWidth).wire ≠
      ((liftedRCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [liftedRCoeffValueWord, liftedRCoeffWord,
    RegisterBits.rCoeffValueBit] using
    liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)

/-- Lifted little-endian `u` and `v` value bits occupy distinct wires. -/
lemma liftedUWordBit_liftedVWordBit_wire_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    ((liftedUWord n counterWidth).bit uIndex).wire ≠
      ((liftedVWord n counterWidth).bit vIndex).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.uValueBit n counterWidth uIndex)
    (RegisterBits.vValueBit n counterWidth vIndex)
    (RegisterBits.u_v_wire_ne n counterWidth
      (WireAddress.littleEndianWire uIndex)
      (WireAddress.littleEndianWire vIndex))

/-- Lifted little-endian `u` value bits are disjoint from lifted `s`
coefficient bits. -/
lemma liftedUWordBit_liftedSCoeffWordBit_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (sIndex : Fin (n + 1)) :
    ((liftedUWord n counterWidth).bit uIndex).wire ≠
      ((liftedSCoeffWord n counterWidth).bit sIndex).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.uValueBit n counterWidth uIndex)
    (RegisterBits.sCoeffBit n counterWidth sIndex)
    (RegisterBits.u_sCoeff_wire_ne n counterWidth
      (WireAddress.littleEndianWire uIndex) sIndex)

/-- Lifted little-endian `u` value bits are disjoint from lifted `r`
coefficient bits. -/
lemma liftedUWordBit_liftedRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (rIndex : Fin (n + 1)) :
    ((liftedUWord n counterWidth).bit uIndex).wire ≠
      ((liftedRCoeffWord n counterWidth).bit rIndex).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.uValueBit n counterWidth uIndex)
    (RegisterBits.rCoeffBit n counterWidth rIndex)
    (RegisterBits.u_rCoeff_wire_ne n counterWidth
      (WireAddress.littleEndianWire uIndex) rIndex)

/-- Lifted little-endian `u` value bits are disjoint from lifted little-endian
`s` coefficient value bits. -/
lemma liftedUWordBit_liftedSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (sIndex : Fin (n + 1)) :
    ((liftedUWord n counterWidth).bit uIndex).wire ≠
      ((liftedSCoeffValueWord n counterWidth).bit sIndex).wire := by
  simpa [liftedSCoeffValueWord, liftedSCoeffWord,
    RegisterBits.sCoeffValueBit] using
    liftedUWordBit_liftedSCoeffWordBit_wire_ne n counterWidth uIndex
      (WireAddress.littleEndianWire sIndex)

/-- Lifted little-endian `u` value bits are disjoint from lifted little-endian
`r` coefficient value bits. -/
lemma liftedUWordBit_liftedRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (rIndex : Fin (n + 1)) :
    ((liftedUWord n counterWidth).bit uIndex).wire ≠
      ((liftedRCoeffValueWord n counterWidth).bit rIndex).wire := by
  simpa [liftedRCoeffValueWord, liftedRCoeffWord,
    RegisterBits.rCoeffValueBit] using
    liftedUWordBit_liftedRCoeffWordBit_wire_ne n counterWidth uIndex
      (WireAddress.littleEndianWire rIndex)

/-- Lifted little-endian `v` value bits are disjoint from lifted `s`
coefficient bits. -/
lemma liftedVWordBit_liftedSCoeffWordBit_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (sIndex : Fin (n + 1)) :
    ((liftedVWord n counterWidth).bit vIndex).wire ≠
      ((liftedSCoeffWord n counterWidth).bit sIndex).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.vValueBit n counterWidth vIndex)
    (RegisterBits.sCoeffBit n counterWidth sIndex)
    (RegisterBits.v_sCoeff_wire_ne n counterWidth
      (WireAddress.littleEndianWire vIndex) sIndex)

/-- Lifted little-endian `v` value bits are disjoint from lifted `r`
coefficient bits. -/
lemma liftedVWordBit_liftedRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (rIndex : Fin (n + 1)) :
    ((liftedVWord n counterWidth).bit vIndex).wire ≠
      ((liftedRCoeffWord n counterWidth).bit rIndex).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.vValueBit n counterWidth vIndex)
    (RegisterBits.rCoeffBit n counterWidth rIndex)
    (RegisterBits.v_rCoeff_wire_ne n counterWidth
      (WireAddress.littleEndianWire vIndex) rIndex)

/-- Lifted little-endian `v` value bits are disjoint from lifted little-endian
`s` coefficient value bits. -/
lemma liftedVWordBit_liftedSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (sIndex : Fin (n + 1)) :
    ((liftedVWord n counterWidth).bit vIndex).wire ≠
      ((liftedSCoeffValueWord n counterWidth).bit sIndex).wire := by
  simpa [liftedSCoeffValueWord, liftedSCoeffWord,
    RegisterBits.sCoeffValueBit] using
    liftedVWordBit_liftedSCoeffWordBit_wire_ne n counterWidth vIndex
      (WireAddress.littleEndianWire sIndex)

/-- Lifted little-endian `v` value bits are disjoint from lifted little-endian
`r` coefficient value bits. -/
lemma liftedVWordBit_liftedRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (rIndex : Fin (n + 1)) :
    ((liftedVWord n counterWidth).bit vIndex).wire ≠
      ((liftedRCoeffValueWord n counterWidth).bit rIndex).wire := by
  simpa [liftedRCoeffValueWord, liftedRCoeffWord,
    RegisterBits.rCoeffValueBit] using
    liftedVWordBit_liftedRCoeffWordBit_wire_ne n counterWidth vIndex
      (WireAddress.littleEndianWire rIndex)

/-- Distinct lifted little-endian `u` value bits occupy distinct wires. -/
lemma liftedUWordBit_liftedUWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    ((liftedUWord n counterWidth).bit left).wire ≠
      ((liftedUWord n counterWidth).bit right).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.uValueBit n counterWidth left)
    (RegisterBits.uValueBit n counterWidth right)
    (u_u_wire_ne n counterWidth
      (WireAddress.littleEndianWire left)
      (WireAddress.littleEndianWire right)
      (littleEndianWire_ne h))

/-- Distinct lifted little-endian `v` value bits occupy distinct wires. -/
lemma liftedVWordBit_liftedVWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    ((liftedVWord n counterWidth).bit left).wire ≠
      ((liftedVWord n counterWidth).bit right).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.vValueBit n counterWidth left)
    (RegisterBits.vValueBit n counterWidth right)
    (v_v_wire_ne n counterWidth
      (WireAddress.littleEndianWire left)
      (WireAddress.littleEndianWire right)
      (littleEndianWire_ne h))

/-- Lifted `s` and `r` coefficient bits occupy distinct wires. -/
lemma liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (sIndex rIndex : Fin (n + 1)) :
    ((liftedSCoeffWord n counterWidth).bit sIndex).wire ≠
      ((liftedRCoeffWord n counterWidth).bit rIndex).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.sCoeffBit n counterWidth sIndex)
    (RegisterBits.rCoeffBit n counterWidth rIndex)
    (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth sIndex rIndex)

/-- Distinct lifted `s` coefficient bits occupy distinct wires. -/
lemma liftedSCoeffWordBit_liftedSCoeffWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((liftedSCoeffWord n counterWidth).bit left).wire ≠
      ((liftedSCoeffWord n counterWidth).bit right).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.sCoeffBit n counterWidth left)
    (RegisterBits.sCoeffBit n counterWidth right)
    (sCoeff_sCoeff_wire_ne n counterWidth left right h)

/-- Distinct lifted `r` coefficient bits occupy distinct wires. -/
lemma liftedRCoeffWordBit_liftedRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((liftedRCoeffWord n counterWidth).bit left).wire ≠
      ((liftedRCoeffWord n counterWidth).bit right).wire := by
  exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
    (RegisterBits.rCoeffBit n counterWidth left)
    (RegisterBits.rCoeffBit n counterWidth right)
    (rCoeff_rCoeff_wire_ne n counterWidth left right h)

/-- Lifted little-endian `s` and `r` coefficient value bits occupy distinct
wires. -/
lemma liftedSCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (sIndex rIndex : Fin (n + 1)) :
    ((liftedSCoeffValueWord n counterWidth).bit sIndex).wire ≠
      ((liftedRCoeffValueWord n counterWidth).bit rIndex).wire := by
  simpa [liftedSCoeffValueWord, liftedRCoeffValueWord, liftedSCoeffWord,
    liftedRCoeffWord, RegisterBits.sCoeffValueBit,
    RegisterBits.rCoeffValueBit] using
    liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire sIndex)
      (WireAddress.littleEndianWire rIndex)

/-- Distinct lifted little-endian `s` coefficient value bits occupy distinct
wires. -/
lemma liftedSCoeffValueWordBit_liftedSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((liftedSCoeffValueWord n counterWidth).bit left).wire ≠
      ((liftedSCoeffValueWord n counterWidth).bit right).wire := by
  simpa [liftedSCoeffValueWord, liftedSCoeffWord,
    RegisterBits.sCoeffValueBit] using
    liftedSCoeffWordBit_liftedSCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire left) (WireAddress.littleEndianWire right)
      (littleEndianWire_ne h)

/-- Distinct lifted little-endian `r` coefficient value bits occupy distinct
wires. -/
lemma liftedRCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((liftedRCoeffValueWord n counterWidth).bit left).wire ≠
      ((liftedRCoeffValueWord n counterWidth).bit right).wire := by
  simpa [liftedRCoeffValueWord, liftedRCoeffWord,
    RegisterBits.rCoeffValueBit] using
    liftedRCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire left) (WireAddress.littleEndianWire right)
      (littleEndianWire_ne h)

/-- Distinct coefficient-work-lifted `u` value bits occupy distinct wires. -/
lemma coeffAdderUWordBit_coeffAdderUWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    ((coeffAdderUWord n counterWidth).bit left).wire ≠
      ((coeffAdderUWord n counterWidth).bit right).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedUWord n counterWidth).bit left)
    ((liftedUWord n counterWidth).bit right)
    (liftedUWordBit_liftedUWordBit_wire_ne n counterWidth left right h)

/-- Distinct coefficient-work-lifted `v` value bits occupy distinct wires. -/
lemma coeffAdderVWordBit_coeffAdderVWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    ((coeffAdderVWord n counterWidth).bit left).wire ≠
      ((coeffAdderVWord n counterWidth).bit right).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedVWord n counterWidth).bit left)
    ((liftedVWord n counterWidth).bit right)
    (liftedVWordBit_liftedVWordBit_wire_ne n counterWidth left right h)

/-- Coefficient-work-lifted `u` and `v` value bits occupy distinct wires. -/
lemma coeffAdderUWordBit_coeffAdderVWordBit_wire_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    ((coeffAdderUWord n counterWidth).bit uIndex).wire ≠
      ((coeffAdderVWord n counterWidth).bit vIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedUWord n counterWidth).bit uIndex)
    ((liftedVWord n counterWidth).bit vIndex)
    (liftedUWordBit_liftedVWordBit_wire_ne n counterWidth uIndex vIndex)

/-- Coefficient-work-lifted `u` value bits are disjoint from coefficient-work
little-endian `s` coefficient value bits. -/
lemma coeffAdderUWordBit_coeffAdderSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (sIndex : Fin (n + 1)) :
    ((coeffAdderUWord n counterWidth).bit uIndex).wire ≠
      ((coeffAdderSCoeffValueWord n counterWidth).bit sIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedUWord n counterWidth).bit uIndex)
    ((liftedSCoeffValueWord n counterWidth).bit sIndex)
    (liftedUWordBit_liftedSCoeffValueWordBit_wire_ne n counterWidth
      uIndex sIndex)

/-- Coefficient-work-lifted `u` value bits are disjoint from coefficient-work
little-endian `r` coefficient value bits. -/
lemma coeffAdderUWordBit_coeffAdderRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (rIndex : Fin (n + 1)) :
    ((coeffAdderUWord n counterWidth).bit uIndex).wire ≠
      ((coeffAdderRCoeffValueWord n counterWidth).bit rIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedUWord n counterWidth).bit uIndex)
    ((liftedRCoeffValueWord n counterWidth).bit rIndex)
    (liftedUWordBit_liftedRCoeffValueWordBit_wire_ne n counterWidth
      uIndex rIndex)

/-- Coefficient-work-lifted `v` value bits are disjoint from coefficient-work
little-endian `s` coefficient value bits. -/
lemma coeffAdderVWordBit_coeffAdderSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (sIndex : Fin (n + 1)) :
    ((coeffAdderVWord n counterWidth).bit vIndex).wire ≠
      ((coeffAdderSCoeffValueWord n counterWidth).bit sIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedVWord n counterWidth).bit vIndex)
    ((liftedSCoeffValueWord n counterWidth).bit sIndex)
    (liftedVWordBit_liftedSCoeffValueWordBit_wire_ne n counterWidth
      vIndex sIndex)

/-- Coefficient-work-lifted `v` value bits are disjoint from coefficient-work
little-endian `r` coefficient value bits. -/
lemma coeffAdderVWordBit_coeffAdderRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (rIndex : Fin (n + 1)) :
    ((coeffAdderVWord n counterWidth).bit vIndex).wire ≠
      ((coeffAdderRCoeffValueWord n counterWidth).bit rIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedVWord n counterWidth).bit vIndex)
    ((liftedRCoeffValueWord n counterWidth).bit rIndex)
    (liftedVWordBit_liftedRCoeffValueWordBit_wire_ne n counterWidth
      vIndex rIndex)

/-- Coefficient-work-lifted `u` value bits are disjoint from comparison-work
carry bits. -/
lemma coeffAdderUWordBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (bit workBit : Fin n) :
    ((coeffAdderUWord n counterWidth).bit bit).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedUWord n counterWidth).bit bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth bit)
      (comparisonCarryValueBit n workBit))

/-- Coefficient-work-lifted `v` value bits are disjoint from comparison-work
carry bits. -/
lemma coeffAdderVWordBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (bit workBit : Fin n) :
    ((coeffAdderVWord n counterWidth).bit bit).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedVWord n counterWidth).bit bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth bit)
      (comparisonCarryValueBit n workBit))

/-- Coefficient-work-lifted selected `u` and selected `v` bits are disjoint. -/
lemma coeffAdderUBit_coeffAdderVBit_wire_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    (coeffAdderUBit n counterWidth uIndex).wire ≠
      (coeffAdderVBit n counterWidth vIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedUBit n counterWidth uIndex)
    (liftedVBit n counterWidth vIndex)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uBit n counterWidth uIndex)
      (RegisterBits.vBit n counterWidth vIndex)
      (RegisterBits.u_v_wire_ne n counterWidth uIndex vIndex))

/-- The coefficient-work-lifted active flag is disjoint from selected `u`
bits. -/
lemma coeffAdderActiveBit_coeffAdderUBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      (coeffAdderUBit n counterWidth bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    (liftedUBit n counterWidth bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.uBit n counterWidth bit)
      (RegisterBits.active_u_wire_ne n counterWidth bit))

/-- The coefficient-work-lifted active flag is disjoint from selected `v`
bits. -/
lemma coeffAdderActiveBit_coeffAdderVBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      (coeffAdderVBit n counterWidth bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    (liftedVBit n counterWidth bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.vBit n counterWidth bit)
      (RegisterBits.active_v_wire_ne n counterWidth bit))

/-- Coefficient-work-lifted selected `u` bits are disjoint from compare. -/
lemma coeffAdderUBit_coeffAdderCompareBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderUBit n counterWidth bit).wire ≠
      (coeffAdderCompareBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedUBit n counterWidth bit)
    (liftedCompareBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uBit n counterWidth bit)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.u_compare_wire_ne n counterWidth bit))

/-- Coefficient-work-lifted selected `v` bits are disjoint from compare. -/
lemma coeffAdderVBit_coeffAdderCompareBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderVBit n counterWidth bit).wire ≠
      (coeffAdderCompareBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedVBit n counterWidth bit)
    (liftedCompareBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vBit n counterWidth bit)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.v_compare_wire_ne n counterWidth bit))

/-- The coefficient-work-lifted active flag is disjoint from compare. -/
lemma coeffAdderActiveBit_coeffAdderCompareBit_wire_ne
    (n counterWidth : Nat) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      (coeffAdderCompareBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    (liftedCompareBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth))

/-- Coefficient-work-lifted selected `u` bits are disjoint from
comparison-work carry bits. -/
lemma coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (bit workBit : Fin n) :
    (coeffAdderUBit n counterWidth bit).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedUBit n counterWidth bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.uBit n counterWidth bit)
      (comparisonCarryValueBit n workBit))

/-- Coefficient-work-lifted selected `v` bits are disjoint from
comparison-work carry bits. -/
lemma coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (bit workBit : Fin n) :
    (coeffAdderVBit n counterWidth bit).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedVBit n counterWidth bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.vBit n counterWidth bit)
      (comparisonCarryValueBit n workBit))

/-- The coefficient-work-lifted compare bit is disjoint from comparison-work
carry bits. -/
lemma coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (coeffAdderCompareBit n counterWidth).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedCompareBit n counterWidth)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth workBit)

/-- The coefficient-work-lifted active flag is disjoint from comparison-work
carry bits. -/
lemma coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (comparisonCarryValueBit n workBit))

/-- The coefficient-work-lifted scratchA bit is disjoint from comparison-work
carry bits. -/
lemma coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedScratchA_liftedComparisonCarry_wire_ne n counterWidth workBit)

/-- The coefficient-work-lifted scratchB bit is disjoint from comparison-work
carry bits. -/
lemma coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (coeffAdderScratchBBit n counterWidth).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchBBit n counterWidth)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth)
      (comparisonCarryValueBit n workBit))

/-- Distinct coefficient-work-lifted comparison-carry bits occupy distinct
wires. -/
lemma coeffAdderComparisonCarryBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    (coeffAdderComparisonCarryBit n counterWidth left).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth right).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedComparisonCarryBit n counterWidth left)
    (liftedComparisonCarryBit n counterWidth right)
    (liftComparisonWorkBit_liftComparisonWorkBit_wire_ne n counterWidth
      (comparisonCarryValueBit n left) (comparisonCarryValueBit n right)
      (comparisonCarryValue_comparisonCarryValue_wire_ne n left right h))

/-- Distinct coefficient-work-lifted `s` coefficient bits occupy distinct
wires. -/
lemma coeffAdderSCoeffWordBit_coeffAdderSCoeffWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((coeffAdderSCoeffWord n counterWidth).bit left).wire ≠
      ((coeffAdderSCoeffWord n counterWidth).bit right).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedSCoeffWord n counterWidth).bit left)
    ((liftedSCoeffWord n counterWidth).bit right)
    (liftedSCoeffWordBit_liftedSCoeffWordBit_wire_ne n counterWidth left
      right h)

/-- Distinct coefficient-work-lifted `r` coefficient bits occupy distinct
wires. -/
lemma coeffAdderRCoeffWordBit_coeffAdderRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((coeffAdderRCoeffWord n counterWidth).bit left).wire ≠
      ((coeffAdderRCoeffWord n counterWidth).bit right).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedRCoeffWord n counterWidth).bit left)
    ((liftedRCoeffWord n counterWidth).bit right)
    (liftedRCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth left
      right h)

/-- Distinct coefficient-work-lifted little-endian `s` coefficient value bits
occupy distinct wires. -/
lemma coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit left).wire ≠
      ((coeffAdderSCoeffValueWord n counterWidth).bit right).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedSCoeffValueWord n counterWidth).bit left)
    ((liftedSCoeffValueWord n counterWidth).bit right)
    (liftedSCoeffValueWordBit_liftedSCoeffValueWordBit_wire_ne n counterWidth
      left right h)

/-- Distinct coefficient-work-lifted little-endian `r` coefficient value bits
occupy distinct wires. -/
lemma coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit left).wire ≠
      ((coeffAdderRCoeffValueWord n counterWidth).bit right).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedRCoeffValueWord n counterWidth).bit left)
    ((liftedRCoeffValueWord n counterWidth).bit right)
    (liftedRCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne n counterWidth
      left right h)

/-- Coefficient-work-lifted little-endian `s` and `r` coefficient value bits
occupy distinct wires. -/
lemma coeffAdderSCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (sIndex rIndex : Fin (n + 1)) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit sIndex).wire ≠
      ((coeffAdderRCoeffValueWord n counterWidth).bit rIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedSCoeffValueWord n counterWidth).bit sIndex)
    ((liftedRCoeffValueWord n counterWidth).bit rIndex)
    (liftedSCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne n counterWidth
      sIndex rIndex)

/-- The coefficient-work-lifted active flag is disjoint from every `u` value
bit. -/
lemma coeffAdderActiveBit_coeffAdderUWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      ((coeffAdderUWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    ((liftedUWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.uValueBit n counterWidth bit)
      (RegisterBits.active_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)))

/-- The coefficient-work-lifted active flag is disjoint from every `v` value
bit. -/
lemma coeffAdderActiveBit_coeffAdderVWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      ((coeffAdderVWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    ((liftedVWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.vValueBit n counterWidth bit)
      (RegisterBits.active_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)))

/-- The coefficient-work-lifted active flag is disjoint from every `s`
coefficient bit. -/
lemma coeffAdderActiveBit_coeffAdderSCoeffWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      ((coeffAdderSCoeffWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    ((liftedSCoeffWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.sCoeffBit n counterWidth bit)
      (RegisterBits.active_sCoeff_wire_ne n counterWidth bit))

/-- The coefficient-work-lifted active flag is disjoint from every `r`
coefficient bit. -/
lemma coeffAdderActiveBit_coeffAdderRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      ((coeffAdderRCoeffWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    ((liftedRCoeffWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.rCoeffBit n counterWidth bit)
      (RegisterBits.active_rCoeff_wire_ne n counterWidth bit))

/-- The coefficient-work-lifted active flag is disjoint from every
little-endian `s` coefficient value bit. -/
lemma coeffAdderActiveBit_coeffAdderSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [coeffAdderSCoeffValueWord, liftedSCoeffValueWord, coeffAdderSCoeffWord,
    liftedSCoeffWord, RegisterBits.sCoeffValueBit] using
    coeffAdderActiveBit_coeffAdderSCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)

/-- The coefficient-work-lifted active flag is disjoint from every
little-endian `r` coefficient value bit. -/
lemma coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [coeffAdderRCoeffValueWord, liftedRCoeffValueWord, coeffAdderRCoeffWord,
    liftedRCoeffWord, RegisterBits.rCoeffValueBit] using
    coeffAdderActiveBit_coeffAdderRCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)

/-- The coefficient-work-lifted active flag is disjoint from scratchA. -/
lemma coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
    (n counterWidth : Nat) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      (coeffAdderScratchABit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    (liftedScratchABit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.active_scratchA_wire_ne n counterWidth))

/-- The coefficient-work-lifted active flag is disjoint from scratchB. -/
lemma coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
    (n counterWidth : Nat) :
    (coeffAdderActiveBit n counterWidth).wire ≠
      (coeffAdderScratchBBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedActiveBit n counterWidth)
    (liftedScratchBBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth)
      (RegisterBits.scratchBBit n counterWidth)
      (RegisterBits.active_scratchB_wire_ne n counterWidth))

/-- Coefficient-work-lifted selected `u` bits are disjoint from scratchA. -/
lemma coeffAdderUBit_coeffAdderScratchABit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderUBit n counterWidth bit).wire ≠
      (coeffAdderScratchABit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedUBit n counterWidth bit)
    (liftedScratchABit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uBit n counterWidth bit)
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.u_scratchA_wire_ne n counterWidth bit))

/-- Coefficient-work-lifted selected `v` bits are disjoint from scratchA. -/
lemma coeffAdderVBit_coeffAdderScratchABit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderVBit n counterWidth bit).wire ≠
      (coeffAdderScratchABit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedVBit n counterWidth bit)
    (liftedScratchABit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vBit n counterWidth bit)
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.v_scratchA_wire_ne n counterWidth bit))

/-- The coefficient-work-lifted scratchA bit is disjoint from every `u` value
bit. -/
lemma coeffAdderScratchABit_coeffAdderUWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      ((coeffAdderUWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    ((liftedUWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.uValueBit n counterWidth bit)
      (Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))))

/-- The coefficient-work-lifted scratchA bit is disjoint from every `v` value
bit. -/
lemma coeffAdderScratchABit_coeffAdderVWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      ((coeffAdderVWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    ((liftedVWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.vValueBit n counterWidth bit)
      (Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))))

/-- The coefficient-work-lifted scratchA bit is disjoint from every `s`
coefficient bit. -/
lemma coeffAdderScratchABit_coeffAdderSCoeffWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      ((coeffAdderSCoeffWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    ((liftedSCoeffWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.sCoeffBit n counterWidth bit)
      (Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth bit)))

/-- The coefficient-work-lifted scratchA bit is disjoint from every `r`
coefficient bit. -/
lemma coeffAdderScratchABit_coeffAdderRCoeffWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      ((coeffAdderRCoeffWord n counterWidth).bit bit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    ((liftedRCoeffWord n counterWidth).bit bit)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.rCoeffBit n counterWidth bit)
      (Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth bit)))

/-- The coefficient-work-lifted scratchA bit is disjoint from every
little-endian `s` coefficient value bit. -/
lemma coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [coeffAdderSCoeffValueWord, liftedSCoeffValueWord, coeffAdderSCoeffWord,
    liftedSCoeffWord, RegisterBits.sCoeffValueBit] using
    coeffAdderScratchABit_coeffAdderSCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)

/-- The coefficient-work-lifted scratchA bit is disjoint from every
little-endian `r` coefficient value bit. -/
lemma coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [coeffAdderRCoeffValueWord, liftedRCoeffValueWord, coeffAdderRCoeffWord,
    liftedRCoeffWord, RegisterBits.rCoeffValueBit] using
    coeffAdderScratchABit_coeffAdderRCoeffWordBit_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit)

/-- The coefficient-work-lifted scratchA bit is disjoint from compare. -/
lemma coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
    (n counterWidth : Nat) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      (coeffAdderCompareBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    (liftedCompareBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.compareBit n counterWidth)
      (Ne.symm (RegisterBits.compare_scratchA_wire_ne n counterWidth)))

/-- The coefficient-work-lifted scratchA and scratchB bits are disjoint. -/
lemma coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne
    (n counterWidth : Nat) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      (coeffAdderScratchBBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    (liftedScratchBBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.scratchBBit n counterWidth)
      (RegisterBits.scratchA_scratchB_wire_ne n counterWidth))

/-- The coefficient-work-lifted compare and scratchB bits are disjoint. -/
lemma coeffAdderCompareBit_coeffAdderScratchBBit_wire_ne
    (n counterWidth : Nat) :
    (coeffAdderCompareBit n counterWidth).wire ≠
      (coeffAdderScratchBBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedCompareBit n counterWidth)
    (liftedScratchBBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.scratchBBit n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth))

/-- Coefficient-work-lifted selected `u` bits are disjoint from scratchB. -/
lemma coeffAdderUBit_coeffAdderScratchBBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderUBit n counterWidth bit).wire ≠
      (coeffAdderScratchBBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedUBit n counterWidth bit)
    (liftedScratchBBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uBit n counterWidth bit)
      (RegisterBits.scratchBBit n counterWidth)
      (RegisterBits.u_scratchB_wire_ne n counterWidth bit))

/-- Coefficient-work-lifted selected `v` bits are disjoint from scratchB. -/
lemma coeffAdderVBit_coeffAdderScratchBBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffAdderVBit n counterWidth bit).wire ≠
      (coeffAdderScratchBBit n counterWidth).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedVBit n counterWidth bit)
    (liftedScratchBBit n counterWidth)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vBit n counterWidth bit)
      (RegisterBits.scratchBBit n counterWidth)
      (RegisterBits.v_scratchB_wire_ne n counterWidth bit))

/-- Coefficient-work-lifted selected `u` bits are disjoint from history bits. -/
lemma coeffAdderUBit_coeffAdderHistoryBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    (coeffAdderUBit n counterWidth bit).wire ≠
      (coeffAdderHistoryBit n counterWidth historyIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedUBit n counterWidth bit)
    (liftedHistoryBit n counterWidth historyIndex)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uBit n counterWidth bit)
      (RegisterBits.historyBit n counterWidth historyIndex)
      (RegisterBits.u_history_wire_ne n counterWidth bit historyIndex))

/-- Coefficient-work-lifted selected `v` bits are disjoint from history bits. -/
lemma coeffAdderVBit_coeffAdderHistoryBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    (coeffAdderVBit n counterWidth bit).wire ≠
      (coeffAdderHistoryBit n counterWidth historyIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedVBit n counterWidth bit)
    (liftedHistoryBit n counterWidth historyIndex)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vBit n counterWidth bit)
      (RegisterBits.historyBit n counterWidth historyIndex)
      (RegisterBits.v_history_wire_ne n counterWidth bit historyIndex))

/-- The coefficient-work-lifted scratchA bit is disjoint from history bits. -/
lemma coeffAdderScratchABit_coeffAdderHistoryBit_wire_ne
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (coeffAdderScratchABit n counterWidth).wire ≠
      (coeffAdderHistoryBit n counterWidth historyIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchABit n counterWidth)
    (liftedHistoryBit n counterWidth historyIndex)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.historyBit n counterWidth historyIndex)
      (RegisterBits.scratchA_history_wire_ne n counterWidth historyIndex))

/-- The coefficient-work-lifted scratchB bit is disjoint from history bits. -/
lemma coeffAdderScratchBBit_coeffAdderHistoryBit_wire_ne
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (coeffAdderScratchBBit n counterWidth).wire ≠
      (coeffAdderHistoryBit n counterWidth historyIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedScratchBBit n counterWidth)
    (liftedHistoryBit n counterWidth historyIndex)
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth)
      (RegisterBits.historyBit n counterWidth historyIndex)
      (RegisterBits.scratchB_history_wire_ne n counterWidth historyIndex))

/-- Coefficient-work comparison-carry bits are disjoint from history bits. -/
lemma coeffAdderComparisonCarryBit_coeffAdderHistoryBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n)
    (historyIndex : Fin (2 * n)) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).wire ≠
      (coeffAdderHistoryBit n counterWidth historyIndex).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedHistoryBit n counterWidth historyIndex)
    (Ne.symm (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.historyBit n counterWidth historyIndex)
      (comparisonCarryValueBit n workBit)))

/-- Lifted little-endian `u` value bits are disjoint from comparison-work carry
bits. -/
lemma liftedUWordBit_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit workBit : Fin n) :
    ((liftedUWord n counterWidth).bit bit).wire ≠
      (liftedComparisonCarryBit n counterWidth workBit).wire := by
  exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
    (RegisterBits.uValueBit n counterWidth bit)
    (comparisonCarryValueBit n workBit)

/-- Lifted little-endian `v` value bits are disjoint from comparison-work carry
bits. -/
lemma liftedVWordBit_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit workBit : Fin n) :
    ((liftedVWord n counterWidth).bit bit).wire ≠
      (liftedComparisonCarryBit n counterWidth workBit).wire := by
  exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
    (RegisterBits.vValueBit n counterWidth bit)
    (comparisonCarryValueBit n workBit)

/-- Lifted `s` coefficient bits are disjoint from comparison-work carry bits. -/
lemma liftedSCoeffWordBit_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) (workBit : Fin n) :
    ((liftedSCoeffWord n counterWidth).bit bit).wire ≠
      (liftedComparisonCarryBit n counterWidth workBit).wire := by
  exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
    (RegisterBits.sCoeffBit n counterWidth bit)
    (comparisonCarryValueBit n workBit)

/-- Lifted `r` coefficient bits are disjoint from comparison-work carry bits. -/
lemma liftedRCoeffWordBit_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) (workBit : Fin n) :
    ((liftedRCoeffWord n counterWidth).bit bit).wire ≠
      (liftedComparisonCarryBit n counterWidth workBit).wire := by
  exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
    (RegisterBits.rCoeffBit n counterWidth bit)
    (comparisonCarryValueBit n workBit)

/-- Lifted little-endian `s` coefficient value bits are disjoint from
comparison-work carry bits. -/
lemma liftedSCoeffValueWordBit_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) (workBit : Fin n) :
    ((liftedSCoeffValueWord n counterWidth).bit bit).wire ≠
      (liftedComparisonCarryBit n counterWidth workBit).wire := by
  simpa [liftedSCoeffValueWord, liftedSCoeffWord,
    RegisterBits.sCoeffValueBit] using
    liftedSCoeffWordBit_liftedComparisonCarry_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit) workBit

/-- Lifted little-endian `r` coefficient value bits are disjoint from
comparison-work carry bits. -/
lemma liftedRCoeffValueWordBit_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) (workBit : Fin n) :
    ((liftedRCoeffValueWord n counterWidth).bit bit).wire ≠
      (liftedComparisonCarryBit n counterWidth workBit).wire := by
  simpa [liftedRCoeffValueWord, liftedRCoeffWord,
    RegisterBits.rCoeffValueBit] using
    liftedRCoeffWordBit_liftedComparisonCarry_wire_ne n counterWidth
      (WireAddress.littleEndianWire bit) workBit

/-- Coefficient-work-lifted `s` coefficient value bits are disjoint from
comparison-work carry bits. -/
lemma coeffAdderSCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) (workBit : Fin n) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedSCoeffValueWord n counterWidth).bit bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedSCoeffValueWordBit_liftedComparisonCarry_wire_ne
      n counterWidth bit workBit)

/-- Coefficient-work-lifted `r` coefficient value bits are disjoint from
comparison-work carry bits. -/
lemma coeffAdderRCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) (workBit : Fin n) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).wire ≠
      (coeffAdderComparisonCarryBit n counterWidth workBit).wire := by
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
    ((liftedRCoeffValueWord n counterWidth).bit bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedRCoeffValueWordBit_liftedComparisonCarry_wire_ne
      n counterWidth bit workBit)

/-! ## Compact borrowed padding counter -/

namespace Compact

/-- Little-endian padding-counter value bit in the compact carrier. -/
def paddingCounterValueBit (n k : Nat) (bit : Fin (k + 1)) :
    EncodedBit (encoding n (k + 1)) :=
  liftCoreBit n (k + 1)
    (RegisterBits.counterBit n (k + 1) (WireAddress.littleEndianWire bit))

/-- Little-endian padding-counter value word in the compact carrier. -/
def paddingCounterValueWord (n k : Nat) :
    EncodedBit.Word (encoding n (k + 1)) (k + 1) where
  bit := paddingCounterValueBit n k

@[simp] lemma paddingCounterValueBit_get
    (n k : Nat) (bit : Fin (k + 1)) (x : Registers n (k + 1)) :
    (paddingCounterValueBit n k bit).get x =
      x.core.counter.val.testBit bit.val := by
  change
    (RegisterBits.counterBit n (k + 1)
      (WireAddress.littleEndianWire bit)).get x.core =
      x.core.counter.val.testBit bit.val
  simpa only [WireAddress.bitIndex_littleEndianWire] using
    RegisterBits.counterBit_get n (k + 1)
      (WireAddress.littleEndianWire bit) x.core

/-- The high-word index corresponding to a nonzero literal-one source bit. -/
def paddingCounterSourceHighIndex {k : Nat} (bit : Fin (k + 1))
    (hbit : bit.val ≠ 0) : Fin k :=
  ⟨bit.val - 1, by
    have hlt := bit.isLt
    omega⟩

@[simp] lemma paddingCounterSourceHighIndex_val {k : Nat}
    (bit : Fin (k + 1)) (hbit : bit.val ≠ 0) :
    (paddingCounterSourceHighIndex bit hbit).val = bit.val - 1 :=
  rfl

/-- One source bit for a borrowed literal-one counter increment.  Its low bit
is the shared control bit, while higher bits borrow the correction counter. -/
def paddingCounterSourceBit (n k : Nat) (bit : Fin (k + 1)) :
    EncodedBit (encoding n (k + 1)) :=
  if hbit : bit.val = 0 then controlBit n (k + 1)
  else correctionCounterValueBit n (k + 1)
    (paddingCounterSourceHighIndex bit hbit)

/-- The borrowed source word before the literal X loads its low bit. -/
def paddingCounterSourceWord (n k : Nat) :
    EncodedBit.Word (encoding n (k + 1)) (k + 1) where
  bit := paddingCounterSourceBit n k

/-- Embed a temporary `(k+1)`-bit-adder carry index into the available VBE
carry bank. -/
def paddingCounterCarryWorkIndex (n k : Nat) (hkn : k ≤ n)
    (bit : Fin k) : Fin n :=
  ⟨bit.val, lt_of_lt_of_le bit.isLt hkn⟩

@[simp] lemma paddingCounterCarryWorkIndex_val
    (n k : Nat) (hkn : k ≤ n) (bit : Fin k) :
    (paddingCounterCarryWorkIndex n k hkn bit).val = bit.val :=
  rfl

/-- One temporary padding-counter carry bit borrowed from the VBE bank. -/
def paddingCounterCarryWorkBit (n k : Nat) (hkn : k ≤ n) (bit : Fin k) :
    EncodedBit (encoding n (k + 1)) :=
  coefficientCarryWorkBit n (k + 1)
    (paddingCounterCarryWorkIndex n k hkn bit)

/-- The `k`-bit prefix of the VBE carry bank borrowed by the counter adder. -/
def paddingCounterCarryWorkWord (n k : Nat) (hkn : k ≤ n) :
    EncodedBit.Word (encoding n (k + 1)) k where
  bit := paddingCounterCarryWorkBit n k hkn

/-- Compact clean input for one padding-counter increment.  The counter
borrows mutually exclusive correction, route, control, and VBE-carry fields;
all are required clean at entry and are returned clean at exit. -/
def paddingCounterCleanInput (n k : Nat)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    Registers n (k + 1) where
  core := core
  shared := cleanSharedWork n (k + 1)
  target := target

@[simp] lemma paddingCounterSourceBit_eq_control_of_zero
    (n k : Nat) (bit : Fin (k + 1)) (hbit : bit.val = 0) :
    paddingCounterSourceBit n k bit = controlBit n (k + 1) := by
  simp [paddingCounterSourceBit, hbit]

@[simp] lemma paddingCounterSourceBit_eq_correction_of_ne_zero
    (n k : Nat) (bit : Fin (k + 1)) (hbit : bit.val ≠ 0) :
    paddingCounterSourceBit n k bit =
      correctionCounterValueBit n (k + 1)
        (paddingCounterSourceHighIndex bit hbit) := by
  simp [paddingCounterSourceBit, hbit]

/-- Distinct borrowed source positions occupy distinct wires. -/
lemma paddingCounterSourceBit_wire_ne
    (n k : Nat) {left right : Fin (k + 1)} (hne : left ≠ right) :
    (paddingCounterSourceBit n k left).wire ≠
      (paddingCounterSourceBit n k right).wire := by
  by_cases hleft : left.val = 0
  · have hright : right.val ≠ 0 := by
      intro hright
      apply hne
      apply Fin.ext
      omega
    rw [paddingCounterSourceBit_eq_control_of_zero n k left hleft,
      paddingCounterSourceBit_eq_correction_of_ne_zero n k right hright]
    exact controlBit_correctionCounterBit_wire_ne n (k + 1)
      (WireAddress.littleEndianWire
        (paddingCounterSourceHighIndex right hright))
  · by_cases hright : right.val = 0
    · rw [paddingCounterSourceBit_eq_correction_of_ne_zero n k left hleft,
        paddingCounterSourceBit_eq_control_of_zero n k right hright]
      exact Ne.symm
        (controlBit_correctionCounterBit_wire_ne n (k + 1)
          (WireAddress.littleEndianWire
            (paddingCounterSourceHighIndex left hleft)))
    · rw [paddingCounterSourceBit_eq_correction_of_ne_zero n k left hleft,
        paddingCounterSourceBit_eq_correction_of_ne_zero n k right hright]
      apply correctionCounterBit_wire_ne n (k + 1)
      apply littleEndianWire_ne
      intro hindices
      apply hne
      apply Fin.ext
      have hval := congrArg Fin.val hindices
      simp only [paddingCounterSourceHighIndex_val] at hval
      omega

/-- Every borrowed source bit is disjoint from the compact padding counter. -/
lemma paddingCounterSourceBit_paddingCounterValueBit_wire_ne
    (n k : Nat) (sourceBit counterBit : Fin (k + 1)) :
    (paddingCounterSourceBit n k sourceBit).wire ≠
      (paddingCounterValueBit n k counterBit).wire := by
  by_cases hsource : sourceBit.val = 0
  · rw [paddingCounterSourceBit_eq_control_of_zero n k sourceBit hsource]
    exact Ne.symm (by
      simpa [paddingCounterValueBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n (k + 1)
          (RegisterBits.counterBit n (k + 1)
            (WireAddress.littleEndianWire counterBit))
          (sharedControlBit n (k + 1)))
  · rw [paddingCounterSourceBit_eq_correction_of_ne_zero
      n k sourceBit hsource]
    exact Ne.symm (by
      simpa [paddingCounterValueBit, correctionCounterValueBit,
        correctionCounterBit] using
        liftCoreBit_liftSharedBit_wire_ne n (k + 1)
          (RegisterBits.counterBit n (k + 1)
            (WireAddress.littleEndianWire counterBit))
          (sharedCorrectionCounterBit n (k + 1)
            (WireAddress.littleEndianWire
              (paddingCounterSourceHighIndex sourceBit hsource))))

/-- Every borrowed source bit is disjoint from the shared path carry-in. -/
lemma paddingCounterSourceBit_pathBit_wire_ne
    (n k : Nat) (sourceBit : Fin (k + 1)) :
    (paddingCounterSourceBit n k sourceBit).wire ≠
      (pathBit n (k + 1)).wire := by
  by_cases hsource : sourceBit.val = 0
  · rw [paddingCounterSourceBit_eq_control_of_zero n k sourceBit hsource]
    exact Ne.symm (pathBit_controlBit_wire_ne n (k + 1))
  · rw [paddingCounterSourceBit_eq_correction_of_ne_zero
      n k sourceBit hsource]
    exact Ne.symm
      (pathBit_correctionCounterBit_wire_ne n (k + 1)
        (WireAddress.littleEndianWire
          (paddingCounterSourceHighIndex sourceBit hsource)))

/-- Every borrowed source bit is disjoint from every borrowed VBE carry bit. -/
lemma paddingCounterSourceBit_carryWorkBit_wire_ne
    (n k : Nat) (hkn : k ≤ n) (sourceBit : Fin (k + 1))
    (workBit : Fin k) :
    (paddingCounterSourceBit n k sourceBit).wire ≠
      (paddingCounterCarryWorkBit n k hkn workBit).wire := by
  by_cases hsource : sourceBit.val = 0
  · rw [paddingCounterSourceBit_eq_control_of_zero n k sourceBit hsource]
    exact controlBit_coefficientCarryWorkBit_wire_ne n (k + 1)
      (paddingCounterCarryWorkIndex n k hkn workBit)
  · rw [paddingCounterSourceBit_eq_correction_of_ne_zero
      n k sourceBit hsource]
    exact correctionCounterBit_coefficientCarryWorkBit_wire_ne n (k + 1)
      (WireAddress.littleEndianWire
        (paddingCounterSourceHighIndex sourceBit hsource))
      (paddingCounterCarryWorkIndex n k hkn workBit)

/-- Distinct compact padding-counter positions occupy distinct wires. -/
lemma paddingCounterValueBit_wire_ne
    (n k : Nat) {left right : Fin (k + 1)} (hne : left ≠ right) :
    (paddingCounterValueBit n k left).wire ≠
      (paddingCounterValueBit n k right).wire := by
  simpa [paddingCounterValueBit] using
    liftCoreBit_wire_ne n (k + 1)
      (counterValue_counterValue_wire_ne n (k + 1) left right hne)

/-- Each compact padding-counter bit is disjoint from the shared path carry. -/
lemma paddingCounterValueBit_pathBit_wire_ne
    (n k : Nat) (counterBit : Fin (k + 1)) :
    (paddingCounterValueBit n k counterBit).wire ≠
      (pathBit n (k + 1)).wire := by
  simpa [paddingCounterValueBit, pathBit] using
    liftCoreBit_liftSharedBit_wire_ne n (k + 1)
      (RegisterBits.counterBit n (k + 1)
        (WireAddress.littleEndianWire counterBit))
      (sharedPathBit n (k + 1))

/-- Each compact padding-counter bit is disjoint from borrowed VBE carry work. -/
lemma paddingCounterValueBit_carryWorkBit_wire_ne
    (n k : Nat) (hkn : k ≤ n) (counterBit : Fin (k + 1))
    (workBit : Fin k) :
    (paddingCounterValueBit n k counterBit).wire ≠
      (paddingCounterCarryWorkBit n k hkn workBit).wire := by
  simpa [paddingCounterValueBit, paddingCounterCarryWorkBit,
    coefficientCarryWorkBit] using
    liftCoreBit_liftSharedBit_wire_ne n (k + 1)
      (RegisterBits.counterBit n (k + 1)
        (WireAddress.littleEndianWire counterBit))
      (sharedCoefficientCarryWorkBit n (k + 1)
        (paddingCounterCarryWorkIndex n k hkn workBit))

/-- The shared path carry-in is disjoint from each borrowed VBE work bit. -/
lemma pathBit_paddingCounterCarryWorkBit_wire_ne
    (n k : Nat) (hkn : k ≤ n) (workBit : Fin k) :
    (pathBit n (k + 1)).wire ≠
      (paddingCounterCarryWorkBit n k hkn workBit).wire := by
  exact pathBit_coefficientCarryWorkBit_wire_ne n (k + 1)
    (paddingCounterCarryWorkIndex n k hkn workBit)

/-- Distinct borrowed padding-counter carry positions remain distinct in the
larger VBE carry bank. -/
lemma paddingCounterCarryWorkBit_wire_ne
    (n k : Nat) (hkn : k ≤ n) {left right : Fin k} (hne : left ≠ right) :
    (paddingCounterCarryWorkBit n k hkn left).wire ≠
      (paddingCounterCarryWorkBit n k hkn right).wire := by
  apply coefficientCarryWorkBit_wire_ne n (k + 1)
  intro heq
  apply hne
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simpa using hval

/-- VBE-style layout for the borrowed `(k+1)`-bit padding-counter adder. -/
def paddingCounterIncrementLayout (n k : Nat) (hkn : k ≤ n) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n (k + 1)) (k + 1) where
  left := paddingCounterSourceWord n k
  right := paddingCounterValueWord n k
  carryIn := pathBit n (k + 1)
  workCarry := paddingCounterCarryWorkWord n k hkn
  leftLeft_ne := by
    intro i j hij
    exact paddingCounterSourceBit_wire_ne n k hij
  rightRight_ne := by
    intro i j hij
    exact paddingCounterValueBit_wire_ne n k hij
  leftRight_ne := by
    intro i j
    exact paddingCounterSourceBit_paddingCounterValueBit_wire_ne n k i j
  leftCarryIn_ne := by
    intro i
    exact paddingCounterSourceBit_pathBit_wire_ne n k i
  rightCarryIn_ne := by
    intro i
    exact paddingCounterValueBit_pathBit_wire_ne n k i
  leftWork_ne := by
    intro i j
    exact paddingCounterSourceBit_carryWorkBit_wire_ne n k hkn i j
  rightWork_ne := by
    intro i j
    exact paddingCounterValueBit_carryWorkBit_wire_ne n k hkn i j
  carryInWork_ne := by
    intro j
    exact pathBit_paddingCounterCarryWorkBit_wire_ne n k hkn j
  workWork_ne := by
    intro i j hij
    exact paddingCounterCarryWorkBit_wire_ne n k hkn hij

/-- The literal X gate that loads (and later unloads) the borrowed source
word's low control bit. -/
def paddingCounterLiteralOneGate (n k : Nat) :
    EncodedBit.GateSpec (encoding n (k + 1)) :=
  .x (controlBit n (k + 1))

/-- Concrete X--VBE--X gate schedule for the borrowed counter increment. -/
def paddingCounterIncrementGates (n k : Nat) (hkn : k ≤ n) :
    List (EncodedBit.GateSpec (encoding n (k + 1))) :=
  [paddingCounterLiteralOneGate n k] ++
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
      (paddingCounterIncrementLayout n k hkn) ++
    [paddingCounterLiteralOneGate n k]

/-- Actual base-gate program for the borrowed padding-counter increment. -/
def paddingCounterIncrementProgram (n k : Nat) (hkn : k ≤ n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n (k + 1)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (paddingCounterIncrementGates n k hkn)

/-- Folded bit-lens step of the literal X--VBE--X counter schedule. -/
def paddingCounterIncrementStep (n k : Nat) (hkn : k ≤ n) :
    Registers n (k + 1) -> Registers n (k + 1) :=
  EncodedBit.GateSpec.stepList (paddingCounterIncrementGates n k hkn)

/-- The literal compact counter program realizes exactly its folded gate step. -/
lemma paddingCounterIncrement_realizes (n k : Nat) (hkn : k ≤ n) :
    UnitaryCircuit.Realizes (encoding n (k + 1))
      (paddingCounterIncrementProgram n k hkn) environment
      (paddingCounterIncrementStep n k hkn) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (paddingCounterIncrementGates n k hkn)

/-- Exact X coordinate: one literal load and one matching unload. -/
lemma paddingCounterIncrementGates_xMultiplicity_sum
    (n k : Nat) (hkn : k ≤ n) :
    ((paddingCounterIncrementGates n k hkn).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp [paddingCounterIncrementGates, paddingCounterLiteralOneGate,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum]

/-- Exact CNOT coordinate inherited from the `(k+1)`-bit VBE sum pass. -/
lemma paddingCounterIncrementGates_cnotMultiplicity_sum
    (n k : Nat) (hkn : k ≤ n) :
    ((paddingCounterIncrementGates n k hkn).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (k + 1) := by
  simp [paddingCounterIncrementGates, paddingCounterLiteralOneGate,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate inherited from the `k` temporary carry positions. -/
lemma paddingCounterIncrementGates_toffoliMultiplicity_sum
    (n k : Nat) (hkn : k ≤ n) :
    ((paddingCounterIncrementGates n k hkn).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * k := by
  simp [paddingCounterIncrementGates, paddingCounterLiteralOneGate,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum]

/-- Exact physical length of the literal compact counter schedule. -/
lemma paddingCounterIncrementGates_length
    (n k : Nat) (hkn : k ≤ n) :
    (paddingCounterIncrementGates n k hkn).length = 8 * k + 4 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    paddingCounterIncrementGates_xMultiplicity_sum,
    paddingCounterIncrementGates_cnotMultiplicity_sum,
    paddingCounterIncrementGates_toffoliMultiplicity_sum]
  omega

/-- The compiled program retains the exact literal X coordinate. -/
lemma paddingCounterIncrementProgram_x_count
    (n k : Nat) (hkn : k ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (paddingCounterIncrementProgram n k hkn).eventCost = 2 := by
  rw [paddingCounterIncrementProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    paddingCounterIncrementGates_xMultiplicity_sum]

/-- The compiled program retains the exact CNOT coordinate. -/
lemma paddingCounterIncrementProgram_cnot_count
    (n k : Nat) (hkn : k ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (paddingCounterIncrementProgram n k hkn).eventCost = 2 * (k + 1) := by
  rw [paddingCounterIncrementProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    paddingCounterIncrementGates_cnotMultiplicity_sum]

/-- The compiled program retains the exact Toffoli coordinate. -/
lemma paddingCounterIncrementProgram_toffoli_count
    (n k : Nat) (hkn : k ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (paddingCounterIncrementProgram n k hkn).eventCost = 6 * k := by
  rw [paddingCounterIncrementProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    paddingCounterIncrementGates_toffoliMultiplicity_sum]

/-- State after the leading literal X has loaded the source-one low bit. -/
def paddingCounterLoadedInput (n k : Nat)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    Registers n (k + 1) :=
  (controlBit n (k + 1)).flip (paddingCounterCleanInput n k core target)

/-- Expose the literal X--adder--X composition of the compact increment step. -/
lemma paddingCounterIncrementStep_decompose
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1)) :
    paddingCounterIncrementStep n k hkn x =
      (controlBit n (k + 1)).flip
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (paddingCounterIncrementLayout n k hkn)
          ((controlBit n (k + 1)).flip x)) := by
  rw [paddingCounterIncrementStep, paddingCounterIncrementGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

lemma controlBit_get_paddingCounterCleanInput
    (n k : Nat) (core : MK.Registers n (k + 1)) (target : Word n) :
    (controlBit n (k + 1)).get (paddingCounterCleanInput n k core target) =
      false := by
  simp [paddingCounterCleanInput, cleanSharedWork]

lemma pathBit_get_paddingCounterCleanInput
    (n k : Nat) (core : MK.Registers n (k + 1)) (target : Word n) :
    (pathBit n (k + 1)).get (paddingCounterCleanInput n k core target) =
      false := by
  simp [paddingCounterCleanInput, cleanSharedWork]

lemma correctionCounterValueBit_get_paddingCounterCleanInput
    (n k : Nat) (core : MK.Registers n (k + 1)) (target : Word n)
    (bit : Fin k) :
    (correctionCounterValueBit n (k + 1) bit).get
        (paddingCounterCleanInput n k core target) = false := by
  simp [paddingCounterCleanInput, cleanSharedWork]

@[simp] lemma paddingCounterCarryWorkBit_get_paddingCounterCleanInput
    (n k : Nat) (hkn : k ≤ n) (core : MK.Registers n (k + 1))
    (target : Word n) (bit : Fin k) :
    (paddingCounterCarryWorkBit n k hkn bit).get
        (paddingCounterCleanInput n k core target) = false := by
  change
    (BinaryLabelEncoding.finIdentityBit n
      (paddingCounterCarryWorkIndex n k hkn bit)).get
        (PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1)) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n
    (paddingCounterCarryWorkIndex n k hkn bit)

/-- The leading literal X leaves the shared path carry-in clean. -/
lemma pathBit_get_paddingCounterLoadedInput
    (n k : Nat) (core : MK.Registers n (k + 1)) (target : Word n) :
    (pathBit n (k + 1)).get (paddingCounterLoadedInput n k core target) =
      false := by
  rw [paddingCounterLoadedInput]
  rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
    (pathBit n (k + 1)) (Ne.symm (pathBit_controlBit_wire_ne n (k + 1)))]
  exact pathBit_get_paddingCounterCleanInput n k core target

/-- The leading literal X leaves every borrowed VBE carry bit clean. -/
lemma paddingCounterCarryWorkBit_get_paddingCounterLoadedInput
    (n k : Nat) (hkn : k ≤ n) (core : MK.Registers n (k + 1))
    (target : Word n) (bit : Fin k) :
    (paddingCounterCarryWorkBit n k hkn bit).get
        (paddingCounterLoadedInput n k core target) = false := by
  rw [paddingCounterLoadedInput]
  rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
    (paddingCounterCarryWorkBit n k hkn bit)
    (controlBit_coefficientCarryWorkBit_wire_ne n (k + 1)
      (paddingCounterCarryWorkIndex n k hkn bit))]
  exact paddingCounterCarryWorkBit_get_paddingCounterCleanInput
    n k hkn core target bit

/-- After the literal load, the borrowed source word has exact value one. -/
lemma paddingCounterSourceBit_get_paddingCounterLoadedInput
    (n k : Nat) (core : MK.Registers n (k + 1)) (target : Word n)
    (bit : Fin (k + 1)) :
    (paddingCounterSourceBit n k bit).get
        (paddingCounterLoadedInput n k core target) =
      (1 : Word (k + 1)).val.testBit bit.val := by
  by_cases hbit : bit.val = 0
  · rw [paddingCounterSourceBit_eq_control_of_zero n k bit hbit,
      paddingCounterLoadedInput, EncodedBit.get_flip_self,
      controlBit_get_paddingCounterCleanInput]
    simp [hbit]
  · rw [paddingCounterSourceBit_eq_correction_of_ne_zero n k bit hbit,
      paddingCounterLoadedInput]
    rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
      (correctionCounterValueBit n (k + 1)
        (paddingCounterSourceHighIndex bit hbit))]
    · rw [correctionCounterValueBit_get_paddingCounterCleanInput]
      have hone : (1 : Word (k + 1)).val = 1 := by
        change 1 % 2 ^ (k + 1) = 1
        exact Nat.mod_eq_of_lt
          (Nat.one_lt_two_pow (by omega))
      rw [hone]
      exact (Nat.testBit_lt_two_pow
        (Nat.one_lt_two_pow hbit)).symm
    · simpa [correctionCounterValueBit] using
        controlBit_correctionCounterBit_wire_ne n (k + 1)
          (WireAddress.littleEndianWire
            (paddingCounterSourceHighIndex bit hbit))

/-- The literal-load control bit is disjoint from every compact counter bit. -/
lemma controlBit_paddingCounterValueBit_wire_ne
    (n k : Nat) (bit : Fin (k + 1)) :
    (controlBit n (k + 1)).wire ≠
      (paddingCounterValueBit n k bit).wire := by
  exact Ne.symm (by
    simpa [paddingCounterValueBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne n (k + 1)
        (RegisterBits.counterBit n (k + 1)
          (WireAddress.littleEndianWire bit))
        (sharedControlBit n (k + 1)))

/-- On clean borrowed carry work, the forward VBE carry stage computes the
natural addition carries for an arbitrary literal source word. -/
lemma paddingCounter_carryStage_get_workCarry_natAddCarry
    (n k : Nat) (hkn : k ≤ n) (source : Word (k + 1))
    (j : Fin k) (x : Registers n (k + 1))
    (hleft :
      ∀ bit : Fin (k + 1),
        (paddingCounterSourceBit n k bit).get x =
          source.val.testBit bit.val)
    (hcarry : (pathBit n (k + 1)).get x = false)
    (hwork :
      ∀ bit : Fin k,
        (paddingCounterCarryWorkBit n k hkn bit).get x = false) :
    (paddingCounterCarryWorkBit n k hkn j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (paddingCounterIncrementLayout n k hkn) x) =
      Nat.BinaryArithmetic.natAddCarry
        source.val x.core.counter.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (paddingCounterIncrementLayout n k hkn) x
  change (paddingCounterCarryWorkBit n k hkn j).get stage =
    Nat.BinaryArithmetic.natAddCarry
      source.val x.core.counter.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin k, j.val = m ->
      (paddingCounterCarryWorkBit n k hkn j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          source.val x.core.counter.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (paddingCounterIncrementLayout n k hkn) j x hwork
        change (paddingCounterCarryWorkBit n k hkn j).get stage =
          Nat.BinaryArithmetic.natAddCarry
            source.val x.core.counter.val (j.val + 1)
        change
          ((paddingCounterIncrementLayout n k hkn).workCarry.bit j).get
              ((paddingCounterIncrementLayout n k hkn).carryStageIndexStep x) =
            Nat.BinaryArithmetic.natAddCarry
              source.val x.core.counter.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (paddingCounterIncrementLayout n k hkn) x
          rw [hdata]
          have hcarryData : x.shared.path = false := by
            simpa only [pathBit_get] using hcarry
          have hsource := hleft
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)
          have hcounter := paddingCounterValueBit_get n k
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j) x
          change Bool.carry
              ((paddingCounterSourceBit n k
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              ((paddingCounterValueBit n k
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              x.shared.path =
            Nat.BinaryArithmetic.natAddCarry
              source.val x.core.counter.val (j.val + 1)
          rw [hsource, hcounter, hcarryData]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let previous :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex
              (n := k + 1) j hzero
          have hpreviousLt : previous.val < m := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hprevious := ih previous.val hpreviousLt previous rfl
          have hprevious' :
              ((paddingCounterIncrementLayout n k hkn).workCarry.bit previous).get
                  ((paddingCounterIncrementLayout n k hkn).carryStageIndexStep x) =
                Nat.BinaryArithmetic.natAddCarry
                  source.val x.core.counter.val (previous.val + 1) := by
            change (paddingCounterCarryWorkBit n k hkn previous).get
                (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
                  (paddingCounterIncrementLayout n k hkn) x) =
              Nat.BinaryArithmetic.natAddCarry
                source.val x.core.counter.val (previous.val + 1)
            simpa only [stage] using hprevious
          have hpreviousSucc : previous.val + 1 = j.val := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hprevious', hpreviousSucc]
          have hsource := hleft
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)
          have hcounter := paddingCounterValueBit_get n k
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j) x
          change Bool.carry
              ((paddingCounterSourceBit n k
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              ((paddingCounterValueBit n k
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              (Nat.BinaryArithmetic.natAddCarry
                source.val x.core.counter.val j.val) =
            Bool.carry
              (source.val.testBit j.val)
              (x.core.counter.val.testBit j.val)
              (Nat.BinaryArithmetic.natAddCarry
                source.val x.core.counter.val j.val)
          rw [hsource, hcounter]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex]
  exact hmain j.val j rfl

/-- The carry selected before each compact padding-counter target sum is the
corresponding natural addition carry. -/
lemma paddingCounter_carryBeforeSum_get_natAddCarry
    (n k : Nat) (hkn : k ≤ n) (source : Word (k + 1))
    (bit : Fin (k + 1)) (x : Registers n (k + 1))
    (hleft :
      ∀ sourceBit : Fin (k + 1),
        (paddingCounterSourceBit n k sourceBit).get x =
          source.val.testBit sourceBit.val)
    (hcarry : (pathBit n (k + 1)).get x = false)
    (hwork :
      ∀ workBit : Fin k,
        (paddingCounterCarryWorkBit n k hkn workBit).get x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (paddingCounterIncrementLayout n k hkn) bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (paddingCounterIncrementLayout n k hkn) x) =
      Nat.BinaryArithmetic.natAddCarry
        source.val x.core.counter.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (paddingCounterIncrementLayout n k hkn) x
    rw [hdata]
    have hcarryData : x.shared.path = false := by
      simpa only [pathBit_get] using hcarry
    simp [paddingCounterIncrementLayout, hcarryData,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hworkLt : bit.val - 1 < k := by
      have hbit := bit.isLt
      omega
    let workBit : Fin k := ⟨bit.val - 1, hworkLt⟩
    have hworkCarry :=
      paddingCounter_carryStage_get_workCarry_natAddCarry
        n k hkn source workBit x hleft hcarry hwork
    have hworkSucc : workBit.val + 1 = bit.val := by
      dsimp [workBit]
      omega
    change
      (paddingCounterCarryWorkBit n k hkn workBit).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (paddingCounterIncrementLayout n k hkn) x) =
        Nat.BinaryArithmetic.natAddCarry
          source.val x.core.counter.val bit.val
    rw [hworkCarry, hworkSucc]

/-- On clean borrowed workspace, the VBE substep writes each compact counter
bit as the corresponding bit of `counter + 1`. -/
lemma paddingCounterAdderStep_get_counter_add_testBit_of_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n)
    (bit : Fin (k + 1)) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
      (paddingCounterIncrementLayout n k hkn)
      (paddingCounterLoadedInput n k core target)).core.counter.val.testBit
        bit.val =
      (core.counter + (1 : Word (k + 1))).val.testBit bit.val := by
  let input := paddingCounterLoadedInput n k core target
  have hright :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (paddingCounterIncrementLayout n k hkn) bit input
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hright
  have hcarry : (pathBit n (k + 1)).get input = false := by
    simpa only [input] using
      pathBit_get_paddingCounterLoadedInput n k core target
  have hwork :
      ∀ workBit : Fin k,
        (paddingCounterCarryWorkBit n k hkn workBit).get input = false := by
    intro workBit
    simpa only [input] using
      paddingCounterCarryWorkBit_get_paddingCounterLoadedInput
        n k hkn core target workBit
  have hsource :
      ∀ sourceBit : Fin (k + 1),
        (paddingCounterSourceBit n k sourceBit).get input =
          (1 : Word (k + 1)).val.testBit sourceBit.val := by
    intro sourceBit
    simpa only [input] using
      paddingCounterSourceBit_get_paddingCounterLoadedInput
        n k core target sourceBit
  have hinputCounter : input.core.counter = core.counter := by
    apply word_eq_of_testBit_eq
    intro counterBit
    rw [← paddingCounterValueBit_get n k counterBit input]
    simp only [input]
    rw [paddingCounterLoadedInput]
    rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
      (paddingCounterValueBit n k counterBit)
      (controlBit_paddingCounterValueBit_wire_ne n k counterBit)]
    exact paddingCounterValueBit_get n k counterBit
      (paddingCounterCleanInput n k core target)
  have hcarryBit :=
    paddingCounter_carryBeforeSum_get_natAddCarry
      n k hkn (1 : Word (k + 1)) bit input hsource hcarry hwork
  rw [hcarryBit] at hright
  rw [hinputCounter] at hright
  calc
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
      (paddingCounterIncrementLayout n k hkn) input).core.counter.val.testBit
        bit.val =
        ((core.counter.val.testBit bit.val ^^
            (1 : Word (k + 1)).val.testBit bit.val) ^^
          Nat.BinaryArithmetic.natAddCarry
            (1 : Word (k + 1)).val core.counter.val bit.val) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        paddingCounterIncrementLayout, paddingCounterValueWord,
        paddingCounterSourceWord, paddingCounterValueBit_get,
        hsource, hinputCounter, Bool.xor_assoc] using hright
    _ = (core.counter + (1 : Word (k + 1))).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using
        (word_add_testBit_eq_xor3 (k + 1)
          (1 : Word (k + 1)) core.counter bit).symm

/-- The full literal X--VBE--X compact step increments the padding counter
modulo its fixed width. -/
lemma paddingCounterIncrementStep_get_counter_add_testBit_of_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n)
    (bit : Fin (k + 1)) :
  (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).core.counter.val.testBit
        bit.val =
      (core.counter + (1 : Word (k + 1))).val.testBit bit.val := by
  rw [← paddingCounterValueBit_get n k bit]
  rw [paddingCounterIncrementStep_decompose]
  rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
    (paddingCounterValueBit n k bit)
    (controlBit_paddingCounterValueBit_wire_ne n k bit)]
  rw [paddingCounterValueBit_get]
  exact paddingCounterAdderStep_get_counter_add_testBit_of_clean
    n k hkn core target bit

/-- Counter-level semantic endpoint for the compact borrowed increment. -/
lemma paddingCounterIncrementStep_counter_of_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).core.counter =
      wordIncrement (k + 1) core.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [paddingCounterIncrementStep_get_counter_add_testBit_of_clean]
  rw [word_add_one_eq_wordIncrement]

/-- Every observation outside the compact counter targets, borrowed VBE carry
prefix, and literal control wire is preserved by the complete X--VBE--X
schedule.  This is the reusable non-interference certificate for the rest of
the compact carrier. -/
lemma paddingCounterIncrementStep_get_observed_of_disjoint
    (n k : Nat) (hkn : k ≤ n)
    (observed : EncodedBit (encoding n (k + 1)))
    (hright : ∀ bit : Fin (k + 1),
      (paddingCounterValueBit n k bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin k,
      (paddingCounterCarryWorkBit n k hkn bit).wire ≠ observed.wire)
    (hcontrol : (controlBit n (k + 1)).wire ≠ observed.wire)
    (x : Registers n (k + 1)) :
    observed.get (paddingCounterIncrementStep n k hkn x) = observed.get x := by
  rw [paddingCounterIncrementStep_decompose]
  rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1)) observed hcontrol]
  have hadder :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (paddingCounterIncrementLayout n k hkn) observed hright hwork
      ((controlBit n (k + 1)).flip x)
  calc
    observed.get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (paddingCounterIncrementLayout n k hkn)
          ((controlBit n (k + 1)).flip x)) =
        observed.get ((controlBit n (k + 1)).flip x) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using hadder
    _ = observed.get x :=
      EncodedBit.get_flip_of_wire_ne
        (controlBit n (k + 1)) observed hcontrol x

/-- A nonzero bit of the `(k+1)`-bit literal-one word is false. -/
lemma oneWord_testBit_eq_false_of_ne_zero
    (k : Nat) (bit : Fin (k + 1)) (hbit : bit.val ≠ 0) :
    (1 : Word (k + 1)).val.testBit bit.val = false := by
  have hone : (1 : Word (k + 1)).val = 1 := by
    change 1 % 2 ^ (k + 1) = 1
    exact Nat.mod_eq_of_lt
      (Nat.one_lt_two_pow (by omega))
  rw [hone]
  exact Nat.testBit_lt_two_pow
    (Nat.one_lt_two_pow hbit)

/-- The literal load makes its shared control source bit true. -/
lemma controlBit_get_paddingCounterLoadedInput
    (n k : Nat) (core : MK.Registers n (k + 1)) (target : Word n) :
    (controlBit n (k + 1)).get
        (paddingCounterLoadedInput n k core target) = true := by
  rw [paddingCounterLoadedInput, EncodedBit.get_flip_self,
    controlBit_get_paddingCounterCleanInput]
  rfl

/-- The source word borrowed for literal one is returned clean after the
matching unload X. -/
lemma paddingCounterIncrementStep_get_sourceBit_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n)
    (bit : Fin (k + 1)) :
    (paddingCounterSourceBit n k bit).get
        (paddingCounterIncrementStep n k hkn
          (paddingCounterCleanInput n k core target)) = false := by
  let loaded := paddingCounterLoadedInput n k core target
  have hleft :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (paddingCounterIncrementLayout n k hkn) bit loaded
  have hleftClean :
      (paddingCounterSourceBit n k bit).get
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
            (paddingCounterIncrementLayout n k hkn) loaded) =
        (paddingCounterSourceBit n k bit).get loaded := by
    simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
      paddingCounterIncrementLayout, paddingCounterSourceWord] using hleft
  rw [paddingCounterIncrementStep_decompose]
  change (paddingCounterSourceBit n k bit).get
      ((controlBit n (k + 1)).flip
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (paddingCounterIncrementLayout n k hkn) loaded)) = false
  by_cases hzero : bit.val = 0
  · rw [paddingCounterSourceBit_eq_control_of_zero n k bit hzero]
    rw [EncodedBit.get_flip_self]
    rw [paddingCounterSourceBit_eq_control_of_zero n k bit hzero] at hleftClean
    rw [hleftClean]
    rw [show (controlBit n (k + 1)).get loaded = true by
      simpa only [loaded] using
        controlBit_get_paddingCounterLoadedInput n k core target]
    rfl
  · have hcontrolSource :
        (controlBit n (k + 1)).wire ≠
          (paddingCounterSourceBit n k bit).wire := by
      rw [paddingCounterSourceBit_eq_correction_of_ne_zero n k bit hzero]
      exact controlBit_correctionCounterBit_wire_ne n (k + 1)
        (WireAddress.littleEndianWire
          (paddingCounterSourceHighIndex bit hzero))
    rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
      (paddingCounterSourceBit n k bit) hcontrolSource]
    rw [hleftClean]
    calc
      (paddingCounterSourceBit n k bit).get loaded =
          (1 : Word (k + 1)).val.testBit bit.val := by
        simpa only [loaded] using
          paddingCounterSourceBit_get_paddingCounterLoadedInput
            n k core target bit
      _ = false := oneWord_testBit_eq_false_of_ne_zero k bit hzero

/-- The shared path carry-in is returned clean by the compact increment. -/
lemma paddingCounterIncrementStep_get_path_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (pathBit n (k + 1)).get
        (paddingCounterIncrementStep n k hkn
          (paddingCounterCleanInput n k core target)) = false := by
  let loaded := paddingCounterLoadedInput n k core target
  rw [paddingCounterIncrementStep_decompose]
  change (pathBit n (k + 1)).get
      ((controlBit n (k + 1)).flip
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (paddingCounterIncrementLayout n k hkn) loaded)) = false
  rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
    (pathBit n (k + 1))
    (Ne.symm (pathBit_controlBit_wire_ne n (k + 1)))]
  have hcarry :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (paddingCounterIncrementLayout n k hkn) loaded
  calc
    (pathBit n (k + 1)).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (paddingCounterIncrementLayout n k hkn) loaded) =
        (pathBit n (k + 1)).get loaded := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        paddingCounterIncrementLayout] using hcarry
    _ = false := by
      simpa only [loaded] using
        pathBit_get_paddingCounterLoadedInput n k core target

/-- Every borrowed VBE carry-prefix bit is uncomputed back to clean. -/
lemma paddingCounterIncrementStep_get_carryWork_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n)
    (bit : Fin k) :
    (paddingCounterCarryWorkBit n k hkn bit).get
        (paddingCounterIncrementStep n k hkn
          (paddingCounterCleanInput n k core target)) = false := by
  let loaded := paddingCounterLoadedInput n k core target
  rw [paddingCounterIncrementStep_decompose]
  change (paddingCounterCarryWorkBit n k hkn bit).get
      ((controlBit n (k + 1)).flip
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (paddingCounterIncrementLayout n k hkn) loaded)) = false
  rw [EncodedBit.get_flip_of_wire_ne (controlBit n (k + 1))
    (paddingCounterCarryWorkBit n k hkn bit)
    (controlBit_coefficientCarryWorkBit_wire_ne n (k + 1)
      (paddingCounterCarryWorkIndex n k hkn bit))]
  have hwork :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (paddingCounterIncrementLayout n k hkn) bit loaded (by
        intro workBit
        simpa [paddingCounterIncrementLayout, paddingCounterCarryWorkWord,
          loaded] using
          paddingCounterCarryWorkBit_get_paddingCounterLoadedInput
            n k hkn core target workBit)
  simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    paddingCounterIncrementLayout, paddingCounterCarryWorkWord] using hwork

/-- The shared literal-load control is restored to its clean value. -/
lemma paddingCounterIncrementStep_control_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared.control = false := by
  have hsource := paddingCounterIncrementStep_get_sourceBit_clean
    n k hkn core target (0 : Fin (k + 1))
  rw [paddingCounterSourceBit_eq_control_of_zero n k
    (0 : Fin (k + 1)) (by rfl)] at hsource
  simpa only [controlBit_get] using hsource

/-- The borrowed high source bits return the correction counter to zero. -/
lemma paddingCounterIncrementStep_correctionCounter_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared.correctionCounter = 0 := by
  apply word_eq_of_testBit_eq
  intro bit
  let sourceBit : Fin (k + 1) := Fin.succ bit
  have hsource := paddingCounterIncrementStep_get_sourceBit_clean
    n k hkn core target sourceBit
  have hnonzero : sourceBit.val ≠ 0 := by
    dsimp [sourceBit]
    omega
  rw [paddingCounterSourceBit_eq_correction_of_ne_zero
    n k sourceBit hnonzero] at hsource
  have hindex : paddingCounterSourceHighIndex sourceBit hnonzero = bit := by
    apply Fin.ext
    dsimp [sourceBit, paddingCounterSourceHighIndex]
  rw [hindex] at hsource
  simpa [correctionCounterValueBit_get] using hsource

/-- The shared path carry-in returns to its clean field value. -/
lemma paddingCounterIncrementStep_path_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared.path = false := by
  simpa only [pathBit_get] using
    paddingCounterIncrementStep_get_path_clean n k hkn core target

/-- The compact increment leaves the public target word untouched. -/
lemma paddingCounterIncrementStep_target_cleanEndpoint
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).target = target := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := paddingCounterIncrementStep_get_observed_of_disjoint
    n k hkn (targetValueBit n (k + 1) bit)
    (fun counterBit => by
      simpa [paddingCounterValueBit, targetValueBit] using
        liftCoreBit_targetBit_wire_ne n (k + 1)
          (RegisterBits.counterBit n (k + 1)
            (WireAddress.littleEndianWire counterBit))
          (WireAddress.littleEndianWire bit))
    (fun workBit => by
      simpa [paddingCounterCarryWorkBit, targetValueBit,
        coefficientCarryWorkBit] using
        liftSharedBit_targetBit_wire_ne n (k + 1)
          (sharedCoefficientCarryWorkBit n (k + 1)
            (paddingCounterCarryWorkIndex n k hkn workBit))
          (WireAddress.littleEndianWire bit))
    (by
      simpa [controlBit, targetValueBit] using
        liftSharedBit_targetBit_wire_ne n (k + 1)
          (sharedControlBit n (k + 1))
          (WireAddress.littleEndianWire bit))
    (paddingCounterCleanInput n k core target)
  simpa only [targetValueBit_get, paddingCounterCleanInput] using h

/-- The VBE carry-in bit is outside the compact counter borrow set and remains
clean from the clean shared-work input. -/
lemma paddingCounterIncrementStep_coefficientCarryIn_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared.coefficientAdder.1 =
      false := by
  have h := paddingCounterIncrementStep_get_observed_of_disjoint
    n k hkn (coefficientCarryInBit n (k + 1))
    (fun counterBit => by
      simpa [paddingCounterValueBit] using
        liftCoreBit_coefficientCarryInBit_wire_ne n (k + 1)
          (RegisterBits.counterBit n (k + 1)
            (WireAddress.littleEndianWire counterBit)))
    (fun workBit => by
      simpa [paddingCounterCarryWorkBit] using
        Ne.symm
          (coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
            n (k + 1)
            (paddingCounterCarryWorkIndex n k hkn workBit)))
    (controlBit_coefficientCarryInBit_wire_ne n (k + 1))
    (paddingCounterCleanInput n k core target)
  simpa [paddingCounterCleanInput, cleanSharedWork, cleanCoeffAdderWork] using h

/-- Every coefficient-carry-bank bit is clean after the compact increment:
the borrowed prefix is explicitly uncomputed, while the untouched suffix is
covered by the generic disjoint-observation theorem. -/
lemma paddingCounterIncrementStep_coefficientCarryWork_clean
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n)
    (bit : Fin n) :
    (coefficientCarryWorkBit n (k + 1) bit).get
        (paddingCounterIncrementStep n k hkn
          (paddingCounterCleanInput n k core target)) = false := by
  by_cases hprefix : bit.val < k
  · let prefixBit : Fin k := ⟨bit.val, hprefix⟩
    have hindex : paddingCounterCarryWorkIndex n k hkn prefixBit = bit := by
      apply Fin.ext
      rfl
    have hclean := paddingCounterIncrementStep_get_carryWork_clean
      n k hkn core target prefixBit
    simpa [paddingCounterCarryWorkBit, hindex] using hclean
  · have h := paddingCounterIncrementStep_get_observed_of_disjoint
      n k hkn (coefficientCarryWorkBit n (k + 1) bit)
      (fun counterBit => by
        simpa [paddingCounterValueBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne n (k + 1)
            (RegisterBits.counterBit n (k + 1)
              (WireAddress.littleEndianWire counterBit)) bit)
      (fun workBit => by
        have hne : paddingCounterCarryWorkIndex n k hkn workBit ≠ bit := by
          intro heq
          have hval := congrArg Fin.val heq
          simp only [paddingCounterCarryWorkIndex_val] at hval
          omega
        simpa [paddingCounterCarryWorkBit] using
          coefficientCarryWorkBit_wire_ne n (k + 1) hne)
      (controlBit_coefficientCarryWorkBit_wire_ne n (k + 1) bit)
      (paddingCounterCleanInput n k core target)
    calc
      (coefficientCarryWorkBit n (k + 1) bit).get
          (paddingCounterIncrementStep n k hkn
            (paddingCounterCleanInput n k core target)) =
          (coefficientCarryWorkBit n (k + 1) bit).get
            (paddingCounterCleanInput n k core target) := h
      _ = false := by
        change (BinaryLabelEncoding.finIdentityBit n bit).get
            (PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1)) = false
        exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit

/-- The full reusable VBE coefficient-adder workspace is again clean at the
compact counter endpoint, including the carry-bank suffix it did not borrow. -/
lemma paddingCounterIncrementStep_coefficientAdder_cleanEndpoint
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  change (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared.coefficientAdder =
      (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1))
  apply Prod.ext
  · exact paddingCounterIncrementStep_coefficientCarryIn_clean
      n k hkn core target
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    change (coefficientCarryWorkBit n (k + 1) bit).get
        (paddingCounterIncrementStep n k hkn
          (paddingCounterCleanInput n k core target)) = false
    exact paddingCounterIncrementStep_coefficientCarryWork_clean
      n k hkn core target bit

/-- The complete shared workspace, not only the borrowed prefix, is restored
to `cleanSharedWork` after the compact padding-counter increment. -/
lemma paddingCounterIncrementStep_shared_cleanEndpoint
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
  (paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared =
      cleanSharedWork n (k + 1) := by
  apply (sharedWorkTupleEquiv n (k + 1)).injective
  change
    ((paddingCounterIncrementStep n k hkn
      (paddingCounterCleanInput n k core target)).shared.coefficientAdder,
      ((paddingCounterIncrementStep n k hkn
        (paddingCounterCleanInput n k core target)).shared.correctionCounter,
        ((paddingCounterIncrementStep n k hkn
          (paddingCounterCleanInput n k core target)).shared.path,
          (paddingCounterIncrementStep n k hkn
            (paddingCounterCleanInput n k core target)).shared.control))) =
      (cleanCoeffAdderWork n, (0, (false, false)))
  apply Prod.ext
  · exact paddingCounterIncrementStep_coefficientAdder_cleanEndpoint
      n k hkn core target
  · apply Prod.ext
    · exact paddingCounterIncrementStep_correctionCounter_clean
        n k hkn core target
    · apply Prod.ext
      · exact paddingCounterIncrementStep_path_clean n k hkn core target
      · exact paddingCounterIncrementStep_control_clean n k hkn core target

/-- The portion of the compact shared carrier borrowed by a padding-counter
increment is clean exactly when its source, carry-in, and VBE carry prefix are
all clean. -/
def PaddingCounterBorrowedClean (n k : Nat) (hkn : k ≤ n)
    (x : Registers n (k + 1)) : Prop :=
  x.shared.correctionCounter = 0 ∧
  x.shared.control = false ∧
  x.shared.path = false ∧
  (∀ bit : Fin k,
    (paddingCounterCarryWorkBit n k hkn bit).get x = false)

/-- Clean endpoint for the whole borrowed counter workspace. -/
lemma paddingCounterIncrementStep_borrowedCleanEndpoint
    (n k : Nat) (hkn : k ≤ n)
    (core : MK.Registers n (k + 1)) (target : Word n) :
    PaddingCounterBorrowedClean n k hkn
      (paddingCounterIncrementStep n k hkn
        (paddingCounterCleanInput n k core target)) := by
  exact ⟨paddingCounterIncrementStep_correctionCounter_clean
      n k hkn core target,
    paddingCounterIncrementStep_control_clean n k hkn core target,
    paddingCounterIncrementStep_path_clean n k hkn core target,
    fun bit => paddingCounterIncrementStep_get_carryWork_clean
      n k hkn core target bit⟩

/-! ## Compact inactive-counter increment -/

/-- The compact active flag, borrowed as the low source bit while incrementing
the fixed-round counter on inactive rounds. -/
def inactiveCounterActiveBit (n k : Nat) :
    EncodedBit (encoding n (k + 1)) :=
  liftCoreBit n (k + 1) (RegisterBits.activeBit n (k + 1))

@[simp] lemma inactiveCounterActiveBit_get
    (n k : Nat) (x : Registers n (k + 1)) :
    (inactiveCounterActiveBit n k).get x = x.core.active := by
  simpa [inactiveCounterActiveBit] using
    RegisterBits.activeBit_get n (k + 1) x.core

/-- The temporary source word for the inactive-counter increment.  The leading
and trailing X gates make its low bit `!active`; its high bits borrow the clean
correction counter. -/
def inactiveCounterSourceBit (n k : Nat) (bit : Fin (k + 1)) :
    EncodedBit (encoding n (k + 1)) :=
  if hbit : bit.val = 0 then inactiveCounterActiveBit n k
  else correctionCounterValueBit n (k + 1)
    (paddingCounterSourceHighIndex bit hbit)

/-- The temporary source word for the inactive-counter VBE addition. -/
def inactiveCounterSourceWord (n k : Nat) :
    EncodedBit.Word (encoding n (k + 1)) (k + 1) where
  bit := inactiveCounterSourceBit n k

@[simp] lemma inactiveCounterSourceBit_eq_active_of_zero
    (n k : Nat) (bit : Fin (k + 1)) (hbit : bit.val = 0) :
    inactiveCounterSourceBit n k bit = inactiveCounterActiveBit n k := by
  simp [inactiveCounterSourceBit, hbit]

@[simp] lemma inactiveCounterSourceBit_eq_correction_of_ne_zero
    (n k : Nat) (bit : Fin (k + 1)) (hbit : bit.val ≠ 0) :
    inactiveCounterSourceBit n k bit =
      correctionCounterValueBit n (k + 1)
        (paddingCounterSourceHighIndex bit hbit) := by
  simp [inactiveCounterSourceBit, hbit]

/-- The active source bit is disjoint from every correction-counter bit. -/
lemma inactiveCounterActiveBit_correctionCounterValueBit_wire_ne
    (n k : Nat) (bit : Fin k) :
    (inactiveCounterActiveBit n k).wire ≠
      (correctionCounterValueBit n (k + 1) bit).wire := by
  simpa [inactiveCounterActiveBit, correctionCounterValueBit,
    correctionCounterBit] using
    liftCoreBit_liftSharedBit_wire_ne n (k + 1)
      (RegisterBits.activeBit n (k + 1))
      (sharedCorrectionCounterBit n (k + 1)
        (WireAddress.littleEndianWire bit))

/-- A correction-counter source bit is disjoint from the VBE carry-in bit. -/
private lemma correctionCounterValueBit_coefficientCarryInBit_wire_ne
    (n k : Nat) (bit : Fin k) :
    (correctionCounterValueBit n (k + 1) bit).wire ≠
      (coefficientCarryInBit n (k + 1)).wire := by
  apply Fin.ne_of_val_ne
  simp [correctionCounterValueBit, correctionCounterBit,
    sharedCorrectionCounterBit, rawCorrectionCounterBit,
    coefficientCarryInBit, sharedCoefficientCarryInBit,
    rawCoefficientCarryInBit, liftSharedBit, rawSharedBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding, wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.boolBit, EncodedBit.relabel]

/-- Distinct temporary source positions occupy distinct compact wires. -/
lemma inactiveCounterSourceBit_wire_ne
    (n k : Nat) {left right : Fin (k + 1)} (hne : left ≠ right) :
    (inactiveCounterSourceBit n k left).wire ≠
      (inactiveCounterSourceBit n k right).wire := by
  by_cases hleft : left.val = 0
  · have hright : right.val ≠ 0 := by
      intro hright
      apply hne
      apply Fin.ext
      omega
    rw [inactiveCounterSourceBit_eq_active_of_zero n k left hleft,
      inactiveCounterSourceBit_eq_correction_of_ne_zero n k right hright]
    exact inactiveCounterActiveBit_correctionCounterValueBit_wire_ne
      n k (paddingCounterSourceHighIndex right hright)
  · by_cases hright : right.val = 0
    · rw [inactiveCounterSourceBit_eq_correction_of_ne_zero n k left hleft,
        inactiveCounterSourceBit_eq_active_of_zero n k right hright]
      exact Ne.symm
        (inactiveCounterActiveBit_correctionCounterValueBit_wire_ne
          n k (paddingCounterSourceHighIndex left hleft))
    · rw [inactiveCounterSourceBit_eq_correction_of_ne_zero n k left hleft,
        inactiveCounterSourceBit_eq_correction_of_ne_zero n k right hright]
      apply correctionCounterBit_wire_ne n (k + 1)
      apply littleEndianWire_ne
      intro hindices
      apply hne
      apply Fin.ext
      have hval := congrArg Fin.val hindices
      simp only [paddingCounterSourceHighIndex_val] at hval
      omega

/-- Every inactive-counter source bit is disjoint from every counter target
bit. -/
lemma inactiveCounterSourceBit_paddingCounterValueBit_wire_ne
    (n k : Nat) (sourceBit counterBit : Fin (k + 1)) :
    (inactiveCounterSourceBit n k sourceBit).wire ≠
      (paddingCounterValueBit n k counterBit).wire := by
  by_cases hsource : sourceBit.val = 0
  · rw [inactiveCounterSourceBit_eq_active_of_zero n k sourceBit hsource]
    simpa [inactiveCounterActiveBit, paddingCounterValueBit] using
      liftCoreBit_wire_ne n (k + 1)
        (RegisterBits.active_counter_wire_ne n (k + 1)
          (WireAddress.littleEndianWire counterBit))
  · rw [inactiveCounterSourceBit_eq_correction_of_ne_zero
      n k sourceBit hsource]
    simpa [paddingCounterSourceBit, hsource] using
      paddingCounterSourceBit_paddingCounterValueBit_wire_ne
        n k sourceBit counterBit

/-- Every source bit is disjoint from the borrowed VBE carry prefix. -/
lemma inactiveCounterSourceBit_paddingCounterCarryWorkBit_wire_ne
    (n k : Nat) (hkn : k ≤ n) (sourceBit : Fin (k + 1))
    (workBit : Fin k) :
    (inactiveCounterSourceBit n k sourceBit).wire ≠
      (paddingCounterCarryWorkBit n k hkn workBit).wire := by
  by_cases hsource : sourceBit.val = 0
  · rw [inactiveCounterSourceBit_eq_active_of_zero n k sourceBit hsource]
    simpa [inactiveCounterActiveBit, paddingCounterCarryWorkBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n (k + 1)
        (RegisterBits.activeBit n (k + 1))
        (paddingCounterCarryWorkIndex n k hkn workBit)
  · rw [inactiveCounterSourceBit_eq_correction_of_ne_zero
      n k sourceBit hsource]
    exact correctionCounterBit_coefficientCarryWorkBit_wire_ne n (k + 1)
      (WireAddress.littleEndianWire
        (paddingCounterSourceHighIndex sourceBit hsource))
      (paddingCounterCarryWorkIndex n k hkn workBit)

/-- Every source bit is disjoint from the coefficient-adder carry-in. -/
lemma inactiveCounterSourceBit_coefficientCarryInBit_wire_ne
    (n k : Nat) (sourceBit : Fin (k + 1)) :
    (inactiveCounterSourceBit n k sourceBit).wire ≠
      (coefficientCarryInBit n (k + 1)).wire := by
  by_cases hsource : sourceBit.val = 0
  · rw [inactiveCounterSourceBit_eq_active_of_zero n k sourceBit hsource]
    simpa [inactiveCounterActiveBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne n (k + 1)
        (RegisterBits.activeBit n (k + 1))
  · rw [inactiveCounterSourceBit_eq_correction_of_ne_zero
      n k sourceBit hsource]
    exact correctionCounterValueBit_coefficientCarryInBit_wire_ne
      n k (paddingCounterSourceHighIndex sourceBit hsource)

/-- The active low source bit is disjoint from the counter target word. -/
lemma inactiveCounterActiveBit_paddingCounterValueBit_wire_ne
    (n k : Nat) (bit : Fin (k + 1)) :
    (inactiveCounterActiveBit n k).wire ≠
      (paddingCounterValueBit n k bit).wire := by
  simpa [inactiveCounterActiveBit, paddingCounterValueBit] using
    liftCoreBit_wire_ne n (k + 1)
      (RegisterBits.active_counter_wire_ne n (k + 1)
        (WireAddress.littleEndianWire bit))

/-- The active low source bit is disjoint from each borrowed VBE carry bit. -/
lemma inactiveCounterActiveBit_paddingCounterCarryWorkBit_wire_ne
    (n k : Nat) (hkn : k ≤ n) (bit : Fin k) :
    (inactiveCounterActiveBit n k).wire ≠
      (paddingCounterCarryWorkBit n k hkn bit).wire := by
  simpa [inactiveCounterActiveBit, paddingCounterCarryWorkBit] using
    liftCoreBit_coefficientCarryWorkBit_wire_ne n (k + 1)
      (RegisterBits.activeBit n (k + 1))
      (paddingCounterCarryWorkIndex n k hkn bit)

/-- VBE layout for adding the temporary `!active` source into the compact
counter.  It borrows only the correction counter and the prefix of the single
shared coefficient-adder carry bank. -/
def inactiveCounterIncrementLayout (n k : Nat) (hkn : k ≤ n) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n (k + 1)) (k + 1) where
  left := inactiveCounterSourceWord n k
  right := paddingCounterValueWord n k
  carryIn := coefficientCarryInBit n (k + 1)
  workCarry := paddingCounterCarryWorkWord n k hkn
  leftLeft_ne := by
    intro i j hij
    exact inactiveCounterSourceBit_wire_ne n k hij
  rightRight_ne := by
    intro i j hij
    exact paddingCounterValueBit_wire_ne n k hij
  leftRight_ne := by
    intro i j
    exact inactiveCounterSourceBit_paddingCounterValueBit_wire_ne n k i j
  leftCarryIn_ne := by
    intro i
    exact inactiveCounterSourceBit_coefficientCarryInBit_wire_ne n k i
  rightCarryIn_ne := by
    intro i
    simpa [paddingCounterValueWord, paddingCounterValueBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne n (k + 1)
        (RegisterBits.counterBit n (k + 1)
          (WireAddress.littleEndianWire i))
  leftWork_ne := by
    intro i j
    exact inactiveCounterSourceBit_paddingCounterCarryWorkBit_wire_ne
      n k hkn i j
  rightWork_ne := by
    intro i j
    exact paddingCounterValueBit_carryWorkBit_wire_ne n k hkn i j
  carryInWork_ne := by
    intro j
    exact coefficientCarryInBit_coefficientCarryWorkBit_wire_ne n (k + 1)
      (paddingCounterCarryWorkIndex n k hkn j)
  workWork_ne := by
    intro i j hij
    exact paddingCounterCarryWorkBit_wire_ne n k hkn hij

/-- The temporary X gate converting the active bit into the inactive source
literal before (and after) the VBE pass. -/
def inactiveCounterLiteralGate (n k : Nat) :
    EncodedBit.GateSpec (encoding n (k + 1)) :=
  .x (inactiveCounterActiveBit n k)

/-- Concrete X--VBE--X schedule for an inactive compact counter increment. -/
def inactiveCounterIncrementGates (n k : Nat) (hkn : k ≤ n) :
    List (EncodedBit.GateSpec (encoding n (k + 1))) :=
  [inactiveCounterLiteralGate n k] ++
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
      (inactiveCounterIncrementLayout n k hkn) ++
    [inactiveCounterLiteralGate n k]

/-- The inactive-counter source word is disjoint from every public target bit. -/
lemma inactiveCounterSourceBit_targetValueBit_wire_ne
    (n k : Nat) (source : Fin (k + 1)) (target : Fin n) :
    (inactiveCounterSourceBit n k source).wire ≠
      (targetValueBit n (k + 1) target).wire := by
  by_cases hsource : source.val = 0
  · rw [inactiveCounterSourceBit_eq_active_of_zero n k source hsource]
    simpa [inactiveCounterActiveBit, targetValueBit] using
      liftCoreBit_targetBit_wire_ne n (k + 1)
        (RegisterBits.activeBit n (k + 1))
        (WireAddress.littleEndianWire target)
  · rw [inactiveCounterSourceBit_eq_correction_of_ne_zero n k source hsource]
    simpa [correctionCounterValueBit, correctionCounterBit, targetValueBit] using
      liftSharedBit_targetBit_wire_ne n (k + 1)
        (sharedCorrectionCounterBit n (k + 1)
          (WireAddress.littleEndianWire
            (paddingCounterSourceHighIndex source hsource)))
        (WireAddress.littleEndianWire target)

/-- The inactive-counter target word is disjoint from every public target bit. -/
lemma paddingCounterValueBit_targetValueBit_wire_ne
    (n k : Nat) (counter : Fin (k + 1)) (target : Fin n) :
    (paddingCounterValueBit n k counter).wire ≠
      (targetValueBit n (k + 1) target).wire := by
  simpa [paddingCounterValueBit, targetValueBit] using
    liftCoreBit_targetBit_wire_ne n (k + 1)
      (RegisterBits.counterBit n (k + 1)
        (WireAddress.littleEndianWire counter))
      (WireAddress.littleEndianWire target)

/-- Every borrowed inactive-counter carry bit is disjoint from every public
target bit. -/
lemma paddingCounterCarryWorkBit_targetValueBit_wire_ne
    (n k : Nat) (hkn : k ≤ n) (work : Fin k) (target : Fin n) :
    (paddingCounterCarryWorkBit n k hkn work).wire ≠
      (targetValueBit n (k + 1) target).wire := by
  simpa [paddingCounterCarryWorkBit, coefficientCarryWorkBit, targetValueBit] using
    liftSharedBit_targetBit_wire_ne n (k + 1)
      (sharedCoefficientCarryWorkBit n (k + 1)
        (paddingCounterCarryWorkIndex n k hkn work))
      (WireAddress.littleEndianWire target)

/-- The borrowed VBE carry-in is disjoint from every public target bit. -/
lemma coefficientCarryInBit_targetValueBit_wire_ne
    (n k : Nat) (target : Fin n) :
    (coefficientCarryInBit n (k + 1)).wire ≠
      (targetValueBit n (k + 1) target).wire := by
  simpa [coefficientCarryInBit, targetValueBit] using
    liftSharedBit_targetBit_wire_ne n (k + 1)
      (sharedCoefficientCarryInBit n (k + 1))
      (WireAddress.littleEndianWire target)

/-- The temporary inactive source bit is disjoint from every public target bit. -/
lemma inactiveCounterActiveBit_targetValueBit_wire_ne
    (n k : Nat) (target : Fin n) :
    (inactiveCounterActiveBit n k).wire ≠
      (targetValueBit n (k + 1) target).wire := by
  simpa [inactiveCounterActiveBit, targetValueBit] using
    liftCoreBit_targetBit_wire_ne n (k + 1)
      (RegisterBits.activeBit n (k + 1))
      (WireAddress.littleEndianWire target)

/-- The literal inactive-counter increment never reads or writes a public
target bit. -/
lemma inactiveCounterIncrementGates_bitDisjoint_target
    (n k : Nat) (hkn : k ≤ n) (target : Fin n) :
    ∀ gate, gate ∈ inactiveCounterIncrementGates n k hkn →
      EncodedBit.GateSpec.bitDisjoint (targetValueBit n (k + 1) target) gate := by
  intro gate hgate
  rw [inactiveCounterIncrementGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | hlast
  · rcases List.mem_append.mp hprefix with hfirst | hclean
    · rw [List.mem_singleton] at hfirst
      subst gate
      exact inactiveCounterActiveBit_targetValueBit_wire_ne n k target
    · exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
        (inactiveCounterIncrementLayout n k hkn)
        (targetValueBit n (k + 1) target)
        (fun source => by
          simpa [inactiveCounterIncrementLayout, inactiveCounterSourceWord] using
            inactiveCounterSourceBit_targetValueBit_wire_ne n k source target)
        (fun counter => by
          simpa [inactiveCounterIncrementLayout, paddingCounterValueWord] using
            paddingCounterValueBit_targetValueBit_wire_ne n k counter target)
        (by
          simpa [inactiveCounterIncrementLayout] using
            coefficientCarryInBit_targetValueBit_wire_ne n k target)
        (fun work => by
          simpa [inactiveCounterIncrementLayout, paddingCounterCarryWorkWord] using
            paddingCounterCarryWorkBit_targetValueBit_wire_ne n k hkn work target)
        gate hclean
  · rw [List.mem_singleton] at hlast
    subst gate
    exact inactiveCounterActiveBit_targetValueBit_wire_ne n k target

/-- Actual base-gate program for the inactive compact counter increment. -/
def inactiveCounterIncrementProgram (n k : Nat) (hkn : k ≤ n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n (k + 1)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (inactiveCounterIncrementGates n k hkn)

/-- Folded bit-lens step of the inactive X--VBE--X schedule. -/
def inactiveCounterIncrementStep (n k : Nat) (hkn : k ≤ n) :
    Registers n (k + 1) -> Registers n (k + 1) :=
  EncodedBit.GateSpec.stepList (inactiveCounterIncrementGates n k hkn)

/-- The inactive compact counter program realizes its exact folded gate step. -/
lemma inactiveCounterIncrement_realizes (n k : Nat) (hkn : k ≤ n) :
    UnitaryCircuit.Realizes (encoding n (k + 1))
      (inactiveCounterIncrementProgram n k hkn) environment
      (inactiveCounterIncrementStep n k hkn) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (inactiveCounterIncrementGates n k hkn)

/-- Exact X coordinate of the inactive increment. -/
lemma inactiveCounterIncrementGates_xMultiplicity_sum
    (n k : Nat) (hkn : k ≤ n) :
    ((inactiveCounterIncrementGates n k hkn).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp [inactiveCounterIncrementGates, inactiveCounterLiteralGate,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum]

/-- Exact CNOT coordinate of the inactive increment. -/
lemma inactiveCounterIncrementGates_cnotMultiplicity_sum
    (n k : Nat) (hkn : k ≤ n) :
    ((inactiveCounterIncrementGates n k hkn).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (k + 1) := by
  simp [inactiveCounterIncrementGates, inactiveCounterLiteralGate,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate of the inactive increment. -/
lemma inactiveCounterIncrementGates_toffoliMultiplicity_sum
    (n k : Nat) (hkn : k ≤ n) :
    ((inactiveCounterIncrementGates n k hkn).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * k := by
  simp [inactiveCounterIncrementGates, inactiveCounterLiteralGate,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum]

/-- Exact primitive-gate length of the inactive increment. -/
lemma inactiveCounterIncrementGates_length
    (n k : Nat) (hkn : k ≤ n) :
    (inactiveCounterIncrementGates n k hkn).length = 8 * k + 4 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    inactiveCounterIncrementGates_xMultiplicity_sum,
    inactiveCounterIncrementGates_cnotMultiplicity_sum,
    inactiveCounterIncrementGates_toffoliMultiplicity_sum]
  omega

/-- The compiled inactive program retains its exact X count. -/
lemma inactiveCounterIncrementProgram_x_count
    (n k : Nat) (hkn : k ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (inactiveCounterIncrementProgram n k hkn).eventCost = 2 := by
  rw [inactiveCounterIncrementProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    inactiveCounterIncrementGates_xMultiplicity_sum]

/-- The compiled inactive program retains its exact CNOT count. -/
lemma inactiveCounterIncrementProgram_cnot_count
    (n k : Nat) (hkn : k ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (inactiveCounterIncrementProgram n k hkn).eventCost = 2 * (k + 1) := by
  rw [inactiveCounterIncrementProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    inactiveCounterIncrementGates_cnotMultiplicity_sum]

/-- The compiled inactive program retains its exact Toffoli count. -/
lemma inactiveCounterIncrementProgram_toffoli_count
    (n k : Nat) (hkn : k ≤ n) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (inactiveCounterIncrementProgram n k hkn).eventCost = 6 * k := by
  rw [inactiveCounterIncrementProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    inactiveCounterIncrementGates_toffoliMultiplicity_sum]

/-- Ordered carry recurrence shared by compact counter layouts.  A caller
supplies the source and target readout interpretations, while the proof reuses
the certified VBE bit-slice recurrence without enumerating word states. -/
private lemma compactCarryStage_get_workCarry_natAddCarry
    (n k : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n (k + 1)) (k + 1))
    (source target : Word (k + 1))
    (j : Fin k) (x : Registers n (k + 1))
    (hleft : ∀ bit : Fin (k + 1),
      (layout.left.bit bit).get x = source.val.testBit bit.val)
    (hright : ∀ bit : Fin (k + 1),
      (layout.right.bit bit).get x = target.val.testBit bit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ workBit : Fin k,
      (layout.workCarry.bit workBit).get x = false) :
    (layout.workCarry.bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry
        source.val target.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x
  change (layout.workCarry.bit j).get stage =
    Nat.BinaryArithmetic.natAddCarry
      source.val target.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin k, j.val = m ->
      (layout.workCarry.bit j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          source.val target.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            layout j x hwork
        change (layout.workCarry.bit j).get stage =
          Nat.BinaryArithmetic.natAddCarry
            source.val target.val (j.val + 1)
        change
          (layout.workCarry.bit j).get (layout.carryStageIndexStep x) =
            Nat.BinaryArithmetic.natAddCarry
              source.val target.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              layout x
          rw [hdata]
          have hsource := hleft
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)
          have htarget := hright
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)
          change Bool.carry
              ((layout.left.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              ((layout.right.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              (layout.carryIn.get x) =
            Nat.BinaryArithmetic.natAddCarry
              source.val target.val (j.val + 1)
          rw [hsource, htarget, hcarry]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let previous :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex
              (n := k + 1) j hzero
          have hpreviousLt : previous.val < m := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hprevious := ih previous.val hpreviousLt previous rfl
          have hprevious' :
              (layout.workCarry.bit previous).get
                  (layout.carryStageIndexStep x) =
                Nat.BinaryArithmetic.natAddCarry
                  source.val target.val (previous.val + 1) := by
            simpa only [stage] using hprevious
          have hpreviousSucc : previous.val + 1 = j.val := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hprevious', hpreviousSucc]
          have hsource := hleft
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)
          have htarget := hright
            (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)
          change Bool.carry
              ((layout.left.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              ((layout.right.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              (Nat.BinaryArithmetic.natAddCarry
                source.val target.val j.val) =
            Bool.carry
              (source.val.testBit j.val)
              (target.val.testBit j.val)
              (Nat.BinaryArithmetic.natAddCarry
                source.val target.val j.val)
          rw [hsource, htarget]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex]
  exact hmain j.val j rfl

/-- The carry selected before a compact counter sum is the corresponding
natural-addition carry for any layout satisfying the shared recurrence. -/
private lemma compactCarryBeforeSum_get_natAddCarry
    (n k : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n (k + 1)) (k + 1))
    (source target : Word (k + 1))
    (bit : Fin (k + 1)) (x : Registers n (k + 1))
    (hleft : ∀ sourceBit : Fin (k + 1),
      (layout.left.bit sourceBit).get x = source.val.testBit sourceBit.val)
    (hright : ∀ targetBit : Fin (k + 1),
      (layout.right.bit targetBit).get x = target.val.testBit targetBit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ workBit : Fin k,
      (layout.workCarry.bit workBit).get x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum layout bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry source.val target.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        layout x
    rw [hdata, hcarry]
    simp [Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hworkLt : bit.val - 1 < k := by
      have hbit := bit.isLt
      omega
    let workBit : Fin k := ⟨bit.val - 1, hworkLt⟩
    have hworkCarry :=
      compactCarryStage_get_workCarry_natAddCarry
        n k layout source target workBit x hleft hright hcarry hwork
    have hworkSucc : workBit.val + 1 = bit.val := by
      dsimp [workBit]
      omega
    change
      (layout.workCarry.bit workBit).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
        Nat.BinaryArithmetic.natAddCarry source.val target.val bit.val
    rw [hworkCarry, hworkSucc]

/-- Fixed-width word added by the inactive counter route. -/
def inactiveCounterSourceValue (k : Nat) (active : Bool) : Word (k + 1) :=
  if active then 0 else 1

/-- State after the leading X has turned the active bit into an inactive-mode
source bit. -/
def inactiveCounterLoadedInput (n k : Nat) (x : Registers n (k + 1)) :
    Registers n (k + 1) :=
  (inactiveCounterActiveBit n k).flip x

/-- Expose the literal X--adder--X composition of the inactive counter step. -/
lemma inactiveCounterIncrementStep_decompose
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1)) :
    inactiveCounterIncrementStep n k hkn x =
      (inactiveCounterActiveBit n k).flip
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (inactiveCounterIncrementLayout n k hkn)
          ((inactiveCounterActiveBit n k).flip x)) := by
  rw [inactiveCounterIncrementStep, inactiveCounterIncrementGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- The active bit is disjoint from the coefficient-adder carry-in. -/
lemma inactiveCounterActiveBit_coefficientCarryInBit_wire_ne
    (n k : Nat) :
    (inactiveCounterActiveBit n k).wire ≠
      (coefficientCarryInBit n (k + 1)).wire := by
  simpa [inactiveCounterActiveBit] using
    liftCoreBit_coefficientCarryInBit_wire_ne n (k + 1)
      (RegisterBits.activeBit n (k + 1))

/-- The leading active-bit X leaves each counter target bit unchanged. -/
lemma paddingCounterValueBit_get_inactiveCounterLoadedInput
    (n k : Nat) (x : Registers n (k + 1)) (bit : Fin (k + 1)) :
    (paddingCounterValueBit n k bit).get
        (inactiveCounterLoadedInput n k x) =
      x.core.counter.val.testBit bit.val := by
  rw [inactiveCounterLoadedInput]
  rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
    (paddingCounterValueBit n k bit)
    (inactiveCounterActiveBit_paddingCounterValueBit_wire_ne n k bit)]
  exact paddingCounterValueBit_get n k bit x

/-- A clean coefficient-adder workspace makes the carry-in clean after the
leading active-bit X. -/
lemma coefficientCarryInBit_get_inactiveCounterLoadedInput_of_clean
    (n k : Nat) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n) :
    (coefficientCarryInBit n (k + 1)).get
        (inactiveCounterLoadedInput n k x) = false := by
  rw [inactiveCounterLoadedInput]
  rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
    (coefficientCarryInBit n (k + 1))
    (inactiveCounterActiveBit_coefficientCarryInBit_wire_ne n k)]
  rw [coefficientCarryInBit_get, hcoeff]
  rfl

/-- A clean coefficient-adder workspace makes every borrowed VBE carry bit
clean after the leading active-bit X. -/
lemma paddingCounterCarryWorkBit_get_inactiveCounterLoadedInput_of_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (bit : Fin k) :
    (paddingCounterCarryWorkBit n k hkn bit).get
        (inactiveCounterLoadedInput n k x) = false := by
  rw [inactiveCounterLoadedInput]
  rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
    (paddingCounterCarryWorkBit n k hkn bit)
    (inactiveCounterActiveBit_paddingCounterCarryWorkBit_wire_ne n k hkn bit)]
  change
    (BinaryLabelEncoding.finIdentityBit n
      (paddingCounterCarryWorkIndex n k hkn bit)).get
        x.shared.coefficientAdder.2 = false
  rw [hcoeff]
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n
    (paddingCounterCarryWorkIndex n k hkn bit)

/-- The leading active-bit X turns the borrowed source word into the symbolic
fixed-width value `if active then 0 else 1`. -/
lemma inactiveCounterSourceBit_get_inactiveCounterLoadedInput
    (n k : Nat) (x : Registers n (k + 1))
    (hcorrection : x.shared.correctionCounter = 0)
    (bit : Fin (k + 1)) :
    (inactiveCounterSourceBit n k bit).get
        (inactiveCounterLoadedInput n k x) =
      (inactiveCounterSourceValue k x.core.active).val.testBit bit.val := by
  by_cases hbit : bit.val = 0
  · rw [inactiveCounterSourceBit_eq_active_of_zero n k bit hbit,
      inactiveCounterLoadedInput, EncodedBit.get_flip_self,
      inactiveCounterActiveBit_get]
    cases hactive : x.core.active <;>
      simp [inactiveCounterSourceValue, hbit]
  · rw [inactiveCounterSourceBit_eq_correction_of_ne_zero n k bit hbit,
      inactiveCounterLoadedInput]
    rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
      (correctionCounterValueBit n (k + 1)
        (paddingCounterSourceHighIndex bit hbit))
      (inactiveCounterActiveBit_correctionCounterValueBit_wire_ne n k
        (paddingCounterSourceHighIndex bit hbit))]
    rw [correctionCounterValueBit_get, hcorrection]
    cases hactive : x.core.active
    · simpa [inactiveCounterSourceValue] using
        (oneWord_testBit_eq_false_of_ne_zero k bit hbit).symm
    · simp [inactiveCounterSourceValue]

/-- Every observation outside the counter target, borrowed carry prefix, and
temporary active source wire is preserved by the inactive X--VBE--X schedule. -/
lemma inactiveCounterIncrementStep_get_observed_of_disjoint
    (n k : Nat) (hkn : k ≤ n)
    (observed : EncodedBit (encoding n (k + 1)))
    (hright : ∀ bit : Fin (k + 1),
      (paddingCounterValueBit n k bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin k,
      (paddingCounterCarryWorkBit n k hkn bit).wire ≠ observed.wire)
    (hactive : (inactiveCounterActiveBit n k).wire ≠ observed.wire)
    (x : Registers n (k + 1)) :
    observed.get (inactiveCounterIncrementStep n k hkn x) = observed.get x := by
  rw [inactiveCounterIncrementStep_decompose]
  rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
    observed hactive]
  have hadder :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (inactiveCounterIncrementLayout n k hkn) observed hright hwork
      ((inactiveCounterActiveBit n k).flip x)
  calc
    observed.get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (inactiveCounterIncrementLayout n k hkn)
          ((inactiveCounterActiveBit n k).flip x)) =
        observed.get ((inactiveCounterActiveBit n k).flip x) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using hadder
    _ = observed.get x :=
      EncodedBit.get_flip_of_wire_ne
        (inactiveCounterActiveBit n k) observed hactive x

/-- On a clean coefficient-adder/correction workspace, the VBE substep writes
each counter bit as the corresponding bit of `counter + (!active)`. -/
lemma inactiveCounterAdderStep_get_counter_add_testBit_of_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (hcorrection : x.shared.correctionCounter = 0)
    (bit : Fin (k + 1)) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
      (inactiveCounterIncrementLayout n k hkn)
      (inactiveCounterLoadedInput n k x)).core.counter.val.testBit bit.val =
      (x.core.counter + inactiveCounterSourceValue k x.core.active).val.testBit
        bit.val := by
  let input := inactiveCounterLoadedInput n k x
  have hgate :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (inactiveCounterIncrementLayout n k hkn) bit input
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hgate
  have hcarry :
      (inactiveCounterIncrementLayout n k hkn).carryIn.get input = false := by
    simpa [inactiveCounterIncrementLayout, input] using
      coefficientCarryInBit_get_inactiveCounterLoadedInput_of_clean
        n k x hcoeff
  have hwork : ∀ workBit : Fin k,
      ((inactiveCounterIncrementLayout n k hkn).workCarry.bit workBit).get
        input = false := by
    intro workBit
    simpa [inactiveCounterIncrementLayout, paddingCounterCarryWorkWord,
      input] using
      paddingCounterCarryWorkBit_get_inactiveCounterLoadedInput_of_clean
        n k hkn x hcoeff workBit
  have hsource : ∀ sourceBit : Fin (k + 1),
      ((inactiveCounterIncrementLayout n k hkn).left.bit sourceBit).get input =
        (inactiveCounterSourceValue k x.core.active).val.testBit sourceBit.val := by
    intro sourceBit
    simpa [inactiveCounterIncrementLayout, inactiveCounterSourceWord, input] using
      inactiveCounterSourceBit_get_inactiveCounterLoadedInput
        n k x hcorrection sourceBit
  have hright : ∀ counterBit : Fin (k + 1),
      ((inactiveCounterIncrementLayout n k hkn).right.bit counterBit).get input =
        x.core.counter.val.testBit counterBit.val := by
    intro counterBit
    simpa [inactiveCounterIncrementLayout, paddingCounterValueWord, input] using
      paddingCounterValueBit_get_inactiveCounterLoadedInput
        n k x counterBit
  have hcarryBit :=
    compactCarryBeforeSum_get_natAddCarry
      n k (inactiveCounterIncrementLayout n k hkn)
      (inactiveCounterSourceValue k x.core.active) x.core.counter bit input
      hsource hright hcarry hwork
  rw [hcarryBit] at hgate
  rw [hright bit, hsource bit] at hgate
  calc
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
      (inactiveCounterIncrementLayout n k hkn) input).core.counter.val.testBit
        bit.val =
        ((x.core.counter.val.testBit bit.val ^^
            (inactiveCounterSourceValue k x.core.active).val.testBit bit.val) ^^
          Nat.BinaryArithmetic.natAddCarry
            (inactiveCounterSourceValue k x.core.active).val x.core.counter.val
            bit.val) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        inactiveCounterIncrementLayout, inactiveCounterSourceWord,
        paddingCounterValueWord, paddingCounterValueBit_get,
        Bool.xor_assoc] using hgate
    _ = (x.core.counter + inactiveCounterSourceValue k x.core.active).val.testBit
        bit.val := by
      simpa [Bool.xor_assoc] using
        (word_add_testBit_eq_xor3 (k + 1)
          (inactiveCounterSourceValue k x.core.active) x.core.counter bit).symm

/-- The complete inactive X--VBE--X step updates the counter by the symbolic
fixed-width value `!active`. -/
lemma inactiveCounterIncrementStep_get_counter_add_testBit_of_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (hcorrection : x.shared.correctionCounter = 0)
    (bit : Fin (k + 1)) :
    (inactiveCounterIncrementStep n k hkn x).core.counter.val.testBit bit.val =
      (x.core.counter + inactiveCounterSourceValue k x.core.active).val.testBit
        bit.val := by
  rw [← paddingCounterValueBit_get n k bit]
  rw [inactiveCounterIncrementStep_decompose]
  rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
    (paddingCounterValueBit n k bit)
    (inactiveCounterActiveBit_paddingCounterValueBit_wire_ne n k bit)]
  rw [paddingCounterValueBit_get]
  exact inactiveCounterAdderStep_get_counter_add_testBit_of_clean
    n k hkn x hcoeff hcorrection bit

/-- Counter-level semantic endpoint for the compact inactive increment. -/
lemma inactiveCounterIncrementStep_counter_of_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (hcorrection : x.shared.correctionCounter = 0) :
    (inactiveCounterIncrementStep n k hkn x).core.counter =
      x.core.counter + inactiveCounterSourceValue k x.core.active := by
  apply word_eq_of_testBit_eq
  intro bit
  exact inactiveCounterIncrementStep_get_counter_add_testBit_of_clean
    n k hkn x hcoeff hcorrection bit

/-- The temporary X gates restore the active flag after the VBE addition. -/
lemma inactiveCounterIncrementStep_active
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1)) :
    (inactiveCounterIncrementStep n k hkn x).core.active = x.core.active := by
  have hleft :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (inactiveCounterIncrementLayout n k hkn) (0 : Fin (k + 1))
      ((inactiveCounterActiveBit n k).flip x)
  have hleftActive :
      (inactiveCounterActiveBit n k).get
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
            (inactiveCounterIncrementLayout n k hkn)
            ((inactiveCounterActiveBit n k).flip x)) =
        (inactiveCounterActiveBit n k).get
          ((inactiveCounterActiveBit n k).flip x) := by
    simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
      inactiveCounterIncrementLayout, inactiveCounterSourceWord,
      inactiveCounterSourceBit] using hleft
  rw [← inactiveCounterActiveBit_get n k
    (inactiveCounterIncrementStep n k hkn x),
    ← inactiveCounterActiveBit_get n k x]
  rw [inactiveCounterIncrementStep_decompose, EncodedBit.get_flip_self,
    hleftActive, EncodedBit.get_flip_self]
  simp

/-- A clean coefficient-adder work object has every carry-bank bit clear. -/
lemma coefficientCarryWorkBit_get_of_coefficientAdder_clean
    (n k : Nat) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (bit : Fin n) :
    (coefficientCarryWorkBit n (k + 1) bit).get x = false := by
  change (BinaryLabelEncoding.finIdentityBit n bit).get
      x.shared.coefficientAdder.2 = false
  rw [hcoeff]
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit

/-- The VBE carry-in returns to its clean value after the inactive increment. -/
lemma inactiveCounterIncrementStep_coefficientCarryIn_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n) :
    (inactiveCounterIncrementStep n k hkn x).shared.coefficientAdder.1 =
      false := by
  rw [← coefficientCarryInBit_get]
  rw [inactiveCounterIncrementStep_decompose]
  rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
    (coefficientCarryInBit n (k + 1))
    (inactiveCounterActiveBit_coefficientCarryInBit_wire_ne n k)]
  have hdata :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (inactiveCounterIncrementLayout n k hkn)
      ((inactiveCounterActiveBit n k).flip x)
  calc
    (coefficientCarryInBit n (k + 1)).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (inactiveCounterIncrementLayout n k hkn)
          ((inactiveCounterActiveBit n k).flip x)) =
        (coefficientCarryInBit n (k + 1)).get
          ((inactiveCounterActiveBit n k).flip x) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        inactiveCounterIncrementLayout] using hdata
    _ = (coefficientCarryInBit n (k + 1)).get x :=
      EncodedBit.get_flip_of_wire_ne
        (inactiveCounterActiveBit n k) (coefficientCarryInBit n (k + 1))
        (inactiveCounterActiveBit_coefficientCarryInBit_wire_ne n k) x
    _ = false := by
      rw [coefficientCarryInBit_get, hcoeff]
      rfl

/-- Each borrowed prefix carry is uncomputed back to zero by the inactive VBE
schedule. -/
lemma inactiveCounterIncrementStep_get_carryWork_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (bit : Fin k) :
    (paddingCounterCarryWorkBit n k hkn bit).get
        (inactiveCounterIncrementStep n k hkn x) = false := by
  rw [inactiveCounterIncrementStep_decompose]
  rw [EncodedBit.get_flip_of_wire_ne (inactiveCounterActiveBit n k)
    (paddingCounterCarryWorkBit n k hkn bit)
    (inactiveCounterActiveBit_paddingCounterCarryWorkBit_wire_ne n k hkn bit)]
  have hwork :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (inactiveCounterIncrementLayout n k hkn) bit
      ((inactiveCounterActiveBit n k).flip x) (by
        intro workBit
        simpa [inactiveCounterIncrementLayout, paddingCounterCarryWorkWord,
          inactiveCounterLoadedInput] using
          paddingCounterCarryWorkBit_get_inactiveCounterLoadedInput_of_clean
            n k hkn x hcoeff workBit)
  simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    inactiveCounterIncrementLayout, paddingCounterCarryWorkWord] using hwork

/-- Every VBE carry-bank bit is clean after the inactive increment: the
borrowed prefix is uncomputed and the untouched suffix is observed unchanged. -/
lemma inactiveCounterIncrementStep_coefficientCarryWork_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (bit : Fin n) :
    (coefficientCarryWorkBit n (k + 1) bit).get
        (inactiveCounterIncrementStep n k hkn x) = false := by
  by_cases hprefix : bit.val < k
  · let prefixBit : Fin k := ⟨bit.val, hprefix⟩
    have hindex : paddingCounterCarryWorkIndex n k hkn prefixBit = bit := by
      apply Fin.ext
      rfl
    have hclean := inactiveCounterIncrementStep_get_carryWork_clean
      n k hkn x hcoeff prefixBit
    simpa [paddingCounterCarryWorkBit, hindex] using hclean
  · have h := inactiveCounterIncrementStep_get_observed_of_disjoint
      n k hkn (coefficientCarryWorkBit n (k + 1) bit)
      (fun counterBit => by
        simpa [paddingCounterValueBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne n (k + 1)
            (RegisterBits.counterBit n (k + 1)
              (WireAddress.littleEndianWire counterBit)) bit)
      (fun workBit => by
        have hne : paddingCounterCarryWorkIndex n k hkn workBit ≠ bit := by
          intro heq
          have hval := congrArg Fin.val heq
          simp only [paddingCounterCarryWorkIndex_val] at hval
          omega
        simpa [paddingCounterCarryWorkBit] using
          coefficientCarryWorkBit_wire_ne n (k + 1) hne)
      (by
        simpa [inactiveCounterActiveBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne n (k + 1)
            (RegisterBits.activeBit n (k + 1)) bit)
      x
    calc
      (coefficientCarryWorkBit n (k + 1) bit).get
          (inactiveCounterIncrementStep n k hkn x) =
          (coefficientCarryWorkBit n (k + 1) bit).get x := h
      _ = false := coefficientCarryWorkBit_get_of_coefficientAdder_clean
        n k x hcoeff bit

/-- The complete shared VBE coefficient-adder workspace is clean at the
inactive-counter endpoint. -/
lemma inactiveCounterIncrementStep_coefficientAdder_cleanEndpoint
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n) :
    (inactiveCounterIncrementStep n k hkn x).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  change (inactiveCounterIncrementStep n k hkn x).shared.coefficientAdder =
    (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1))
  apply Prod.ext
  · exact inactiveCounterIncrementStep_coefficientCarryIn_clean
      n k hkn x hcoeff
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    change (coefficientCarryWorkBit n (k + 1) bit).get
        (inactiveCounterIncrementStep n k hkn x) = false
    exact inactiveCounterIncrementStep_coefficientCarryWork_clean
      n k hkn x hcoeff bit

/-- The borrowed correction-counter source word is preserved and hence remains
clean at the inactive-counter endpoint. -/
lemma inactiveCounterIncrementStep_correctionCounter_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcorrection : x.shared.correctionCounter = 0) :
    (inactiveCounterIncrementStep n k hkn x).shared.correctionCounter = 0 := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := inactiveCounterIncrementStep_get_observed_of_disjoint
    n k hkn (correctionCounterValueBit n (k + 1) bit)
    (fun counterBit => by
      simpa [paddingCounterValueBit, correctionCounterValueBit,
        correctionCounterBit] using
        liftCoreBit_liftSharedBit_wire_ne n (k + 1)
          (RegisterBits.counterBit n (k + 1)
            (WireAddress.littleEndianWire counterBit))
          (sharedCorrectionCounterBit n (k + 1)
            (WireAddress.littleEndianWire bit)))
    (fun workBit => by
      simpa [paddingCounterCarryWorkBit, correctionCounterValueBit,
        correctionCounterBit] using
        Ne.symm
          (correctionCounterBit_coefficientCarryWorkBit_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit)
            (paddingCounterCarryWorkIndex n k hkn workBit)))
    (inactiveCounterActiveBit_correctionCounterValueBit_wire_ne n k bit)
    x
  simpa [correctionCounterValueBit_get, hcorrection] using h

/-- The inactive increment leaves the shared route/path bit untouched. -/
lemma inactiveCounterIncrementStep_path
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1)) :
    (inactiveCounterIncrementStep n k hkn x).shared.path = x.shared.path := by
  have h := inactiveCounterIncrementStep_get_observed_of_disjoint
    n k hkn (pathBit n (k + 1))
    (fun counterBit => paddingCounterValueBit_pathBit_wire_ne n k counterBit)
    (fun workBit => Ne.symm
      (pathBit_paddingCounterCarryWorkBit_wire_ne n k hkn workBit))
    (by
      simpa [inactiveCounterActiveBit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n (k + 1)
          (RegisterBits.activeBit n (k + 1))
          (sharedPathBit n (k + 1)))
    x
  simpa only [pathBit_get] using h

/-- The inactive increment leaves the shared control bit untouched. -/
lemma inactiveCounterIncrementStep_control
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1)) :
    (inactiveCounterIncrementStep n k hkn x).shared.control =
      x.shared.control := by
  have h := inactiveCounterIncrementStep_get_observed_of_disjoint
    n k hkn (controlBit n (k + 1))
    (fun counterBit => by
      simpa [paddingCounterValueBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n (k + 1)
          (RegisterBits.counterBit n (k + 1)
            (WireAddress.littleEndianWire counterBit))
          (sharedControlBit n (k + 1)))
    (fun workBit => by
      simpa [paddingCounterCarryWorkBit] using
        Ne.symm
          (controlBit_coefficientCarryWorkBit_wire_ne n (k + 1)
            (paddingCounterCarryWorkIndex n k hkn workBit)))
    (by
      simpa [inactiveCounterActiveBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n (k + 1)
          (RegisterBits.activeBit n (k + 1))
          (sharedControlBit n (k + 1)))
    x
  simpa only [controlBit_get] using h

/-- The public target word is outside the inactive counter borrow set. -/
lemma inactiveCounterIncrementStep_target
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1)) :
    (inactiveCounterIncrementStep n k hkn x).target = x.target := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := inactiveCounterIncrementStep_get_observed_of_disjoint
    n k hkn (targetValueBit n (k + 1) bit)
    (fun counterBit => by
      simpa [paddingCounterValueBit, targetValueBit] using
        liftCoreBit_targetBit_wire_ne n (k + 1)
          (RegisterBits.counterBit n (k + 1)
            (WireAddress.littleEndianWire counterBit))
          (WireAddress.littleEndianWire bit))
    (fun workBit => by
      simpa [paddingCounterCarryWorkBit, targetValueBit,
        coefficientCarryWorkBit] using
        liftSharedBit_targetBit_wire_ne n (k + 1)
          (sharedCoefficientCarryWorkBit n (k + 1)
            (paddingCounterCarryWorkIndex n k hkn workBit))
          (WireAddress.littleEndianWire bit))
    (by
      simpa [inactiveCounterActiveBit, targetValueBit] using
        liftCoreBit_targetBit_wire_ne n (k + 1)
          (RegisterBits.activeBit n (k + 1))
          (WireAddress.littleEndianWire bit))
    x
  simpa only [targetValueBit_get] using h

/-- On clean coefficient-adder and correction inputs, the inactive route
restores every borrowed shared field while preserving the round path/control
state. -/
lemma inactiveCounterIncrementStep_shared_cleanEndpoint
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (hcorrection : x.shared.correctionCounter = 0) :
    (inactiveCounterIncrementStep n k hkn x).shared =
      { x.shared with
        coefficientAdder := cleanCoeffAdderWork n
        correctionCounter := 0 } := by
  apply (sharedWorkTupleEquiv n (k + 1)).injective
  change
    ((inactiveCounterIncrementStep n k hkn x).shared.coefficientAdder,
      ((inactiveCounterIncrementStep n k hkn x).shared.correctionCounter,
        ((inactiveCounterIncrementStep n k hkn x).shared.path,
          (inactiveCounterIncrementStep n k hkn x).shared.control))) =
      (cleanCoeffAdderWork n, (0, (x.shared.path, x.shared.control)))
  apply Prod.ext
  · exact inactiveCounterIncrementStep_coefficientAdder_cleanEndpoint
      n k hkn x hcoeff
  · apply Prod.ext
    · exact inactiveCounterIncrementStep_correctionCounter_clean
        n k hkn x hcorrection
    · apply Prod.ext
      · exact inactiveCounterIncrementStep_path n k hkn x
      · exact inactiveCounterIncrementStep_control n k hkn x

/-- A core-register observation outside the inactive counter target and
temporary active source wire is preserved by the inactive increment. -/
private lemma inactiveCounterIncrementStep_get_coreBit_of_disjoint
    (n k : Nat) (hkn : k ≤ n)
    (observed : EncodedBit (registerEncoding n (k + 1)))
    (hright : ∀ bit : Fin (k + 1),
      (RegisterBits.counterBit n (k + 1)
        (WireAddress.littleEndianWire bit)).wire ≠ observed.wire)
    (hactive : (RegisterBits.activeBit n (k + 1)).wire ≠ observed.wire)
    (x : Registers n (k + 1)) :
    observed.get (inactiveCounterIncrementStep n k hkn x).core =
      observed.get x.core := by
  have h := inactiveCounterIncrementStep_get_observed_of_disjoint
    n k hkn (liftCoreBit n (k + 1) observed)
    (fun bit => by
      simpa only [paddingCounterValueBit] using
        liftCoreBit_wire_ne n (k + 1)
          (hright bit))
    (fun bit => by
      simpa only [paddingCounterCarryWorkBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n (k + 1) observed
          (paddingCounterCarryWorkIndex n k hkn bit)).symm)
    (by
      simpa only [inactiveCounterActiveBit] using
        liftCoreBit_wire_ne n (k + 1) hactive)
    x
  simpa only [liftCoreBit_get] using h

/-- The inactive increment preserves every core field except its symbolic
padding-counter update. -/
lemma inactiveCounterIncrementStep_core_eq_update_of_clean
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (hcorrection : x.shared.correctionCounter = 0) :
    (inactiveCounterIncrementStep n k hkn x).core =
      { x.core with
        counter := x.core.counter + inactiveCounterSourceValue k x.core.active } := by
  apply (QuantumAlg.MAU.Inversion.MK.registerTupleEquiv n (k + 1)).injective
  change
    ((inactiveCounterIncrementStep n k hkn x).core.u,
      ((inactiveCounterIncrementStep n k hkn x).core.v,
        ((inactiveCounterIncrementStep n k hkn x).core.compare,
          ((inactiveCounterIncrementStep n k hkn x).core.sCoeff,
            ((inactiveCounterIncrementStep n k hkn x).core.rCoeff,
              ((inactiveCounterIncrementStep n k hkn x).core.scratchA,
                ((inactiveCounterIncrementStep n k hkn x).core.scratchB,
                  ((inactiveCounterIncrementStep n k hkn x).core.history,
                    ((inactiveCounterIncrementStep n k hkn x).core.active,
                      (inactiveCounterIncrementStep n k hkn x).core.counter))))))))) =
      (x.core.u,
        (x.core.v,
          (x.core.compare,
            (x.core.sCoeff,
              (x.core.rCoeff,
                (x.core.scratchA,
                  (x.core.scratchB,
                    (x.core.history,
                      (x.core.active,
                        x.core.counter + inactiveCounterSourceValue k x.core.active)))))))))
  repeat' apply Prod.ext
  · apply word_eq_of_testBit_eq
    intro bit
    have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.uValueBit n (k + 1) bit)
      (fun counterBit => by
        simpa only [RegisterBits.uValueBit] using
          (RegisterBits.u_counter_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire counterBit)).symm)
      (by
        simpa only [RegisterBits.uValueBit] using
          RegisterBits.active_u_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit))
      x
    simpa only [RegisterBits.uValueBit_get] using h
  · apply word_eq_of_testBit_eq
    intro bit
    have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.vValueBit n (k + 1) bit)
      (fun counterBit => by
        simpa only [RegisterBits.vValueBit] using
          (RegisterBits.v_counter_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire counterBit)).symm)
      (by
        simpa only [RegisterBits.vValueBit] using
          RegisterBits.active_v_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit))
      x
    simpa only [RegisterBits.vValueBit_get] using h
  · have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.compareBit n (k + 1))
      (fun counterBit =>
        (RegisterBits.compare_counter_wire_ne n (k + 1)
          (WireAddress.littleEndianWire counterBit)).symm)
      (RegisterBits.active_compare_wire_ne n (k + 1)) x
    simpa only [RegisterBits.compareBit_get] using h
  · apply word_eq_of_testBit_eq
    intro bit
    have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.sCoeffValueBit n (k + 1) bit)
      (fun counterBit => by
        simpa only [RegisterBits.sCoeffValueBit] using
          (RegisterBits.sCoeff_counter_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire counterBit)).symm)
      (by
        simpa only [RegisterBits.sCoeffValueBit] using
          RegisterBits.active_sCoeff_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit))
      x
    simpa only [RegisterBits.sCoeffValueBit_get] using h
  · apply word_eq_of_testBit_eq
    intro bit
    have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.rCoeffValueBit n (k + 1) bit)
      (fun counterBit => by
        simpa only [RegisterBits.rCoeffValueBit] using
          (RegisterBits.rCoeff_counter_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire counterBit)).symm)
      (by
        simpa only [RegisterBits.rCoeffValueBit] using
          RegisterBits.active_rCoeff_wire_ne n (k + 1)
            (WireAddress.littleEndianWire bit))
      x
    simpa only [RegisterBits.rCoeffValueBit_get] using h
  · have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.scratchABit n (k + 1))
      (fun counterBit =>
        (RegisterBits.scratchA_counter_wire_ne n (k + 1)
          (WireAddress.littleEndianWire counterBit)).symm)
      (RegisterBits.active_scratchA_wire_ne n (k + 1)) x
    simpa only [RegisterBits.scratchABit_get] using h
  · have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.scratchBBit n (k + 1))
      (fun counterBit =>
        (RegisterBits.scratchB_counter_wire_ne n (k + 1)
          (WireAddress.littleEndianWire counterBit)).symm)
      (RegisterBits.active_scratchB_wire_ne n (k + 1)) x
    simpa only [RegisterBits.scratchBBit_get] using h
  · apply word_eq_of_testBit_eq
    intro bit
    have h := inactiveCounterIncrementStep_get_coreBit_of_disjoint
      n k hkn (RegisterBits.historyBit n (k + 1)
        (WireAddress.littleEndianWire bit))
      (fun counterBit =>
        (RegisterBits.history_counter_wire_ne n (k + 1)
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire counterBit)).symm)
      (RegisterBits.active_history_wire_ne n (k + 1)
        (WireAddress.littleEndianWire bit)) x
    simpa only [RegisterBits.historyBit_get,
      WireAddress.bitIndex_littleEndianWire] using h
  · exact inactiveCounterIncrementStep_active n k hkn x
  · exact inactiveCounterIncrementStep_counter_of_clean
      n k hkn x hcoeff hcorrection

/-- Complete clean-boundary endpoint for the compact inactive counter route.
The only state update is the symbolic fixed-width counter addition. -/
lemma inactiveCounterIncrementStep_cleanEndpoint
    (n k : Nat) (hkn : k ≤ n) (x : Registers n (k + 1))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (hcorrection : x.shared.correctionCounter = 0) :
    inactiveCounterIncrementStep n k hkn x =
      { x with
        core := { x.core with
          counter := x.core.counter + inactiveCounterSourceValue k x.core.active } } := by
  apply (registerTupleEquiv n (k + 1)).injective
  change
    ((inactiveCounterIncrementStep n k hkn x).core,
      ((inactiveCounterIncrementStep n k hkn x).shared,
        (inactiveCounterIncrementStep n k hkn x).target)) =
      ({ x.core with
        counter := x.core.counter + inactiveCounterSourceValue k x.core.active },
        (x.shared, x.target))
  apply Prod.ext
  · exact inactiveCounterIncrementStep_core_eq_update_of_clean
      n k hkn x hcoeff hcorrection
  · apply Prod.ext
    · apply (sharedWorkTupleEquiv n (k + 1)).injective
      change
        ((inactiveCounterIncrementStep n k hkn x).shared.coefficientAdder,
          ((inactiveCounterIncrementStep n k hkn x).shared.correctionCounter,
            ((inactiveCounterIncrementStep n k hkn x).shared.path,
              (inactiveCounterIncrementStep n k hkn x).shared.control))) =
          (x.shared.coefficientAdder,
            (x.shared.correctionCounter, (x.shared.path, x.shared.control)))
      rw [inactiveCounterIncrementStep_coefficientAdder_cleanEndpoint
        n k hkn x hcoeff,
        inactiveCounterIncrementStep_correctionCounter_clean
          n k hkn x hcorrection,
        inactiveCounterIncrementStep_path n k hkn x,
        inactiveCounterIncrementStep_control n k hkn x,
        hcoeff, hcorrection]
    · exact inactiveCounterIncrementStep_target n k hkn x

end Compact

end
end MK
end MAU.Inversion
end QuantumAlg

end
