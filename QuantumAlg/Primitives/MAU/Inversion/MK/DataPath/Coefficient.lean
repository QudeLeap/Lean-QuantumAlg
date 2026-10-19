/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Inversion.MK.DataPath.Swap

/-!
# Coefficient data path

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

/-! ## Coefficient-add data-path atoms -/

/-- Carry-work layout for adding the `r` coefficient word into the `s`
coefficient word with a dedicated clean carry-in/work object.  This instantiates
the VBE clean-work adder shape for the Kaliski coefficient update route
[RNSL17, ECDLP.tex:399-421; VBE95, 9511018.tex:237-264,591-618]. -/
def coefficientAddRIntoSLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := registersWithCoeffAdderWorkEncoding n counterWidth)
      (n + 1) where
  left := coeffAdderRCoeffValueWord n counterWidth
  right := coeffAdderSCoeffValueWord n counterWidth
  carryIn := liftedCoeffAdderCarryInBit n counterWidth
  workCarry := liftedCoeffAdderCarryWorkWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
      ((liftedRCoeffValueWord n counterWidth).bit j)
      (liftedRCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne
        n counterWidth i j hij)
  rightRight_ne := by
    intro i j hij
    exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
      ((liftedSCoeffValueWord n counterWidth).bit j)
      (liftedSCoeffValueWordBit_liftedSCoeffValueWordBit_wire_ne
        n counterWidth i j hij)
  leftRight_ne := by
    intro i j
    exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
      ((liftedSCoeffValueWord n counterWidth).bit j)
      (Ne.symm
        (liftedSCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne
          n counterWidth j i))
  leftCarryIn_ne := by
    intro i
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryInWorkBit n)
  rightCarryIn_ne := by
    intro i
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryInWorkBit n)
  leftWork_ne := by
    intro i j
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryWorkBit n j)
  rightWork_ne := by
    intro i j
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryWorkBit n j)
  carryInWork_ne := by
    intro j
    exact liftCoeffAdderWorkBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth (coeffAdderCarryInWorkBit n)
      (coeffAdderCarryWorkBit n j)
      (coeffAdderCarryIn_carryWork_wire_ne n j)
  workWork_ne := by
    intro i j hij
    exact liftCoeffAdderWorkBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth (coeffAdderCarryWorkBit n i)
      (coeffAdderCarryWorkBit n j)
      (coeffAdderCarryWork_carryWork_wire_ne n i j hij)

/-- Folded carry/sum/cleanup gate list for adding `r` into `s` in the
coefficient workspace. -/
def coefficientAddRIntoSGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (coefficientAddRIntoSLayout n counterWidth)

/-- Exact physical length of the `r`-into-`s` coefficient adder. -/
lemma coefficientAddRIntoSGates_length (n counterWidth : Nat) :
    (coefficientAddRIntoSGates n counterWidth).length = 8 * n + 2 := by
  simp only [coefficientAddRIntoSGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length]
  omega

/-- The `r`-into-`s` coefficient adder has no X leaf. -/
lemma coefficientAddRIntoSGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((coefficientAddRIntoSGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [coefficientAddRIntoSGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
      (coefficientAddRIntoSLayout n counterWidth))

/-- Exact CNOT coordinate of the `r`-into-`s` coefficient adder. -/
lemma coefficientAddRIntoSGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddRIntoSGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (n + 1) := by
  simpa only [coefficientAddRIntoSGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
      (coefficientAddRIntoSLayout n counterWidth))

/-- Exact Toffoli coordinate of the `r`-into-`s` coefficient adder. -/
lemma coefficientAddRIntoSGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddRIntoSGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  simpa only [coefficientAddRIntoSGates, Nat.add_sub_cancel] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
      (coefficientAddRIntoSLayout n counterWidth))

/-- Base-gate program for the `r`-into-`s` coefficient adder. -/
def coefficientAddRIntoSProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram
    (coefficientAddRIntoSLayout n counterWidth)

/-- Folded semantic action for the `r`-into-`s` coefficient adder. -/
def coefficientAddRIntoSStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
    (coefficientAddRIntoSLayout n counterWidth)

/-- The `r`-into-`s` coefficient adder realizes its folded bit-lens action with
the same base-gate object used for resource accounting. -/
lemma coefficientAddRIntoS_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coefficientAddRIntoSProgram n counterWidth) environment
      (coefficientAddRIntoSStep n counterWidth) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes
    (coefficientAddRIntoSLayout n counterWidth)

/-- The `r`-into-`s` coefficient adder preserves every `r` coefficient bit. -/
lemma coefficientAddRIntoSStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coefficientAddRIntoSStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (coefficientAddRIntoSLayout n counterWidth) bit x
  simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The `r`-into-`s` coefficient adder preserves its dedicated carry-in flag. -/
lemma coefficientAddRIntoSStep_get_carryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (coefficientAddRIntoSLayout n counterWidth) x
  simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- Gate-list target-bit formula for adding `r` into `s`; the arithmetic
endpoint follows from the same carry-work invariant in the reusable VBE adder. -/
lemma coefficientAddRIntoSStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coefficientAddRIntoSStep n counterWidth x) =
      ((((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x ^^
          ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x) ^^
        (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
          (coefficientAddRIntoSLayout n counterWidth) bit).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coefficientAddRIntoSLayout n counterWidth) x)) := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (coefficientAddRIntoSLayout n counterWidth) bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep] at h
  simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- On clean coefficient carry/work inputs, the `r`-into-`s` carry stage
computes the propagated natural addition carry. -/
lemma coefficientAddRIntoS_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat) (j : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coefficientAddRIntoSLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.rCoeff.val x.1.1.sCoeff.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (coefficientAddRIntoSLayout n counterWidth) x
  change
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get stage =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.rCoeff.val x.1.1.sCoeff.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin ((n + 1) - 1), j.val = m ->
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.rCoeff.val x.1.1.sCoeff.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (coefficientAddRIntoSLayout n counterWidth) j x hwork
        change
          ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get stage =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.rCoeff.val x.1.1.sCoeff.val (j.val + 1)
        change
          ((coefficientAddRIntoSLayout n counterWidth).workCarry.bit j).get
              ((coefficientAddRIntoSLayout n counterWidth).carryStageIndexStep
                x) =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.rCoeff.val x.1.1.sCoeff.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (coefficientAddRIntoSLayout n counterWidth) x
          rw [hdata]
          simp [coefficientAddRIntoSLayout, coeffAdderRCoeffValueWord_get_testBit,
            coeffAdderSCoeffValueWord_get_testBit, hcarry,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpRec' :
              ((coefficientAddRIntoSLayout n counterWidth).workCarry.bit p).get
                  ((coefficientAddRIntoSLayout n counterWidth).carryStageIndexStep
                    x) =
                Nat.BinaryArithmetic.natAddCarry
                  x.1.1.rCoeff.val x.1.1.sCoeff.val (p.val + 1) := by
            simpa [stage, coefficientAddRIntoSLayout] using hpRec
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hpRec', hpSucc]
          simp [coefficientAddRIntoSLayout, coeffAdderRCoeffValueWord_get_testBit,
            coeffAdderSCoeffValueWord_get_testBit,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before the `r`-into-`s` target sum is the propagated
natural addition carry on clean coefficient carry/work inputs. -/
lemma coefficientAddRIntoS_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (coefficientAddRIntoSLayout n counterWidth) bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coefficientAddRIntoSLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.rCoeff.val x.1.1.sCoeff.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (coefficientAddRIntoSLayout n counterWidth) x
    rw [hdata]
    simp [coefficientAddRIntoSLayout, hcarry,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : bit.val - 1 < (n + 1) - 1 := by
      have hbit := bit.isLt
      omega
    let j : Fin ((n + 1) - 1) := ⟨bit.val - 1, hjLt⟩
    have hworkCarry :=
      coefficientAddRIntoS_carryStage_get_workCarry_natAddCarry
        n counterWidth j x hcarry hwork
    have hjSucc : j.val + 1 = bit.val := by
      dsimp [j]
      omega
    change
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coefficientAddRIntoSLayout n counterWidth) x) =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.rCoeff.val x.1.1.sCoeff.val bit.val
    rw [hworkCarry, hjSucc]

/-- On clean coefficient carry/work inputs, the `r`-into-`s` adder writes the
target `s` coefficient word as `s + r`. -/
lemma coefficientAddRIntoSStep_get_sCoeff_add_testBit_of_clean
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coefficientAddRIntoSStep n counterWidth x).1.1.sCoeff.val.testBit
        bit.val =
      (x.1.1.sCoeff + x.1.1.rCoeff).val.testBit bit.val := by
  have hright :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (coefficientAddRIntoSLayout n counterWidth) bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hright
  have hcarryBit :=
    coefficientAddRIntoS_carryBeforeSum_get_natAddCarry
      n counterWidth bit x hcarry hwork
  rw [hcarryBit] at hright
  have hadd :=
    (word_add_testBit_eq_xor3 (n + 1) x.1.1.rCoeff x.1.1.sCoeff bit).symm
  calc
    (coefficientAddRIntoSStep n counterWidth x).1.1.sCoeff.val.testBit
        bit.val =
        (((x.1.1.sCoeff.val.testBit bit.val ^^
              x.1.1.rCoeff.val.testBit bit.val) ^^
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.rCoeff.val x.1.1.sCoeff.val bit.val)) := by
      simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        coeffAdderSCoeffValueWord_get_testBit,
        coeffAdderRCoeffValueWord_get_testBit, Bool.xor_assoc] using hright
    _ = (x.1.1.sCoeff + x.1.1.rCoeff).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using hadd

/-- Word-level clean-input endpoint for the `r`-into-`s` coefficient adder. -/
lemma coefficientAddRIntoSStep_get_sCoeff_add_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coefficientAddRIntoSStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  exact coefficientAddRIntoSStep_get_sCoeff_add_testBit_of_clean
    n counterWidth bit x hcarry hwork

/-- On clean coefficient-adder work inputs, the `r`-into-`s` adder restores each
temporary carry-work bit to false. -/
lemma coefficientAddRIntoSStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hclean :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x = false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coefficientAddRIntoSStep n counterWidth x) =
      false := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (coefficientAddRIntoSLayout n counterWidth) bit x hclean
  simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The `r`-into-`s` coefficient adder preserves any observed readout whose
wire is disjoint from every `s` target bit and every temporary carry-work bit. -/
lemma coefficientAddRIntoSStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hright :
      ∀ i : Fin (n + 1),
        ((coeffAdderSCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (hwork :
      ∀ j : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).wire ≠
          observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coefficientAddRIntoSStep n counterWidth x) =
      observed.get x := by
  have hrightValue :
      ∀ i : Fin (n + 1),
        ((coefficientAddRIntoSLayout n counterWidth).right.bit i).wire ≠
          observed.wire := by
    intro i
    simpa [coefficientAddRIntoSLayout, coeffAdderSCoeffValueWord,
      coeffAdderSCoeffWord, liftedSCoeffValueWord, liftedSCoeffWord,
      RegisterBits.sCoeffValueBit] using
      hright (WireAddress.littleEndianWire i)
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coefficientAddRIntoSLayout n counterWidth) observed hrightValue hwork x
  simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The `r`-into-`s` coefficient adder preserves the comparison ancilla. -/
lemma coefficientAddRIntoSStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderCompareBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          (liftedCompareBit n counterWidth)
          (Ne.symm
            (liftedCompare_liftedSCoeffWordBit_wire_ne
              n counterWidth i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedCompareBit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `r`-into-`s` coefficient adder preserves the active flag. -/
lemma coefficientAddRIntoSStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderActiveBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          (liftedActiveBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.sCoeffBit n counterWidth i)
            (RegisterBits.activeBit n counterWidth)
            (Ne.symm (RegisterBits.active_sCoeff_wire_ne
              n counterWidth i))))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedActiveBit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `r`-into-`s` coefficient adder preserves every stored branch-history
bit. -/
lemma coefficientAddRIntoSStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderHistoryBit n counterWidth historyIndex)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          (liftedHistoryBit n counterWidth historyIndex)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.sCoeffBit n counterWidth i)
            (RegisterBits.historyBit n counterWidth historyIndex)
            (RegisterBits.sCoeff_history_wire_ne n counterWidth i
              historyIndex)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedHistoryBit n counterWidth historyIndex)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `r`-into-`s` coefficient adder preserves the first scratch bit. -/
lemma coefficientAddRIntoSStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderScratchABit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          (liftedScratchABit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.sCoeffBit n counterWidth i)
            (RegisterBits.scratchABit n counterWidth)
            (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedScratchABit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `r`-into-`s` coefficient adder preserves the second scratch bit. -/
lemma coefficientAddRIntoSStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderScratchBBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          (liftedScratchBBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.sCoeffBit n counterWidth i)
            (RegisterBits.scratchBBit n counterWidth)
            (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedScratchBBit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `r`-into-`s` coefficient adder preserves every comparison-work carry
bit. -/
lemma coefficientAddRIntoSStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderComparisonCarryBit n counterWidth workBit)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          (liftedComparisonCarryBit n counterWidth workBit)
          (liftedSCoeffWordBit_liftedComparisonCarry_wire_ne
            n counterWidth i workBit))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth
            (liftedComparisonCarryBit n counterWidth workBit)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `r`-into-`s` coefficient adder preserves every `u` value bit. -/
lemma coefficientAddRIntoSStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coefficientAddRIntoSStep n counterWidth x) =
      ((coeffAdderUWord n counterWidth).bit bit).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth ((coeffAdderUWord n counterWidth).bit bit)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          ((liftedUWord n counterWidth).bit bit)
          (Ne.symm
            (liftedUWordBit_liftedSCoeffWordBit_wire_ne
              n counterWidth bit i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth ((liftedUWord n counterWidth).bit bit)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `r`-into-`s` coefficient adder preserves every `v` value bit. -/
lemma coefficientAddRIntoSStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coefficientAddRIntoSStep n counterWidth x) =
      ((coeffAdderVWord n counterWidth).bit bit).get x := by
  exact
    coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth ((coeffAdderVWord n counterWidth).bit bit)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedSCoeffWord n counterWidth).bit i)
          ((liftedVWord n counterWidth).bit bit)
          (Ne.symm
            (liftedVWordBit_liftedSCoeffWordBit_wire_ne
              n counterWidth bit i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth ((liftedVWord n counterWidth).bit bit)
            (coeffAdderCarryWorkBit n j)))
      x

/-- Carry-work layout for adding the `s` coefficient word into the `r`
coefficient word with the same dedicated clean carry-in/work object
[RNSL17, ECDLP.tex:399-421; VBE95, 9511018.tex:237-264,591-618]. -/
def coefficientAddSIntoRLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := registersWithCoeffAdderWorkEncoding n counterWidth)
      (n + 1) where
  left := coeffAdderSCoeffValueWord n counterWidth
  right := coeffAdderRCoeffValueWord n counterWidth
  carryIn := liftedCoeffAdderCarryInBit n counterWidth
  workCarry := liftedCoeffAdderCarryWorkWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
      ((liftedSCoeffValueWord n counterWidth).bit j)
      (liftedSCoeffValueWordBit_liftedSCoeffValueWordBit_wire_ne
        n counterWidth i j hij)
  rightRight_ne := by
    intro i j hij
    exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
      ((liftedRCoeffValueWord n counterWidth).bit j)
      (liftedRCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne
        n counterWidth i j hij)
  leftRight_ne := by
    intro i j
    exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
      n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
      ((liftedRCoeffValueWord n counterWidth).bit j)
      (liftedSCoeffValueWordBit_liftedRCoeffValueWordBit_wire_ne
        n counterWidth i j)
  leftCarryIn_ne := by
    intro i
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryInWorkBit n)
  rightCarryIn_ne := by
    intro i
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryInWorkBit n)
  leftWork_ne := by
    intro i j
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryWorkBit n j)
  rightWork_ne := by
    intro i j
    exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
      (coeffAdderCarryWorkBit n j)
  carryInWork_ne := by
    intro j
    exact liftCoeffAdderWorkBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth (coeffAdderCarryInWorkBit n)
      (coeffAdderCarryWorkBit n j)
      (coeffAdderCarryIn_carryWork_wire_ne n j)
  workWork_ne := by
    intro i j hij
    exact liftCoeffAdderWorkBit_liftCoeffAdderWorkBit_wire_ne
      n counterWidth (coeffAdderCarryWorkBit n i)
      (coeffAdderCarryWorkBit n j)
      (coeffAdderCarryWork_carryWork_wire_ne n i j hij)

/-- Folded carry/sum/cleanup gate list for adding `s` into `r` in the
coefficient workspace. -/
def coefficientAddSIntoRGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (coefficientAddSIntoRLayout n counterWidth)

/-- Exact physical length of the `s`-into-`r` coefficient adder. -/
lemma coefficientAddSIntoRGates_length (n counterWidth : Nat) :
    (coefficientAddSIntoRGates n counterWidth).length = 8 * n + 2 := by
  simp only [coefficientAddSIntoRGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length]
  omega

/-- The `s`-into-`r` coefficient adder has no X leaf. -/
lemma coefficientAddSIntoRGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((coefficientAddSIntoRGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [coefficientAddSIntoRGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
      (coefficientAddSIntoRLayout n counterWidth))

/-- Exact CNOT coordinate of the `s`-into-`r` coefficient adder. -/
lemma coefficientAddSIntoRGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddSIntoRGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (n + 1) := by
  simpa only [coefficientAddSIntoRGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
      (coefficientAddSIntoRLayout n counterWidth))

/-- Exact Toffoli coordinate of the `s`-into-`r` coefficient adder. -/
lemma coefficientAddSIntoRGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddSIntoRGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  simpa only [coefficientAddSIntoRGates, Nat.add_sub_cancel] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
      (coefficientAddSIntoRLayout n counterWidth))

/-- Base-gate program for the `s`-into-`r` coefficient adder. -/
def coefficientAddSIntoRProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram
    (coefficientAddSIntoRLayout n counterWidth)

/-- Folded semantic action for the `s`-into-`r` coefficient adder. -/
def coefficientAddSIntoRStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
    (coefficientAddSIntoRLayout n counterWidth)

/-- The `s`-into-`r` coefficient adder realizes its folded bit-lens action with
the same base-gate object used for resource accounting. -/
lemma coefficientAddSIntoR_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coefficientAddSIntoRProgram n counterWidth) environment
      (coefficientAddSIntoRStep n counterWidth) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes
    (coefficientAddSIntoRLayout n counterWidth)

/-- The `s`-into-`r` coefficient adder preserves every `s` coefficient bit. -/
lemma coefficientAddSIntoRStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coefficientAddSIntoRStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (coefficientAddSIntoRLayout n counterWidth) bit x
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The `s`-into-`r` coefficient adder preserves its dedicated carry-in flag. -/
lemma coefficientAddSIntoRStep_get_carryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (coefficientAddSIntoRLayout n counterWidth) x
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- Gate-list target-bit formula for adding `s` into `r`; the arithmetic
endpoint follows from the same carry-work invariant in the reusable VBE adder. -/
lemma coefficientAddSIntoRStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coefficientAddSIntoRStep n counterWidth x) =
      ((((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x ^^
          ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x) ^^
        (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
          (coefficientAddSIntoRLayout n counterWidth) bit).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coefficientAddSIntoRLayout n counterWidth) x)) := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (coefficientAddSIntoRLayout n counterWidth) bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep] at h
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- On clean coefficient carry/work inputs, the `s`-into-`r` carry stage
computes the propagated natural addition carry. -/
lemma coefficientAddSIntoR_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat) (j : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coefficientAddSIntoRLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.sCoeff.val x.1.1.rCoeff.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (coefficientAddSIntoRLayout n counterWidth) x
  change
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get stage =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.sCoeff.val x.1.1.rCoeff.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin ((n + 1) - 1), j.val = m ->
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.sCoeff.val x.1.1.rCoeff.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (coefficientAddSIntoRLayout n counterWidth) j x hwork
        change
          ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get stage =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.sCoeff.val x.1.1.rCoeff.val (j.val + 1)
        change
          ((coefficientAddSIntoRLayout n counterWidth).workCarry.bit j).get
              ((coefficientAddSIntoRLayout n counterWidth).carryStageIndexStep
                x) =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.sCoeff.val x.1.1.rCoeff.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (coefficientAddSIntoRLayout n counterWidth) x
          rw [hdata]
          simp [coefficientAddSIntoRLayout, coeffAdderSCoeffValueWord_get_testBit,
            coeffAdderRCoeffValueWord_get_testBit, hcarry,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpRec' :
              ((coefficientAddSIntoRLayout n counterWidth).workCarry.bit p).get
                  ((coefficientAddSIntoRLayout n counterWidth).carryStageIndexStep
                    x) =
                Nat.BinaryArithmetic.natAddCarry
                  x.1.1.sCoeff.val x.1.1.rCoeff.val (p.val + 1) := by
            simpa [stage, coefficientAddSIntoRLayout] using hpRec
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hpRec', hpSucc]
          simp [coefficientAddSIntoRLayout, coeffAdderSCoeffValueWord_get_testBit,
            coeffAdderRCoeffValueWord_get_testBit,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before the `s`-into-`r` target sum is the propagated
natural addition carry on clean coefficient carry/work inputs. -/
lemma coefficientAddSIntoR_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (coefficientAddSIntoRLayout n counterWidth) bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coefficientAddSIntoRLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.sCoeff.val x.1.1.rCoeff.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (coefficientAddSIntoRLayout n counterWidth) x
    rw [hdata]
    simp [coefficientAddSIntoRLayout, hcarry,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : bit.val - 1 < (n + 1) - 1 := by
      have hbit := bit.isLt
      omega
    let j : Fin ((n + 1) - 1) := ⟨bit.val - 1, hjLt⟩
    have hworkCarry :=
      coefficientAddSIntoR_carryStage_get_workCarry_natAddCarry
        n counterWidth j x hcarry hwork
    have hjSucc : j.val + 1 = bit.val := by
      dsimp [j]
      omega
    change
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coefficientAddSIntoRLayout n counterWidth) x) =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.sCoeff.val x.1.1.rCoeff.val bit.val
    rw [hworkCarry, hjSucc]

/-- On clean coefficient carry/work inputs, the `s`-into-`r` adder writes the
target `r` coefficient word as `r + s`. -/
lemma coefficientAddSIntoRStep_get_rCoeff_add_testBit_of_clean
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coefficientAddSIntoRStep n counterWidth x).1.1.rCoeff.val.testBit
        bit.val =
      (x.1.1.rCoeff + x.1.1.sCoeff).val.testBit bit.val := by
  have hright :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (coefficientAddSIntoRLayout n counterWidth) bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hright
  have hcarryBit :=
    coefficientAddSIntoR_carryBeforeSum_get_natAddCarry
      n counterWidth bit x hcarry hwork
  rw [hcarryBit] at hright
  have hadd :=
    (word_add_testBit_eq_xor3 (n + 1) x.1.1.sCoeff x.1.1.rCoeff bit).symm
  calc
    (coefficientAddSIntoRStep n counterWidth x).1.1.rCoeff.val.testBit
        bit.val =
        (((x.1.1.rCoeff.val.testBit bit.val ^^
              x.1.1.sCoeff.val.testBit bit.val) ^^
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.sCoeff.val x.1.1.rCoeff.val bit.val)) := by
      simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        coeffAdderRCoeffValueWord_get_testBit,
        coeffAdderSCoeffValueWord_get_testBit, Bool.xor_assoc] using hright
    _ = (x.1.1.rCoeff + x.1.1.sCoeff).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using hadd

/-- Word-level clean-input endpoint for the `s`-into-`r` coefficient adder. -/
lemma coefficientAddSIntoRStep_get_rCoeff_add_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coefficientAddSIntoRStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  exact coefficientAddSIntoRStep_get_rCoeff_add_testBit_of_clean
    n counterWidth bit x hcarry hwork

/-- On clean coefficient-adder work inputs, the `s`-into-`r` adder restores each
temporary carry-work bit to false. -/
lemma coefficientAddSIntoRStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hclean :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x = false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coefficientAddSIntoRStep n counterWidth x) =
      false := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (coefficientAddSIntoRLayout n counterWidth) bit x hclean
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The `s`-into-`r` coefficient adder preserves any observed readout whose
wire is disjoint from every `r` target bit and every temporary carry-work bit. -/
lemma coefficientAddSIntoRStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hright :
      ∀ i : Fin (n + 1),
        ((coeffAdderRCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (hwork :
      ∀ j : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).wire ≠
          observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coefficientAddSIntoRStep n counterWidth x) =
      observed.get x := by
  have hrightValue :
      ∀ i : Fin (n + 1),
        ((coefficientAddSIntoRLayout n counterWidth).right.bit i).wire ≠
          observed.wire := by
    intro i
    simpa [coefficientAddSIntoRLayout, coeffAdderRCoeffValueWord,
      coeffAdderRCoeffWord, liftedRCoeffValueWord, liftedRCoeffWord,
      RegisterBits.rCoeffValueBit] using
      hright (WireAddress.littleEndianWire i)
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coefficientAddSIntoRLayout n counterWidth) observed hrightValue hwork x
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The `s`-into-`r` coefficient adder preserves the comparison ancilla. -/
lemma coefficientAddSIntoRStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderCompareBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          (liftedCompareBit n counterWidth)
          (Ne.symm
            (liftedCompare_liftedRCoeffWordBit_wire_ne
              n counterWidth i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedCompareBit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `s`-into-`r` coefficient adder preserves the active flag. -/
lemma coefficientAddSIntoRStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderActiveBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          (liftedActiveBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.rCoeffBit n counterWidth i)
            (RegisterBits.activeBit n counterWidth)
            (Ne.symm (RegisterBits.active_rCoeff_wire_ne
              n counterWidth i))))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedActiveBit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `s`-into-`r` coefficient adder preserves every stored branch-history
bit. -/
lemma coefficientAddSIntoRStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderHistoryBit n counterWidth historyIndex)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          (liftedHistoryBit n counterWidth historyIndex)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.rCoeffBit n counterWidth i)
            (RegisterBits.historyBit n counterWidth historyIndex)
            (RegisterBits.rCoeff_history_wire_ne n counterWidth i
              historyIndex)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedHistoryBit n counterWidth historyIndex)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `s`-into-`r` coefficient adder preserves the first scratch bit. -/
lemma coefficientAddSIntoRStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderScratchABit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          (liftedScratchABit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.rCoeffBit n counterWidth i)
            (RegisterBits.scratchABit n counterWidth)
            (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedScratchABit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `s`-into-`r` coefficient adder preserves the second scratch bit. -/
lemma coefficientAddSIntoRStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderScratchBBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          (liftedScratchBBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.rCoeffBit n counterWidth i)
            (RegisterBits.scratchBBit n counterWidth)
            (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedScratchBBit n counterWidth)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `s`-into-`r` coefficient adder preserves every comparison-work carry
bit. -/
lemma coefficientAddSIntoRStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth (coeffAdderComparisonCarryBit n counterWidth workBit)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          (liftedComparisonCarryBit n counterWidth workBit)
          (liftedRCoeffWordBit_liftedComparisonCarry_wire_ne
            n counterWidth i workBit))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth
            (liftedComparisonCarryBit n counterWidth workBit)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `s`-into-`r` coefficient adder preserves every `u` value bit. -/
lemma coefficientAddSIntoRStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coefficientAddSIntoRStep n counterWidth x) =
      ((coeffAdderUWord n counterWidth).bit bit).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth ((coeffAdderUWord n counterWidth).bit bit)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          ((liftedUWord n counterWidth).bit bit)
          (Ne.symm
            (liftedUWordBit_liftedRCoeffWordBit_wire_ne
              n counterWidth bit i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth ((liftedUWord n counterWidth).bit bit)
            (coeffAdderCarryWorkBit n j)))
      x

/-- The `s`-into-`r` coefficient adder preserves every `v` value bit. -/
lemma coefficientAddSIntoRStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coefficientAddSIntoRStep n counterWidth x) =
      ((coeffAdderVWord n counterWidth).bit bit).get x := by
  exact
    coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth ((coeffAdderVWord n counterWidth).bit bit)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedRCoeffWord n counterWidth).bit i)
          ((liftedVWord n counterWidth).bit bit)
          (Ne.symm
            (liftedVWordBit_liftedRCoeffWordBit_wire_ne
              n counterWidth bit i)))
      (fun j =>
        Ne.symm
          (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth ((liftedVWord n counterWidth).bit bit)
            (coeffAdderCarryWorkBit n j)))
      x

/-! ## Compare-selected coefficient-add data paths -/

/-- The `r`-into-`s` coefficient-add gate list is disjoint from compare. -/
lemma coefficientAddRIntoSGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddRIntoSGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (coeffAdderCompareBit n counterWidth) gate := by
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coefficientAddRIntoSLayout n counterWidth)
      (coeffAdderCompareBit n counterWidth)
      (fun i =>
        by
          simpa [coefficientAddRIntoSLayout, coeffAdderRCoeffValueWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedRCoeffValueWordBit_wire_ne
                  n counterWidth i)))
      (fun i =>
        by
          simpa [coefficientAddRIntoSLayout, coeffAdderSCoeffValueWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedSCoeffValueWordBit_wire_ne
                  n counterWidth i)))
      (by
        simpa [coefficientAddRIntoSLayout, coeffAdderCompareBit,
          liftedCoeffAdderCarryInBit] using
          Ne.symm
            (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (coeffAdderCarryInWorkBit n)))
      (fun j =>
        by
          simpa [coefficientAddRIntoSLayout, coeffAdderCompareBit,
            liftedCoeffAdderCarryWorkWord, liftedCoeffAdderCarryWorkBit] using
            Ne.symm
              (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                n counterWidth (liftedCompareBit n counterWidth)
                (coeffAdderCarryWorkBit n j)))

/-- The `r`-into-`s` coefficient-add gate list is disjoint from `scratchA`,
which can serve as the clean control-work bit for coefficient-add wrappers. -/
lemma coefficientAddRIntoSGates_bitDisjoint_scratchA
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddRIntoSGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (coeffAdderScratchABit n counterWidth) gate := by
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coefficientAddRIntoSLayout n counterWidth)
      (coeffAdderScratchABit n counterWidth)
      (fun i =>
        by
          simpa [coefficientAddRIntoSLayout] using
            Ne.symm
              (coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne
                n counterWidth i))
      (fun i =>
        by
          simpa [coefficientAddRIntoSLayout] using
            Ne.symm
              (coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne
                n counterWidth i))
      (by
        simpa [coefficientAddRIntoSLayout, coeffAdderScratchABit,
          liftedCoeffAdderCarryInBit] using
          Ne.symm
            (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth (liftedScratchABit n counterWidth)
              (coeffAdderCarryInWorkBit n)))
      (fun j =>
        by
          simpa [coefficientAddRIntoSLayout, coeffAdderScratchABit,
            liftedCoeffAdderCarryWorkWord, liftedCoeffAdderCarryWorkBit] using
            Ne.symm
              (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                n counterWidth (liftedScratchABit n counterWidth)
                (coeffAdderCarryWorkBit n j)))

/-- The `s`-into-`r` coefficient-add gate list is disjoint from compare. -/
lemma coefficientAddSIntoRGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddSIntoRGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (coeffAdderCompareBit n counterWidth) gate := by
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coefficientAddSIntoRLayout n counterWidth)
      (coeffAdderCompareBit n counterWidth)
      (fun i =>
        by
          simpa [coefficientAddSIntoRLayout, coeffAdderSCoeffValueWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedSCoeffValueWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedSCoeffValueWordBit_wire_ne
                  n counterWidth i)))
      (fun i =>
        by
          simpa [coefficientAddSIntoRLayout, coeffAdderRCoeffValueWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedRCoeffValueWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedRCoeffValueWordBit_wire_ne
                  n counterWidth i)))
      (by
        simpa [coefficientAddSIntoRLayout, coeffAdderCompareBit,
          liftedCoeffAdderCarryInBit] using
          Ne.symm
            (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (coeffAdderCarryInWorkBit n)))
      (fun j =>
        by
          simpa [coefficientAddSIntoRLayout, coeffAdderCompareBit,
            liftedCoeffAdderCarryWorkWord, liftedCoeffAdderCarryWorkBit] using
            Ne.symm
              (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                n counterWidth (liftedCompareBit n counterWidth)
                (coeffAdderCarryWorkBit n j)))

/-- The `s`-into-`r` coefficient-add gate list is disjoint from `scratchA`,
which can serve as the clean control-work bit for coefficient-add wrappers. -/
lemma coefficientAddSIntoRGates_bitDisjoint_scratchA
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddSIntoRGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (coeffAdderScratchABit n counterWidth) gate := by
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coefficientAddSIntoRLayout n counterWidth)
      (coeffAdderScratchABit n counterWidth)
      (fun i =>
        by
          simpa [coefficientAddSIntoRLayout] using
            Ne.symm
              (coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne
                n counterWidth i))
      (fun i =>
        by
          simpa [coefficientAddSIntoRLayout] using
            Ne.symm
              (coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne
                n counterWidth i))
      (by
        simpa [coefficientAddSIntoRLayout, coeffAdderScratchABit,
          liftedCoeffAdderCarryInBit] using
          Ne.symm
            (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth (liftedScratchABit n counterWidth)
              (coeffAdderCarryInWorkBit n)))
      (fun j =>
        by
          simpa [coefficientAddSIntoRLayout, coeffAdderScratchABit,
            liftedCoeffAdderCarryWorkWord, liftedCoeffAdderCarryWorkBit] using
            Ne.symm
              (liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                n counterWidth (liftedScratchABit n counterWidth)
                (coeffAdderCarryWorkBit n j)))

/-- Compare-false-controlled coefficient add for the `s := s + r` data path.
The wrapper uses `scratchA` as the clean control-work bit; the coefficient
adder itself uses the dedicated coefficient carry-in/work word. -/
def coeffWorkCompareFalseControlledAddRIntoSGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  [EncodedBit.GateSpec.x (coeffAdderCompareBit n counterWidth)] ++
  EncodedBit.GateSpec.controlledListWithWorkGates
    (coeffAdderCompareBit n counterWidth)
    (coeffAdderScratchABit n counterWidth)
    (coefficientAddRIntoSGates n counterWidth)
    (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
    (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
    (by
      simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
        Ne.symm
          (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
            n counterWidth)) ++
  [EncodedBit.GateSpec.x (coeffAdderCompareBit n counterWidth)]

/-- Step function for compare-false-controlled `s := s + r`. -/
def coeffWorkCompareFalseControlledAddRIntoSStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (coeffWorkCompareFalseControlledAddRIntoSGates n counterWidth)

/-- Circuit for compare-false-controlled `s := s + r`. -/
def coeffWorkCompareFalseControlledAddRIntoSProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareFalseControlledAddRIntoSGates n counterWidth)

/-- The compare-false-controlled `s := s + r` circuit realizes its step. -/
lemma coeffWorkCompareFalseControlledAddRIntoS_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareFalseControlledAddRIntoSProgram n counterWidth) environment
      (coeffWorkCompareFalseControlledAddRIntoSStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkCompareFalseControlledAddRIntoSGates n counterWidth)

/-- If compare is false and `scratchA` is clean, the compare-false wrapper acts
like the concrete `s := s + r` coefficient add. -/
lemma
    coeffWorkCompareFalseControlledAddRIntoSStep_eq_addRIntoS_of_compare_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hwork : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareFalseControlledAddRIntoSStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth x := by
  let compare := coeffAdderCompareBit n counterWidth
  let work := coeffAdderScratchABit n counterWidth
  let gates := coefficientAddRIntoSGates n counterWidth
  have hcompareFlip : compare.get (compare.flip x) = true := by
    dsimp [compare]
    rw [EncodedBit.get_flip_self, hcompare]
    rfl
  have hworkFlip : work.get (compare.flip x) = false := by
    dsimp [work, compare]
    rw [EncodedBit.get_flip_of_wire_ne
      (coeffAdderCompareBit n counterWidth)
      (coeffAdderScratchABit n counterWidth)]
    · exact hwork
    · simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
        Ne.symm
          (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
            n counterWidth)
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
            (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
            (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
            (by
              dsimp [compare, work]
              simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
                Ne.symm
                  (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
                    n counterWidth)))
          (compare.flip x) =
        EncodedBit.GateSpec.stepList gates (compare.flip x) := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
        compare work gates
        (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
        (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
        (by
          dsimp [compare, work]
          simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
            Ne.symm
              (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
                n counterWidth))
        (compare.flip x) hcompareFlip hworkFlip
  have hcomm :
      EncodedBit.GateSpec.stepList gates (compare.flip x) =
        compare.flip (EncodedBit.GateSpec.stepList gates x) := by
    exact EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
      gates compare
      (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth) x
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
          (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
          (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
          (by
            dsimp [compare, work]
            simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
              Ne.symm
                (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
                  n counterWidth)) ++
        [EncodedBit.GateSpec.x compare])
      (compare.flip x) =
    coefficientAddRIntoSStep n counterWidth x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle]
  rw [hcomm]
  simp [coefficientAddRIntoSStep, coefficientAddRIntoSGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step, gates,
    EncodedBit.flip_flip]

/-- If compare is true, the compare-false-controlled `s := s + r` coefficient
add is a no-op. -/
lemma coeffWorkCompareFalseControlledAddRIntoSStep_eq_self_of_compare_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true) :
    coeffWorkCompareFalseControlledAddRIntoSStep n counterWidth x = x := by
  let compare := coeffAdderCompareBit n counterWidth
  let work := coeffAdderScratchABit n counterWidth
  let gates := coefficientAddRIntoSGates n counterWidth
  have hcompareFlip : compare.get (compare.flip x) = false := by
    dsimp [compare]
    rw [EncodedBit.get_flip_self, hcompare]
    rfl
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
            (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
            (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
            (by
              dsimp [compare, work]
              simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
                Ne.symm
                  (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
                    n counterWidth)))
          (compare.flip x) =
        compare.flip x := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        compare work gates
        (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
        (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
        (by
          dsimp [compare, work]
          simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
            Ne.symm
              (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
                n counterWidth))
        (compare.flip x) hcompareFlip
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
          (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
          (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
          (by
            dsimp [compare, work]
            simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
              Ne.symm
                (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
                  n counterWidth)) ++
        [EncodedBit.GateSpec.x compare])
      (compare.flip x) = x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle]
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.flip_flip]

/-- Compare-controlled coefficient add for the `r := r + s` data path. -/
def coeffWorkCompareControlledAddSIntoRGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (coeffAdderCompareBit n counterWidth)
    (coeffAdderScratchABit n counterWidth)
    (coefficientAddSIntoRGates n counterWidth)
    (coefficientAddSIntoRGates_bitDisjoint_compare n counterWidth)
    (coefficientAddSIntoRGates_bitDisjoint_scratchA n counterWidth)
    (by
      simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
        Ne.symm
          (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
            n counterWidth))

/-- Step function for compare-controlled `r := r + s`. -/
def coeffWorkCompareControlledAddSIntoRStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (coeffWorkCompareControlledAddSIntoRGates n counterWidth)

/-- Circuit for compare-controlled `r := r + s`. -/
def coeffWorkCompareControlledAddSIntoRProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareControlledAddSIntoRGates n counterWidth)

/-- The compare-controlled `r := r + s` circuit realizes its step. -/
lemma coeffWorkCompareControlledAddSIntoR_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareControlledAddSIntoRProgram n counterWidth) environment
      (coeffWorkCompareControlledAddSIntoRStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkCompareControlledAddSIntoRGates n counterWidth)

/-- If compare is false, the compare-controlled `r := r + s` coefficient add
is a no-op. -/
lemma coeffWorkCompareControlledAddSIntoRStep_eq_self_of_compare_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    coeffWorkCompareControlledAddSIntoRStep n counterWidth x = x := by
  simpa [coeffWorkCompareControlledAddSIntoRStep,
    coeffWorkCompareControlledAddSIntoRGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (coeffAdderCompareBit n counterWidth)
      (coeffAdderScratchABit n counterWidth)
      (coefficientAddSIntoRGates n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_compare n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_scratchA n counterWidth)
      (by
        simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
          Ne.symm
            (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
              n counterWidth))
      x hcompare

/-- If compare is true and `scratchA` is clean, the compare-controlled wrapper
acts like the concrete `r := r + s` coefficient add. -/
lemma coeffWorkCompareControlledAddSIntoRStep_eq_addSIntoR_of_compare_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hwork : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareControlledAddSIntoRStep n counterWidth x =
      coefficientAddSIntoRStep n counterWidth x := by
  simpa [coeffWorkCompareControlledAddSIntoRStep,
    coeffWorkCompareControlledAddSIntoRGates, coefficientAddSIntoRStep,
    coefficientAddSIntoRGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (coeffAdderCompareBit n counterWidth)
      (coeffAdderScratchABit n counterWidth)
      (coefficientAddSIntoRGates n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_compare n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_scratchA n counterWidth)
      (by
        simpa [coeffAdderCompareBit, coeffAdderScratchABit] using
          Ne.symm
            (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
              n counterWidth))
      x hcompare hwork

/-- Compare-selected coefficient-add atom for the odd-odd data path.  It
executes `r := r + s` when compare is true and `s := s + r` when compare is
false, using `scratchA` only as the clean control-work bit. -/
def coeffWorkCompareSelectedCoefficientAddGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  coeffWorkCompareControlledAddSIntoRGates n counterWidth ++
    coeffWorkCompareFalseControlledAddRIntoSGates n counterWidth

/-- Base-gate program for the compare-selected coefficient-add atom. -/
def coeffWorkCompareSelectedCoefficientAddProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectedCoefficientAddGates n counterWidth)

/-- Compare-selected coefficient-add atom for the odd-odd data path.  It
executes `r := r + s` when compare is true and `s := s + r` when compare is
false, using `scratchA` only as the clean control-work bit. -/
def coeffWorkCompareSelectedCoefficientAddStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkCompareFalseControlledAddRIntoSStep n counterWidth
      (coeffWorkCompareControlledAddSIntoRStep n counterWidth x)

/-- The explicit compare-selected coefficient-add gate list has the same
folded semantics as the sequential selected coefficient-add step. -/
lemma coeffWorkCompareSelectedCoefficientAddStep_eq_gateList
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkCompareSelectedCoefficientAddGates n counterWidth) x =
      coeffWorkCompareSelectedCoefficientAddStep n counterWidth x := by
  rw [coeffWorkCompareSelectedCoefficientAddGates,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- The compare-selected coefficient-add gate list realizes the sequential
selected coefficient-add step. -/
lemma coeffWorkCompareSelectedCoefficientAdd_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareSelectedCoefficientAddProgram n counterWidth) environment
      (coeffWorkCompareSelectedCoefficientAddStep n counterWidth) := by
  exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectedCoefficientAddGates n counterWidth)
    (coeffWorkCompareSelectedCoefficientAddStep_eq_gateList n counterWidth)

/-- If compare is true and `scratchA` is clean, the selected coefficient-add
atom reduces to `r := r + s`. -/
lemma
    coeffWorkCompareSelectedCoefficientAddStep_eq_addSIntoR_of_compare_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hwork : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareSelectedCoefficientAddStep n counterWidth x =
      coefficientAddSIntoRStep n counterWidth x := by
  have hfirst :
      coeffWorkCompareControlledAddSIntoRStep n counterWidth x =
        coefficientAddSIntoRStep n counterWidth x :=
    coeffWorkCompareControlledAddSIntoRStep_eq_addSIntoR_of_compare_true
      n counterWidth x hcompare hwork
  have hcompareFirst :
      (coeffAdderCompareBit n counterWidth).get
          (coeffWorkCompareControlledAddSIntoRStep n counterWidth x) =
        true := by
    rw [hfirst, coefficientAddSIntoRStep_get_compare]
    exact hcompare
  rw [coeffWorkCompareSelectedCoefficientAddStep]
  rw [coeffWorkCompareFalseControlledAddRIntoSStep_eq_self_of_compare_true
    n counterWidth
    (coeffWorkCompareControlledAddSIntoRStep n counterWidth x)
    hcompareFirst]
  exact hfirst

/-- If compare is false and `scratchA` is clean, the selected coefficient-add
atom reduces to `s := s + r`. -/
lemma
    coeffWorkCompareSelectedCoefficientAddStep_eq_addRIntoS_of_compare_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hwork : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareSelectedCoefficientAddStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth x := by
  have hfirst :
      coeffWorkCompareControlledAddSIntoRStep n counterWidth x = x :=
    coeffWorkCompareControlledAddSIntoRStep_eq_self_of_compare_false
      n counterWidth x hcompare
  rw [coeffWorkCompareSelectedCoefficientAddStep]
  rw [hfirst]
  exact
    coeffWorkCompareFalseControlledAddRIntoSStep_eq_addRIntoS_of_compare_false
      n counterWidth x hcompare hwork

/-! ## Source-register subtraction data paths -/

/-- Carry-work layout for the concrete reverse-adder data path
`u := u - v`.  The forward direction adds `v` into `u`; the subtract path uses
the reverse gate list. -/
def coeffWorkAddVIntoULayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := registersWithCoeffAdderWorkEncoding n counterWidth) n where
  left := coeffAdderVWord n counterWidth
  right := coeffAdderUWord n counterWidth
  carryIn := coeffAdderScratchABit n counterWidth
  workCarry := coeffAdderComparisonCarryPrefixWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact coeffAdderVWordBit_coeffAdderVWordBit_wire_ne
      n counterWidth i j hij
  rightRight_ne := by
    intro i j hij
    exact coeffAdderUWordBit_coeffAdderUWordBit_wire_ne
      n counterWidth i j hij
  leftRight_ne := by
    intro i j
    exact Ne.symm
      (coeffAdderUWordBit_coeffAdderVWordBit_wire_ne n counterWidth j i)
  leftCarryIn_ne := by
    intro i
    exact Ne.symm
      (coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
  rightCarryIn_ne := by
    intro i
    exact Ne.symm
      (coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
  leftWork_ne := by
    intro i j
    exact coeffAdderVWordBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth i (coeffAdderComparisonCarryPrefixIndex n j)
  rightWork_ne := by
    intro i j
    exact coeffAdderUWordBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth i (coeffAdderComparisonCarryPrefixIndex n j)
  carryInWork_ne := by
    intro j
    exact coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth (coeffAdderComparisonCarryPrefixIndex n j)
  workWork_ne := by
    intro i j hij
    exact coeffAdderComparisonCarryBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth (coeffAdderComparisonCarryPrefixIndex n i)
      (coeffAdderComparisonCarryPrefixIndex n j)
      (coeffAdderComparisonCarryPrefixIndex_ne n hij)

/-- Carry-work layout for the concrete reverse-adder data path
`v := v - u`.  The forward direction adds `u` into `v`; the subtract path uses
the reverse gate list. -/
def coeffWorkAddUIntoVLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := registersWithCoeffAdderWorkEncoding n counterWidth) n where
  left := coeffAdderUWord n counterWidth
  right := coeffAdderVWord n counterWidth
  carryIn := coeffAdderScratchABit n counterWidth
  workCarry := coeffAdderComparisonCarryPrefixWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact coeffAdderUWordBit_coeffAdderUWordBit_wire_ne
      n counterWidth i j hij
  rightRight_ne := by
    intro i j hij
    exact coeffAdderVWordBit_coeffAdderVWordBit_wire_ne
      n counterWidth i j hij
  leftRight_ne := by
    intro i j
    exact coeffAdderUWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
  leftCarryIn_ne := by
    intro i
    exact Ne.symm
      (coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
  rightCarryIn_ne := by
    intro i
    exact Ne.symm
      (coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
  leftWork_ne := by
    intro i j
    exact coeffAdderUWordBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth i (coeffAdderComparisonCarryPrefixIndex n j)
  rightWork_ne := by
    intro i j
    exact coeffAdderVWordBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth i (coeffAdderComparisonCarryPrefixIndex n j)
  carryInWork_ne := by
    intro j
    exact coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth (coeffAdderComparisonCarryPrefixIndex n j)
  workWork_ne := by
    intro i j hij
    exact coeffAdderComparisonCarryBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth (coeffAdderComparisonCarryPrefixIndex n i)
      (coeffAdderComparisonCarryPrefixIndex n j)
      (coeffAdderComparisonCarryPrefixIndex_ne n hij)

/-- Gate list for the concrete source-register adder `u := u + v` in the
coefficient-work layout. -/
def coeffWorkAddVIntoUGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (coeffWorkAddVIntoULayout n counterWidth)

/-- Step function realized by `coeffWorkAddVIntoUGates`. -/
def coeffWorkAddVIntoUStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList (coeffWorkAddVIntoUGates n counterWidth)

/-- Circuit for the concrete source-register adder `u := u + v`. -/
def coeffWorkAddVIntoUProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkAddVIntoUGates n counterWidth)

/-- The concrete source-register adder circuit realizes `u := u + v`. -/
lemma coeffWorkAddVIntoU_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAddVIntoUProgram n counterWidth) environment
      (coeffWorkAddVIntoUStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkAddVIntoUGates n counterWidth)

/-- Reverse gate list used as the concrete source-register subtract path
`u := u - v`. -/
def coeffWorkSubVFromUGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  (coeffWorkAddVIntoUGates n counterWidth).reverse

/-- Exact physical length of the `u := u - v` source-register path. -/
lemma coeffWorkSubVFromUGates_length (n counterWidth : Nat) :
    (coeffWorkSubVFromUGates n counterWidth).length =
      6 * (n - 1) + 2 * n := by
  simpa only [coeffWorkSubVFromUGates, coeffWorkAddVIntoUGates,
    List.length_reverse] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length
      (coeffWorkAddVIntoULayout n counterWidth))

/-- The `u := u - v` source-register path has no X leaf. -/
lemma coeffWorkSubVFromUGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((coeffWorkSubVFromUGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp only [coeffWorkSubVFromUGates, coeffWorkAddVIntoUGates,
    List.map_reverse, List.sum_reverse,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum]

/-- Exact CNOT coordinate of the `u := u - v` source-register path. -/
lemma coeffWorkSubVFromUGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkSubVFromUGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * n := by
  simp only [coeffWorkSubVFromUGates, coeffWorkAddVIntoUGates,
    List.map_reverse, List.sum_reverse,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate of the `u := u - v` source-register path. -/
lemma coeffWorkSubVFromUGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkSubVFromUGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * (n - 1) := by
  simp only [coeffWorkSubVFromUGates, coeffWorkAddVIntoUGates,
    List.map_reverse, List.sum_reverse,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum]

/-- Step function realized by `coeffWorkSubVFromUGates`. -/
def coeffWorkSubVFromUStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList (coeffWorkSubVFromUGates n counterWidth)

/-- Circuit for the concrete source-register subtract path `u := u - v`. -/
def coeffWorkSubVFromUProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkSubVFromUGates n counterWidth)

/-- The concrete source-register subtract circuit realizes `u := u - v`. -/
lemma coeffWorkSubVFromU_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkSubVFromUProgram n counterWidth) environment
      (coeffWorkSubVFromUStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkSubVFromUGates n counterWidth)

/-- The concrete `u := u - v` source-subtract gate list is disjoint from the
staged compare bit. -/
lemma coeffWorkSubVFromUGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coeffWorkSubVFromUGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (coeffAdderCompareBit n counterWidth) gate := by
  intro gate hmem
  have hforward :
      gate ∈ coeffWorkAddVIntoUGates n counterWidth := by
    simpa [coeffWorkSubVFromUGates] using hmem
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coeffWorkAddVIntoULayout n counterWidth)
      (coeffAdderCompareBit n counterWidth)
      (fun i =>
        by
          simpa [coeffWorkAddVIntoULayout, coeffAdderVWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedVWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedVWordBit_wire_ne n counterWidth i)))
      (fun i =>
        by
          simpa [coeffWorkAddVIntoULayout, coeffAdderUWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedUWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedUWordBit_wire_ne n counterWidth i)))
      (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne n counterWidth)
      (fun j =>
        by
          simpa [coeffWorkAddVIntoULayout,
            coeffAdderComparisonCarryPrefixWord] using
            Ne.symm
              (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
                n counterWidth (coeffAdderComparisonCarryPrefixIndex n j)))
      gate hforward

/-- The concrete `u := u - v` source-subtract gate list is disjoint from the
dedicated coefficient-adder carry-in bit, which can therefore serve as the
extra clean control-work bit for this source-subtract-only wrapper. -/
lemma coeffWorkSubVFromUGates_bitDisjoint_coeffCarryIn
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coeffWorkSubVFromUGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (liftedCoeffAdderCarryInBit n counterWidth) gate := by
  intro gate hmem
  have hforward :
      gate ∈ coeffWorkAddVIntoUGates n counterWidth := by
    simpa [coeffWorkSubVFromUGates] using hmem
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coeffWorkAddVIntoULayout n counterWidth)
      (liftedCoeffAdderCarryInBit n counterWidth)
      (fun i =>
        by
          simpa [coeffWorkAddVIntoULayout, coeffAdderVWord,
            liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth ((liftedVWord n counterWidth).bit i)
              (coeffAdderCarryInWorkBit n))
      (fun i =>
        by
          simpa [coeffWorkAddVIntoULayout, coeffAdderUWord,
            liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth ((liftedUWord n counterWidth).bit i)
              (coeffAdderCarryInWorkBit n))
      (by
        simpa [coeffWorkAddVIntoULayout, coeffAdderScratchABit,
          liftedCoeffAdderCarryInBit] using
          liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedScratchABit n counterWidth)
            (coeffAdderCarryInWorkBit n))
      (fun j =>
        by
          simpa [coeffWorkAddVIntoULayout,
            coeffAdderComparisonCarryPrefixWord,
            coeffAdderComparisonCarryBit,
            liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth
              (liftedComparisonCarryBit n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))
              (coeffAdderCarryInWorkBit n))
      gate hforward

/-- Compare-controlled source-subtract gate list for the `u := u - v` data
path.  This controls only the source subtract list; it does not include the
coefficient add path that reuses the dedicated carry-in bit. -/
def coeffWorkCompareControlledSubVFromUGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (coeffAdderCompareBit n counterWidth)
    (liftedCoeffAdderCarryInBit n counterWidth)
    (coeffWorkSubVFromUGates n counterWidth)
    (coeffWorkSubVFromUGates_bitDisjoint_compare n counterWidth)
    (coeffWorkSubVFromUGates_bitDisjoint_coeffCarryIn n counterWidth)
    (by
      simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
          n counterWidth (liftedCompareBit n counterWidth)
          (coeffAdderCarryInWorkBit n))

/-- Step function for compare-controlled `u := u - v` source subtract. -/
def coeffWorkCompareControlledSubVFromUStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (coeffWorkCompareControlledSubVFromUGates n counterWidth)

/-- Circuit for compare-controlled `u := u - v` source subtract. -/
def coeffWorkCompareControlledSubVFromUProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareControlledSubVFromUGates n counterWidth)

/-- The compare-controlled `u := u - v` circuit realizes its step. -/
lemma coeffWorkCompareControlledSubVFromU_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareControlledSubVFromUProgram n counterWidth) environment
      (coeffWorkCompareControlledSubVFromUStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkCompareControlledSubVFromUGates n counterWidth)

/-- If compare is false, the compare-controlled `u := u - v` source subtract is
a no-op. -/
lemma coeffWorkCompareControlledSubVFromUStep_eq_self_of_compare_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    coeffWorkCompareControlledSubVFromUStep n counterWidth x = x := by
  simpa [coeffWorkCompareControlledSubVFromUStep,
    coeffWorkCompareControlledSubVFromUGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (coeffAdderCompareBit n counterWidth)
      (liftedCoeffAdderCarryInBit n counterWidth)
      (coeffWorkSubVFromUGates n counterWidth)
      (coeffWorkSubVFromUGates_bitDisjoint_compare n counterWidth)
      (coeffWorkSubVFromUGates_bitDisjoint_coeffCarryIn n counterWidth)
      (by
        simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
          liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedCompareBit n counterWidth)
            (coeffAdderCarryInWorkBit n))
      x hcompare

/-- If compare is true and the dedicated coefficient carry-in is clean, the
compare-controlled wrapper acts like the concrete `u := u - v` source-subtract
path. -/
lemma coeffWorkCompareControlledSubVFromUStep_eq_subVFromU_of_compare_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hwork : (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    coeffWorkCompareControlledSubVFromUStep n counterWidth x =
      coeffWorkSubVFromUStep n counterWidth x := by
  simpa [coeffWorkCompareControlledSubVFromUStep,
    coeffWorkCompareControlledSubVFromUGates, coeffWorkSubVFromUStep,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (coeffAdderCompareBit n counterWidth)
      (liftedCoeffAdderCarryInBit n counterWidth)
      (coeffWorkSubVFromUGates n counterWidth)
      (coeffWorkSubVFromUGates_bitDisjoint_compare n counterWidth)
      (coeffWorkSubVFromUGates_bitDisjoint_coeffCarryIn n counterWidth)
      (by
        simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
          liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedCompareBit n counterWidth)
            (coeffAdderCarryInWorkBit n))
      x hcompare hwork

lemma coeffWorkSubVFromUStep_comp_addVIntoU
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    coeffWorkSubVFromUStep n counterWidth
        (coeffWorkAddVIntoUStep n counterWidth x) =
      x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (coeffWorkAddVIntoUGates n counterWidth) x

lemma coeffWorkAddVIntoUStep_comp_subVFromU
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    coeffWorkAddVIntoUStep n counterWidth
        (coeffWorkSubVFromUStep n counterWidth x) =
      x := by
  have h :=
    EncodedBit.GateSpec.stepList_reverse_stepList
      (coeffWorkAddVIntoUGates n counterWidth).reverse x
  simpa [coeffWorkAddVIntoUStep, coeffWorkSubVFromUStep,
    coeffWorkSubVFromUGates] using h

/-- The forward `v`-into-`u` adder preserves the scratchA carry-in bit. -/
lemma coeffWorkAddVIntoUStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (coeffWorkAddVIntoULayout n counterWidth) x
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout] using h

/-- The forward `v`-into-`u` source adder preserves any observed readout whose
wire is disjoint from every `u` target bit and every comparison-prefix
carry-work bit. -/
lemma coeffWorkAddVIntoUStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hright :
      ∀ i : Fin n,
        ((coeffAdderUWord n counterWidth).bit i).wire ≠ observed.wire)
    (hwork :
      ∀ j : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).wire ≠
          observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkAddVIntoUStep n counterWidth x) =
      observed.get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddVIntoULayout n counterWidth) observed hright hwork x
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout] using h

/-- The forward `v`-into-`u` source adder preserves the active flag. -/
lemma coeffWorkAddVIntoUStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  exact
    coeffWorkAddVIntoUStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderActiveBit n counterWidth)
      (fun i =>
        Ne.symm (coeffAdderActiveBit_coeffAdderUWordBit_wire_ne
          n counterWidth i))
      (fun j => by
        simpa [coeffAdderComparisonCarryPrefixWord,
          coeffAdderComparisonCarryBit, coeffAdderActiveBit] using
          Ne.symm
            (liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth (liftedActiveBit n counterWidth)
              (liftedComparisonCarryBit n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))
              (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
                (RegisterBits.activeBit n counterWidth)
                (comparisonCarryValueBit n
                  (coeffAdderComparisonCarryPrefixIndex n j)))))
      x

/-- The forward `v`-into-`u` source adder preserves the comparison ancilla. -/
lemma coeffWorkAddVIntoUStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  exact
    coeffWorkAddVIntoUStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderCompareBit n counterWidth)
      (fun i =>
        Ne.symm
          (liftComparisonStateBit_liftComparisonStateBit_wire_ne
            n counterWidth (liftedCompareBit n counterWidth)
            ((liftedUWord n counterWidth).bit i)
            (liftedCompare_liftedUWordBit_wire_ne n counterWidth i)))
      (fun j => by
        simpa [coeffAdderComparisonCarryPrefixWord,
          coeffAdderComparisonCarryBit, coeffAdderCompareBit] using
          Ne.symm
            (liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (liftedComparisonCarryBit n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))
              (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))))
      x

/-- The forward `v`-into-`u` source adder preserves every stored
branch-history bit. -/
lemma coeffWorkAddVIntoUStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  exact
    coeffWorkAddVIntoUStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderHistoryBit n counterWidth historyIndex)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedUWord n counterWidth).bit i)
          (liftedHistoryBit n counterWidth historyIndex)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.uValueBit n counterWidth i)
            (RegisterBits.historyBit n counterWidth historyIndex)
            (by
              simpa [RegisterBits.uValueBit] using
                RegisterBits.u_history_wire_ne n counterWidth
                  (WireAddress.littleEndianWire i) historyIndex)))
      (fun j =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth
          (liftedComparisonCarryBit n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n j))
          (liftedHistoryBit n counterWidth historyIndex)
          (Ne.symm
            (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
              (RegisterBits.historyBit n counterWidth historyIndex)
              (comparisonCarryValueBit n
                (coeffAdderComparisonCarryPrefixIndex n j)))))
      x

/-- The forward `v`-into-`u` source adder preserves the second scratch bit. -/
lemma coeffWorkAddVIntoUStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  exact
    coeffWorkAddVIntoUStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderScratchBBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedUWord n counterWidth).bit i)
          (liftedScratchBBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.uValueBit n counterWidth i)
            (RegisterBits.scratchBBit n counterWidth)
            (by
              simpa [RegisterBits.uValueBit] using
                RegisterBits.u_scratchB_wire_ne n counterWidth
                  (WireAddress.littleEndianWire i))))
      (fun j => by
        simpa [coeffAdderComparisonCarryPrefixWord,
          coeffAdderComparisonCarryBit] using
          Ne.symm
            (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
              n counterWidth (coeffAdderComparisonCarryPrefixIndex n j)))
      x

/-- If the input scratchA carry-in is clean, the reverse `u := u - v` path
also lands on clean scratchA. -/
lemma coeffWorkSubVFromUStep_get_scratchA_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      false := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_scratchA n counterWidth
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        (coeffAdderScratchABit n counterWidth).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderScratchABit n counterWidth).get x := by
      rw [hcancel]
    _ = false := hcarry

/-- The concrete `u := u - v` reverse-adder path preserves the active flag. -/
lemma coeffWorkSubVFromUStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_active n counterWidth
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        (coeffAdderActiveBit n counterWidth).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderActiveBit n counterWidth).get x := by
      rw [hcancel]

/-- The concrete `u := u - v` reverse-adder path preserves the comparison
ancilla. -/
lemma coeffWorkSubVFromUStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_compare n counterWidth
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        (coeffAdderCompareBit n counterWidth).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderCompareBit n counterWidth).get x := by
      rw [hcancel]

/-- The concrete `u := u - v` reverse-adder path preserves every stored
branch-history bit. -/
lemma coeffWorkSubVFromUStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_historyBit n counterWidth historyIndex
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        (coeffAdderHistoryBit n counterWidth historyIndex).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
      rw [hcancel]

/-- The concrete `u := u - v` reverse-adder path preserves the second scratch
bit. -/
lemma coeffWorkSubVFromUStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_scratchB n counterWidth
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        (coeffAdderScratchBBit n counterWidth).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderScratchBBit n counterWidth).get x := by
      rw [hcancel]

/-- The forward `v`-into-`u` adder preserves every source `v` bit. -/
lemma coeffWorkAddVIntoUStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      ((coeffAdderVWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (coeffWorkAddVIntoULayout n counterWidth) bit x
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout] using h

/-- The forward `v`-into-`u` adder preserves every `s` coefficient value bit. -/
lemma coeffWorkAddVIntoUStep_get_sCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddVIntoULayout n counterWidth)
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit)
      (fun i => coeffAdderUWordBit_coeffAdderSCoeffValueWordBit_wire_ne
        n counterWidth i bit)
      (fun j => by
        simpa [coeffWorkAddVIntoULayout, coeffAdderComparisonCarryPrefixWord] using
          Ne.symm
            (coeffAdderSCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
              n counterWidth bit (coeffAdderComparisonCarryPrefixIndex n j)))
      x
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout] using h

/-- The forward `v`-into-`u` adder preserves every `r` coefficient value bit. -/
lemma coeffWorkAddVIntoUStep_get_rCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddVIntoULayout n counterWidth)
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit)
      (fun i => coeffAdderUWordBit_coeffAdderRCoeffValueWordBit_wire_ne
        n counterWidth i bit)
      (fun j => by
        simpa [coeffWorkAddVIntoULayout, coeffAdderComparisonCarryPrefixWord] using
          Ne.symm
            (coeffAdderRCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
              n counterWidth bit (coeffAdderComparisonCarryPrefixIndex n j)))
      x
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout] using h

/-- The forward `v`-into-`u` adder preserves the dedicated coefficient-adder
carry-in flag. -/
lemma coeffWorkAddVIntoUStep_get_coeffCarryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddVIntoULayout n counterWidth)
      (liftedCoeffAdderCarryInBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          ((liftedUWord n counterWidth).bit i) (coeffAdderCarryInWorkBit n))
      (fun j =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          (liftedComparisonCarryBit n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n j))
          (coeffAdderCarryInWorkBit n))
      x
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout, coeffAdderComparisonCarryPrefixWord] using h

/-- The forward `v`-into-`u` adder preserves every dedicated coefficient-adder
carry-work bit. -/
lemma coeffWorkAddVIntoUStep_get_coeffCarryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddVIntoULayout n counterWidth)
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit)
      (fun i =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          ((liftedUWord n counterWidth).bit i)
          (coeffAdderCarryWorkBit n workBit))
      (fun j =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          (liftedComparisonCarryBit n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n j))
          (coeffAdderCarryWorkBit n workBit))
      x
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout, coeffAdderComparisonCarryPrefixWord] using h

/-- On clean comparison-prefix work inputs, the forward `v`-into-`u` adder
restores every comparison-prefix carry-work bit. -/
lemma coeffWorkAddVIntoUStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      false := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (coeffWorkAddVIntoULayout n counterWidth) bit x hwork
  simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
    coeffWorkAddVIntoULayout] using h

/-- On clean comparison-prefix work inputs, the concrete reverse `u := u - v`
path also lands on clean comparison-prefix carry-work bits. -/
lemma coeffWorkSubVFromUStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      false := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_reverse_get_workCarry_clean
      (coeffWorkAddVIntoULayout n counterWidth) bit x hwork
  simpa [coeffWorkSubVFromUStep, coeffWorkSubVFromUGates,
    coeffWorkAddVIntoUGates, coeffWorkAddVIntoULayout] using h

/-- On clean carry/work inputs, the forward `v`-into-`u` carry stage computes
the propagated natural addition carry. -/
lemma coeffWorkAddVIntoU_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat) (j : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coeffWorkAddVIntoULayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.v.val x.1.1.u.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (coeffWorkAddVIntoULayout n counterWidth) x
  change
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get stage =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.v.val x.1.1.u.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin (n - 1), j.val = m ->
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.v.val x.1.1.u.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (coeffWorkAddVIntoULayout n counterWidth) j x hwork
        change
          ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get
              stage =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.v.val x.1.1.u.val (j.val + 1)
        change
          ((coeffWorkAddVIntoULayout n counterWidth).workCarry.bit j).get
              ((coeffWorkAddVIntoULayout n counterWidth).carryStageIndexStep
                x) =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.v.val x.1.1.u.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (coeffWorkAddVIntoULayout n counterWidth) x
          rw [hdata]
          simp [coeffWorkAddVIntoULayout, coeffAdderVWord_get_testBit,
            coeffAdderUWord_get_testBit, hcarry,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpRec' :
              ((coeffWorkAddVIntoULayout n counterWidth).workCarry.bit p).get
                  ((coeffWorkAddVIntoULayout n counterWidth).carryStageIndexStep
                    x) =
                Nat.BinaryArithmetic.natAddCarry
                  x.1.1.v.val x.1.1.u.val (p.val + 1) := by
            simpa [stage, coeffWorkAddVIntoULayout] using hpRec
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hpRec', hpSucc]
          simp [coeffWorkAddVIntoULayout, coeffAdderVWord_get_testBit,
            coeffAdderUWord_get_testBit,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before the `v`-into-`u` target sum is the propagated
natural addition carry on clean carry/work inputs. -/
lemma coeffWorkAddVIntoU_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (coeffWorkAddVIntoULayout n counterWidth) bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coeffWorkAddVIntoULayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry x.1.1.v.val x.1.1.u.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (coeffWorkAddVIntoULayout n counterWidth) x
    rw [hdata]
    simp [coeffWorkAddVIntoULayout, hcarry,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : bit.val - 1 < n - 1 := by
      have hbit := bit.isLt
      omega
    let j : Fin (n - 1) := ⟨bit.val - 1, hjLt⟩
    have hworkCarry :=
      coeffWorkAddVIntoU_carryStage_get_workCarry_natAddCarry
        n counterWidth j x hcarry hwork
    have hjSucc : j.val + 1 = bit.val := by
      dsimp [j]
      omega
    change
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coeffWorkAddVIntoULayout n counterWidth) x) =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.v.val x.1.1.u.val bit.val
    rw [hworkCarry, hjSucc]

/-- On clean carry/work inputs, the forward `v`-into-`u` adder writes the
target `u` word as `u + v`. -/
lemma coeffWorkAddVIntoUStep_get_u_add_testBit_of_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkAddVIntoUStep n counterWidth x).1.1.u.val.testBit bit.val =
      (x.1.1.u + x.1.1.v).val.testBit bit.val := by
  have hright :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (coeffWorkAddVIntoULayout n counterWidth) bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hright
  have hcarryBit :=
    coeffWorkAddVIntoU_carryBeforeSum_get_natAddCarry
      n counterWidth bit x hcarry hwork
  rw [hcarryBit] at hright
  have hadd :=
    (word_add_testBit_eq_xor3 n x.1.1.v x.1.1.u bit).symm
  calc
    (coeffWorkAddVIntoUStep n counterWidth x).1.1.u.val.testBit bit.val =
        (((x.1.1.u.val.testBit bit.val ^^
              x.1.1.v.val.testBit bit.val) ^^
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.v.val x.1.1.u.val bit.val)) := by
      simpa [coeffWorkAddVIntoUStep, coeffWorkAddVIntoUGates,
        coeffWorkAddVIntoULayout, coeffAdderUWord_get_testBit,
        coeffAdderVWord_get_testBit, Bool.xor_assoc] using hright
    _ = (x.1.1.u + x.1.1.v).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using hadd

/-- Word-level clean-input endpoint for the forward `v`-into-`u` data path. -/
lemma coeffWorkAddVIntoUStep_get_u_add_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkAddVIntoUStep n counterWidth x).1.1.u =
      x.1.1.u + x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  exact coeffWorkAddVIntoUStep_get_u_add_testBit_of_clean
    n counterWidth bit x hcarry hwork

/-- The concrete `u := u - v` reverse-adder path preserves every source `v`
bit. -/
lemma coeffWorkSubVFromUStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      ((coeffAdderVWord n counterWidth).bit bit).get x := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_vWordBit n counterWidth bit
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        ((coeffAdderVWord n counterWidth).bit bit).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = ((coeffAdderVWord n counterWidth).bit bit).get x := by
      rw [hcancel]

/-- The concrete `u := u - v` reverse-adder path preserves the source `v`
word. -/
lemma coeffWorkSubVFromUStep_get_v
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubVFromUStep n counterWidth x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkSubVFromUStep_get_vWordBit n counterWidth bit x
  simpa [coeffAdderVWord_get_testBit] using h

/-- The concrete `u := u - v` reverse-adder path preserves the `s`
coefficient word. -/
lemma coeffWorkSubVFromUStep_get_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubVFromUStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have hadd :=
    coeffWorkAddVIntoUStep_get_sCoeffValueBit n counterWidth bit
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffWorkSubVFromUStep n counterWidth x).1.1.sCoeff.val.testBit
        bit.val =
        (coeffWorkAddVIntoUStep n counterWidth
          (coeffWorkSubVFromUStep n counterWidth x)).1.1.sCoeff.val.testBit
            bit.val := by
      simpa [coeffAdderSCoeffValueWord_get_testBit] using hadd.symm
    _ = x.1.1.sCoeff.val.testBit bit.val := by
      rw [hcancel]

/-- The concrete `u := u - v` reverse-adder path preserves the `r`
coefficient word. -/
lemma coeffWorkSubVFromUStep_get_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubVFromUStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have hadd :=
    coeffWorkAddVIntoUStep_get_rCoeffValueBit n counterWidth bit
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffWorkSubVFromUStep n counterWidth x).1.1.rCoeff.val.testBit
        bit.val =
        (coeffWorkAddVIntoUStep n counterWidth
          (coeffWorkSubVFromUStep n counterWidth x)).1.1.rCoeff.val.testBit
            bit.val := by
      simpa [coeffAdderRCoeffValueWord_get_testBit] using hadd.symm
    _ = x.1.1.rCoeff.val.testBit bit.val := by
      rw [hcancel]

/-- The concrete `u := u - v` reverse-adder path preserves the dedicated
coefficient-adder carry-in flag. -/
lemma coeffWorkSubVFromUStep_get_coeffCarryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_coeffCarryIn n counterWidth
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        (liftedCoeffAdderCarryInBit n counterWidth).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = (liftedCoeffAdderCarryInBit n counterWidth).get x := by
      rw [hcancel]

/-- The concrete `u := u - v` reverse-adder path preserves every dedicated
coefficient-adder carry-work bit. -/
lemma coeffWorkSubVFromUStep_get_coeffCarryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  have hadd :=
    coeffWorkAddVIntoUStep_get_coeffCarryWorkBit n counterWidth workBit
      (coeffWorkSubVFromUStep n counterWidth x)
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := by
      exact hadd.symm
    _ = ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
      rw [hcancel]

/-- If the reverse `u := u - v` path lands on clean carry/work, its target
word is the width-preserving subtraction endpoint. -/
lemma coeffWorkSubVFromUStep_get_u_sub_of_output_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry :
      (coeffAdderScratchABit n counterWidth).get
          (coeffWorkSubVFromUStep n counterWidth x) = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
            (coeffWorkSubVFromUStep n counterWidth x) = false) :
    (coeffWorkSubVFromUStep n counterWidth x).1.1.u =
      x.1.1.u - x.1.1.v := by
  let z := coeffWorkSubVFromUStep n counterWidth x
  have hadd :=
    coeffWorkAddVIntoUStep_get_u_add_of_clean
      n counterWidth z hcarry hwork
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  have hsource := coeffWorkSubVFromUStep_get_v n counterWidth x
  have hu :
      x.1.1.u = z.1.1.u + z.1.1.v := by
    calc
      x.1.1.u =
          (coeffWorkAddVIntoUStep n counterWidth z).1.1.u := by
        rw [hcancel]
      _ = z.1.1.u + z.1.1.v := hadd
  change z.1.1.u = x.1.1.u - x.1.1.v
  rw [← hsource]
  rw [eq_sub_iff_add_eq]
  exact hu.symm

/-- Clean-input target arithmetic endpoint for the concrete `u := u - v`
reverse-adder path. -/
lemma coeffWorkSubVFromUStep_get_u_sub_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkSubVFromUStep n counterWidth x).1.1.u =
      x.1.1.u - x.1.1.v := by
  exact coeffWorkSubVFromUStep_get_u_sub_of_output_clean
    n counterWidth x
    (coeffWorkSubVFromUStep_get_scratchA_clean n counterWidth x hcarry)
    (fun k =>
      coeffWorkSubVFromUStep_get_comparisonCarryPrefix_clean
        n counterWidth k x hwork)

/-- Gate list for the concrete source-register adder `v := v + u` in the
coefficient-work layout. -/
def coeffWorkAddUIntoVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (coeffWorkAddUIntoVLayout n counterWidth)

/-- Step function realized by `coeffWorkAddUIntoVGates`. -/
def coeffWorkAddUIntoVStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList (coeffWorkAddUIntoVGates n counterWidth)

/-- Circuit for the concrete source-register adder `v := v + u`. -/
def coeffWorkAddUIntoVProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkAddUIntoVGates n counterWidth)

/-- The concrete source-register adder circuit realizes `v := v + u`. -/
lemma coeffWorkAddUIntoV_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAddUIntoVProgram n counterWidth) environment
      (coeffWorkAddUIntoVStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkAddUIntoVGates n counterWidth)

/-- Reverse gate list used as the concrete source-register subtract path
`v := v - u`. -/
def coeffWorkSubUFromVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  (coeffWorkAddUIntoVGates n counterWidth).reverse

/-- Exact physical length of the `v := v - u` source-register path. -/
lemma coeffWorkSubUFromVGates_length (n counterWidth : Nat) :
    (coeffWorkSubUFromVGates n counterWidth).length =
      6 * (n - 1) + 2 * n := by
  simpa only [coeffWorkSubUFromVGates, coeffWorkAddUIntoVGates,
    List.length_reverse] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length
      (coeffWorkAddUIntoVLayout n counterWidth))

/-- The `v := v - u` source-register path has no X leaf. -/
lemma coeffWorkSubUFromVGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((coeffWorkSubUFromVGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp only [coeffWorkSubUFromVGates, coeffWorkAddUIntoVGates,
    List.map_reverse, List.sum_reverse,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum]

/-- Exact CNOT coordinate of the `v := v - u` source-register path. -/
lemma coeffWorkSubUFromVGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkSubUFromVGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * n := by
  simp only [coeffWorkSubUFromVGates, coeffWorkAddUIntoVGates,
    List.map_reverse, List.sum_reverse,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate of the `v := v - u` source-register path. -/
lemma coeffWorkSubUFromVGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkSubUFromVGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * (n - 1) := by
  simp only [coeffWorkSubUFromVGates, coeffWorkAddUIntoVGates,
    List.map_reverse, List.sum_reverse,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum]

/-- Step function realized by `coeffWorkSubUFromVGates`. -/
def coeffWorkSubUFromVStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList (coeffWorkSubUFromVGates n counterWidth)

/-- Circuit for the concrete source-register subtract path `v := v - u`. -/
def coeffWorkSubUFromVProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkSubUFromVGates n counterWidth)

/-- The concrete source-register subtract circuit realizes `v := v - u`. -/
lemma coeffWorkSubUFromV_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkSubUFromVProgram n counterWidth) environment
      (coeffWorkSubUFromVStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkSubUFromVGates n counterWidth)

/-- The concrete `v := v - u` source-subtract gate list is disjoint from the
staged compare bit. -/
lemma coeffWorkSubUFromVGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coeffWorkSubUFromVGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (coeffAdderCompareBit n counterWidth) gate := by
  intro gate hmem
  have hforward :
      gate ∈ coeffWorkAddUIntoVGates n counterWidth := by
    simpa [coeffWorkSubUFromVGates] using hmem
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coeffWorkAddUIntoVLayout n counterWidth)
      (coeffAdderCompareBit n counterWidth)
      (fun i =>
        by
          simpa [coeffWorkAddUIntoVLayout, coeffAdderUWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedUWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedUWordBit_wire_ne n counterWidth i)))
      (fun i =>
        by
          simpa [coeffWorkAddUIntoVLayout, coeffAdderVWord,
            coeffAdderCompareBit] using
            liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth ((liftedVWord n counterWidth).bit i)
              (liftedCompareBit n counterWidth)
              (Ne.symm
                (liftedCompare_liftedVWordBit_wire_ne n counterWidth i)))
      (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne n counterWidth)
      (fun j =>
        by
          simpa [coeffWorkAddUIntoVLayout,
            coeffAdderComparisonCarryPrefixWord] using
            Ne.symm
              (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
                n counterWidth (coeffAdderComparisonCarryPrefixIndex n j)))
      gate hforward

/-- The concrete `v := v - u` source-subtract gate list is disjoint from the
dedicated coefficient-adder carry-in bit, which can therefore serve as the
extra clean control-work bit for this source-subtract-only wrapper. -/
lemma coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coeffWorkSubUFromVGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (liftedCoeffAdderCarryInBit n counterWidth) gate := by
  intro gate hmem
  have hforward :
      gate ∈ coeffWorkAddUIntoVGates n counterWidth := by
    simpa [coeffWorkSubUFromVGates] using hmem
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (coeffWorkAddUIntoVLayout n counterWidth)
      (liftedCoeffAdderCarryInBit n counterWidth)
      (fun i =>
        by
          simpa [coeffWorkAddUIntoVLayout, coeffAdderUWord,
            liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth ((liftedUWord n counterWidth).bit i)
              (coeffAdderCarryInWorkBit n))
      (fun i =>
        by
          simpa [coeffWorkAddUIntoVLayout, coeffAdderVWord,
            liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth ((liftedVWord n counterWidth).bit i)
              (coeffAdderCarryInWorkBit n))
      (by
        simpa [coeffWorkAddUIntoVLayout, coeffAdderScratchABit,
          liftedCoeffAdderCarryInBit] using
          liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
            n counterWidth (liftedScratchABit n counterWidth)
            (coeffAdderCarryInWorkBit n))
      (fun j =>
        by
          simpa [coeffWorkAddUIntoVLayout,
            coeffAdderComparisonCarryPrefixWord,
            coeffAdderComparisonCarryBit,
            liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth
              (liftedComparisonCarryBit n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))
              (coeffAdderCarryInWorkBit n))
      gate hforward

/-- Compare-false-controlled source-subtract gate list for the `v := v - u`
data path.  It flips the compare bit around the clean-work controlled source
subtract list, so the source subtract executes exactly when compare is false. -/
def coeffWorkCompareFalseControlledSubUFromVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  [EncodedBit.GateSpec.x (coeffAdderCompareBit n counterWidth)] ++
  EncodedBit.GateSpec.controlledListWithWorkGates
    (coeffAdderCompareBit n counterWidth)
    (liftedCoeffAdderCarryInBit n counterWidth)
    (coeffWorkSubUFromVGates n counterWidth)
    (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth)
    (coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn n counterWidth)
    (by
      simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
          n counterWidth (liftedCompareBit n counterWidth)
          (coeffAdderCarryInWorkBit n)) ++
  [EncodedBit.GateSpec.x (coeffAdderCompareBit n counterWidth)]

/-- Step function for compare-false-controlled `v := v - u` source subtract. -/
def coeffWorkCompareFalseControlledSubUFromVStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (coeffWorkCompareFalseControlledSubUFromVGates n counterWidth)

/-- Circuit for compare-false-controlled `v := v - u` source subtract. -/
def coeffWorkCompareFalseControlledSubUFromVProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareFalseControlledSubUFromVGates n counterWidth)

/-- The compare-false-controlled `v := v - u` circuit realizes its step. -/
lemma coeffWorkCompareFalseControlledSubUFromV_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareFalseControlledSubUFromVProgram n counterWidth) environment
      (coeffWorkCompareFalseControlledSubUFromVStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coeffWorkCompareFalseControlledSubUFromVGates n counterWidth)

/-- If compare is false and the dedicated coefficient carry-in is clean, the
compare-false wrapper acts like the concrete `v := v - u` source-subtract path. -/
lemma coeffWorkCompareFalseControlledSubUFromVStep_eq_subUFromV_of_compare_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hwork : (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    coeffWorkCompareFalseControlledSubUFromVStep n counterWidth x =
      coeffWorkSubUFromVStep n counterWidth x := by
  let compare := coeffAdderCompareBit n counterWidth
  let work := liftedCoeffAdderCarryInBit n counterWidth
  let gates := coeffWorkSubUFromVGates n counterWidth
  have hcompareFlip : compare.get (compare.flip x) = true := by
    dsimp [compare]
    rw [EncodedBit.get_flip_self, hcompare]
    rfl
  have hworkFlip : work.get (compare.flip x) = false := by
    dsimp [work, compare]
    rw [EncodedBit.get_flip_of_wire_ne
      (coeffAdderCompareBit n counterWidth)
      (liftedCoeffAdderCarryInBit n counterWidth)]
    · exact hwork
    · simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
          n counterWidth (liftedCompareBit n counterWidth)
          (coeffAdderCarryInWorkBit n)
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
            (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth)
            (coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn n counterWidth)
            (by
              dsimp [compare, work]
              simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
                liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                  n counterWidth (liftedCompareBit n counterWidth)
                  (coeffAdderCarryInWorkBit n)))
          (compare.flip x) =
        EncodedBit.GateSpec.stepList gates (compare.flip x) := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
        compare work gates
        (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth)
        (coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn n counterWidth)
        (by
          dsimp [compare, work]
          simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (coeffAdderCarryInWorkBit n))
        (compare.flip x) hcompareFlip hworkFlip
  have hcomm :
      EncodedBit.GateSpec.stepList gates (compare.flip x) =
        compare.flip (EncodedBit.GateSpec.stepList gates x) := by
    exact EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
      gates compare
      (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth) x
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
          (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth)
          (coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn n counterWidth)
          (by
            dsimp [compare, work]
            simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
              liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                n counterWidth (liftedCompareBit n counterWidth)
                (coeffAdderCarryInWorkBit n)) ++
        [EncodedBit.GateSpec.x compare])
      (compare.flip x) =
    coeffWorkSubUFromVStep n counterWidth x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle]
  rw [hcomm]
  simp [coeffWorkSubUFromVStep, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, gates, EncodedBit.flip_flip]

/-- If compare is true, the compare-false-controlled `v := v - u` source
subtract is a no-op. -/
lemma coeffWorkCompareFalseControlledSubUFromVStep_eq_self_of_compare_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true) :
    coeffWorkCompareFalseControlledSubUFromVStep n counterWidth x = x := by
  let compare := coeffAdderCompareBit n counterWidth
  let work := liftedCoeffAdderCarryInBit n counterWidth
  let gates := coeffWorkSubUFromVGates n counterWidth
  have hcompareFlip : compare.get (compare.flip x) = false := by
    dsimp [compare]
    rw [EncodedBit.get_flip_self, hcompare]
    rfl
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
            (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth)
            (coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn n counterWidth)
            (by
              dsimp [compare, work]
              simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
                liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                  n counterWidth (liftedCompareBit n counterWidth)
                  (coeffAdderCarryInWorkBit n)))
          (compare.flip x) =
        compare.flip x := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        compare work gates
        (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth)
        (coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn n counterWidth)
        (by
          dsimp [compare, work]
          simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
            liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (coeffAdderCarryInWorkBit n))
        (compare.flip x) hcompareFlip
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates compare work gates
          (coeffWorkSubUFromVGates_bitDisjoint_compare n counterWidth)
          (coeffWorkSubUFromVGates_bitDisjoint_coeffCarryIn n counterWidth)
          (by
            dsimp [compare, work]
            simpa [coeffAdderCompareBit, liftedCoeffAdderCarryInBit] using
              liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
                n counterWidth (liftedCompareBit n counterWidth)
                (coeffAdderCarryInWorkBit n)) ++
        [EncodedBit.GateSpec.x compare])
      (compare.flip x) = x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle]
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.flip_flip]

/-- Compare-selected source-subtract atom for the odd-odd data path.  It
executes `u := u - v` when compare is true and `v := v - u` when compare is
false.  This is source-subtract-only; the coefficient update still needs a
separate controlled path with its own clean-work allocation. -/
def coeffWorkCompareSelectedSourceSubtractGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  coeffWorkCompareControlledSubVFromUGates n counterWidth ++
    coeffWorkCompareFalseControlledSubUFromVGates n counterWidth

/-- Base-gate program for the compare-selected source-subtract atom. -/
def coeffWorkCompareSelectedSourceSubtractProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectedSourceSubtractGates n counterWidth)

/-- Compare-selected source-subtract atom for the odd-odd data path.  It
executes `u := u - v` when compare is true and `v := v - u` when compare is
false.  This is source-subtract-only; the coefficient update still needs a
separate controlled path with its own clean-work allocation. -/
def coeffWorkCompareSelectedSourceSubtractStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkCompareFalseControlledSubUFromVStep n counterWidth
      (coeffWorkCompareControlledSubVFromUStep n counterWidth x)

/-- The explicit compare-selected source-subtract gate list has the same
folded semantics as the sequential selected source-subtract step. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_eq_gateList
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkCompareSelectedSourceSubtractGates n counterWidth) x =
      coeffWorkCompareSelectedSourceSubtractStep n counterWidth x := by
  rw [coeffWorkCompareSelectedSourceSubtractGates,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- The compare-selected source-subtract gate list realizes the sequential
selected source-subtract step. -/
lemma coeffWorkCompareSelectedSourceSubtract_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareSelectedSourceSubtractProgram n counterWidth) environment
      (coeffWorkCompareSelectedSourceSubtractStep n counterWidth) := by
  exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectedSourceSubtractGates n counterWidth)
    (coeffWorkCompareSelectedSourceSubtractStep_eq_gateList n counterWidth)

/-- If compare is true and the dedicated clean work bit is clean, the
compare-selected source-subtract atom reduces to `u := u - v`. -/
lemma
    coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hwork : (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    coeffWorkCompareSelectedSourceSubtractStep n counterWidth x =
      coeffWorkSubVFromUStep n counterWidth x := by
  have hfirst :
      coeffWorkCompareControlledSubVFromUStep n counterWidth x =
        coeffWorkSubVFromUStep n counterWidth x :=
    coeffWorkCompareControlledSubVFromUStep_eq_subVFromU_of_compare_true
      n counterWidth x hcompare hwork
  have hcompareFirst :
      (coeffAdderCompareBit n counterWidth).get
          (coeffWorkCompareControlledSubVFromUStep n counterWidth x) =
        true := by
    rw [hfirst, coeffWorkSubVFromUStep_get_compare]
    exact hcompare
  rw [coeffWorkCompareSelectedSourceSubtractStep]
  rw [coeffWorkCompareFalseControlledSubUFromVStep_eq_self_of_compare_true
    n counterWidth
    (coeffWorkCompareControlledSubVFromUStep n counterWidth x)
    hcompareFirst]
  exact hfirst

/-- If compare is false and the dedicated clean work bit is clean, the
compare-selected source-subtract atom reduces to `v := v - u`. -/
lemma
    coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hwork : (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    coeffWorkCompareSelectedSourceSubtractStep n counterWidth x =
      coeffWorkSubUFromVStep n counterWidth x := by
  have hfirst :
      coeffWorkCompareControlledSubVFromUStep n counterWidth x = x :=
    coeffWorkCompareControlledSubVFromUStep_eq_self_of_compare_false
      n counterWidth x hcompare
  rw [coeffWorkCompareSelectedSourceSubtractStep]
  rw [hfirst]
  exact
    coeffWorkCompareFalseControlledSubUFromVStep_eq_subUFromV_of_compare_false
      n counterWidth x hcompare hwork

/-- Under compare=true, clean control-work, and clean source-adder inputs, the
compare-selected source-subtract atom writes `u := u - v`. -/
lemma
    coeffWorkCompareSelectedSourceSubtractStep_get_u_sub_of_compare_true_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x).1.1.u =
      x.1.1.u - x.1.1.v := by
  rw [
    coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
      n counterWidth x hcompare hcontrolWork]
  exact coeffWorkSubVFromUStep_get_u_sub_of_clean
    n counterWidth x hcarry hsourceWork

lemma coeffWorkSubUFromVStep_comp_addUIntoV
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    coeffWorkSubUFromVStep n counterWidth
        (coeffWorkAddUIntoVStep n counterWidth x) =
      x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (coeffWorkAddUIntoVGates n counterWidth) x

lemma coeffWorkAddUIntoVStep_comp_subUFromV
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    coeffWorkAddUIntoVStep n counterWidth
        (coeffWorkSubUFromVStep n counterWidth x) =
      x := by
  have h :=
    EncodedBit.GateSpec.stepList_reverse_stepList
      (coeffWorkAddUIntoVGates n counterWidth).reverse x
  simpa [coeffWorkAddUIntoVStep, coeffWorkSubUFromVStep,
    coeffWorkSubUFromVGates] using h

/-- The forward `u`-into-`v` adder preserves the scratchA carry-in bit. -/
lemma coeffWorkAddUIntoVStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (coeffWorkAddUIntoVLayout n counterWidth) x
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout] using h

/-- The forward `u`-into-`v` source adder preserves any observed readout whose
wire is disjoint from every `v` target bit and every comparison-prefix
carry-work bit. -/
lemma coeffWorkAddUIntoVStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hright :
      ∀ i : Fin n,
        ((coeffAdderVWord n counterWidth).bit i).wire ≠ observed.wire)
    (hwork :
      ∀ j : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).wire ≠
          observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkAddUIntoVStep n counterWidth x) =
      observed.get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddUIntoVLayout n counterWidth) observed hright hwork x
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout] using h

/-- The forward `u`-into-`v` source adder preserves the active flag. -/
lemma coeffWorkAddUIntoVStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  exact
    coeffWorkAddUIntoVStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderActiveBit n counterWidth)
      (fun i =>
        Ne.symm (coeffAdderActiveBit_coeffAdderVWordBit_wire_ne
          n counterWidth i))
      (fun j => by
        simpa [coeffAdderComparisonCarryPrefixWord,
          coeffAdderComparisonCarryBit, coeffAdderActiveBit] using
          Ne.symm
            (liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth (liftedActiveBit n counterWidth)
              (liftedComparisonCarryBit n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))
              (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
                (RegisterBits.activeBit n counterWidth)
                (comparisonCarryValueBit n
                  (coeffAdderComparisonCarryPrefixIndex n j)))))
      x

/-- The forward `u`-into-`v` source adder preserves the comparison ancilla. -/
lemma coeffWorkAddUIntoVStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  exact
    coeffWorkAddUIntoVStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderCompareBit n counterWidth)
      (fun i =>
        Ne.symm
          (liftComparisonStateBit_liftComparisonStateBit_wire_ne
            n counterWidth (liftedCompareBit n counterWidth)
            ((liftedVWord n counterWidth).bit i)
            (liftedCompare_liftedVWordBit_wire_ne n counterWidth i)))
      (fun j => by
        simpa [coeffAdderComparisonCarryPrefixWord,
          coeffAdderComparisonCarryBit, coeffAdderCompareBit] using
          Ne.symm
            (liftComparisonStateBit_liftComparisonStateBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (liftedComparisonCarryBit n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))
              (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth
                (coeffAdderComparisonCarryPrefixIndex n j))))
      x

/-- The forward `u`-into-`v` source adder preserves every stored
branch-history bit. -/
lemma coeffWorkAddUIntoVStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  exact
    coeffWorkAddUIntoVStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderHistoryBit n counterWidth historyIndex)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedVWord n counterWidth).bit i)
          (liftedHistoryBit n counterWidth historyIndex)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth i)
            (RegisterBits.historyBit n counterWidth historyIndex)
            (by
              simpa [RegisterBits.vValueBit] using
                RegisterBits.v_history_wire_ne n counterWidth
                  (WireAddress.littleEndianWire i) historyIndex)))
      (fun j =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth
          (liftedComparisonCarryBit n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n j))
          (liftedHistoryBit n counterWidth historyIndex)
          (Ne.symm
            (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
              (RegisterBits.historyBit n counterWidth historyIndex)
              (comparisonCarryValueBit n
                (coeffAdderComparisonCarryPrefixIndex n j)))))
      x

/-- The forward `u`-into-`v` source adder preserves the second scratch bit. -/
lemma coeffWorkAddUIntoVStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  exact
    coeffWorkAddUIntoVStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderScratchBBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftComparisonStateBit_wire_ne
          n counterWidth ((liftedVWord n counterWidth).bit i)
          (liftedScratchBBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth i)
            (RegisterBits.scratchBBit n counterWidth)
            (by
              simpa [RegisterBits.vValueBit] using
                RegisterBits.v_scratchB_wire_ne n counterWidth
                  (WireAddress.littleEndianWire i))))
      (fun j => by
        simpa [coeffAdderComparisonCarryPrefixWord,
          coeffAdderComparisonCarryBit] using
          Ne.symm
            (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
              n counterWidth (coeffAdderComparisonCarryPrefixIndex n j)))
      x

/-- If the input scratchA carry-in is clean, the reverse `v := v - u` path
also lands on clean scratchA. -/
lemma coeffWorkSubUFromVStep_get_scratchA_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      false := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_scratchA n counterWidth
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        (coeffAdderScratchABit n counterWidth).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderScratchABit n counterWidth).get x := by
      rw [hcancel]
    _ = false := hcarry

/-- The concrete `v := v - u` reverse-adder path preserves the active flag. -/
lemma coeffWorkSubUFromVStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_active n counterWidth
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        (coeffAdderActiveBit n counterWidth).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderActiveBit n counterWidth).get x := by
      rw [hcancel]

/-- The concrete `v := v - u` reverse-adder path preserves the comparison
ancilla. -/
lemma coeffWorkSubUFromVStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_compare n counterWidth
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        (coeffAdderCompareBit n counterWidth).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderCompareBit n counterWidth).get x := by
      rw [hcancel]

/-- The concrete `v := v - u` reverse-adder path preserves every stored
branch-history bit. -/
lemma coeffWorkSubUFromVStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_historyBit n counterWidth historyIndex
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        (coeffAdderHistoryBit n counterWidth historyIndex).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
      rw [hcancel]

/-- The concrete `v := v - u` reverse-adder path preserves the second scratch
bit. -/
lemma coeffWorkSubUFromVStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_scratchB n counterWidth
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        (coeffAdderScratchBBit n counterWidth).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = (coeffAdderScratchBBit n counterWidth).get x := by
      rw [hcancel]

/-- The forward `u`-into-`v` adder preserves every source `u` bit. -/
lemma coeffWorkAddUIntoVStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      ((coeffAdderUWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (coeffWorkAddUIntoVLayout n counterWidth) bit x
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout] using h

/-- The forward `u`-into-`v` adder preserves every `s` coefficient value bit. -/
lemma coeffWorkAddUIntoVStep_get_sCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddUIntoVLayout n counterWidth)
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit)
      (fun i => coeffAdderVWordBit_coeffAdderSCoeffValueWordBit_wire_ne
        n counterWidth i bit)
      (fun j => by
        simpa [coeffWorkAddUIntoVLayout, coeffAdderComparisonCarryPrefixWord] using
          Ne.symm
            (coeffAdderSCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
              n counterWidth bit (coeffAdderComparisonCarryPrefixIndex n j)))
      x
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout] using h

/-- The forward `u`-into-`v` adder preserves every `r` coefficient value bit. -/
lemma coeffWorkAddUIntoVStep_get_rCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddUIntoVLayout n counterWidth)
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit)
      (fun i => coeffAdderVWordBit_coeffAdderRCoeffValueWordBit_wire_ne
        n counterWidth i bit)
      (fun j => by
        simpa [coeffWorkAddUIntoVLayout, coeffAdderComparisonCarryPrefixWord] using
          Ne.symm
            (coeffAdderRCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
              n counterWidth bit (coeffAdderComparisonCarryPrefixIndex n j)))
      x
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout] using h

/-- The forward `u`-into-`v` adder preserves the dedicated coefficient-adder
carry-in flag. -/
lemma coeffWorkAddUIntoVStep_get_coeffCarryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddUIntoVLayout n counterWidth)
      (liftedCoeffAdderCarryInBit n counterWidth)
      (fun i =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          ((liftedVWord n counterWidth).bit i) (coeffAdderCarryInWorkBit n))
      (fun j =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          (liftedComparisonCarryBit n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n j))
          (coeffAdderCarryInWorkBit n))
      x
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout, coeffAdderComparisonCarryPrefixWord] using h

/-- The forward `u`-into-`v` adder preserves every dedicated coefficient-adder
carry-work bit. -/
lemma coeffWorkAddUIntoVStep_get_coeffCarryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (coeffWorkAddUIntoVLayout n counterWidth)
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit)
      (fun i =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          ((liftedVWord n counterWidth).bit i)
          (coeffAdderCarryWorkBit n workBit))
      (fun j =>
        liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
          (liftedComparisonCarryBit n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n j))
          (coeffAdderCarryWorkBit n workBit))
      x
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout, coeffAdderComparisonCarryPrefixWord] using h

/-- On clean comparison-prefix work inputs, the forward `u`-into-`v` adder
restores every comparison-prefix carry-work bit. -/
lemma coeffWorkAddUIntoVStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      false := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (coeffWorkAddUIntoVLayout n counterWidth) bit x hwork
  simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
    coeffWorkAddUIntoVLayout] using h

/-- On clean comparison-prefix work inputs, the concrete reverse `v := v - u`
path also lands on clean comparison-prefix carry-work bits. -/
lemma coeffWorkSubUFromVStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      false := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_reverse_get_workCarry_clean
      (coeffWorkAddUIntoVLayout n counterWidth) bit x hwork
  simpa [coeffWorkSubUFromVStep, coeffWorkSubUFromVGates,
    coeffWorkAddUIntoVGates, coeffWorkAddUIntoVLayout] using h

/-- The forward `v`-into-`u` source adder preserves the final comparison
carry, which lies outside its comparison-prefix carry workspace. -/
lemma coeffWorkAddVIntoUStep_get_finalComparisonCarry
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hfinal : finalBit.val + 1 = n) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkAddVIntoUStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
  exact
    coeffWorkAddVIntoUStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderComparisonCarryBit n counterWidth finalBit)
      (fun sourceBit =>
        coeffAdderUWordBit_coeffAdderComparisonCarryBit_wire_ne
          n counterWidth sourceBit finalBit)
      (fun prefixBit => by
        simpa [coeffAdderComparisonCarryPrefixWord] using
          coeffAdderComparisonCarryBit_coeffAdderComparisonCarryBit_wire_ne
            n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n prefixBit) finalBit
            (coeffAdderComparisonCarryPrefixIndex_ne_final
              n finalBit hfinal prefixBit))
      x

/-- The reverse `u := u - v` source adder likewise preserves the final
comparison carry. -/
lemma coeffWorkSubVFromUStep_get_finalComparisonCarry
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hfinal : finalBit.val + 1 = n) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkSubVFromUStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
  have hforward :=
    coeffWorkAddVIntoUStep_get_finalComparisonCarry n counterWidth finalBit
      (coeffWorkSubVFromUStep n counterWidth x) hfinal
  have hcancel := coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth x
  calc
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkSubVFromUStep n counterWidth x) =
        (coeffAdderComparisonCarryBit n counterWidth finalBit).get
          (coeffWorkAddVIntoUStep n counterWidth
            (coeffWorkSubVFromUStep n counterWidth x)) := hforward.symm
    _ = (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
      rw [hcancel]

/-- The forward `u`-into-`v` source adder preserves the final comparison
carry, which lies outside its comparison-prefix carry workspace. -/
lemma coeffWorkAddUIntoVStep_get_finalComparisonCarry
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hfinal : finalBit.val + 1 = n) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkAddUIntoVStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
  exact
    coeffWorkAddUIntoVStep_get_observed_of_right_work_ne n counterWidth
      (coeffAdderComparisonCarryBit n counterWidth finalBit)
      (fun sourceBit =>
        coeffAdderVWordBit_coeffAdderComparisonCarryBit_wire_ne
          n counterWidth sourceBit finalBit)
      (fun prefixBit => by
        simpa [coeffAdderComparisonCarryPrefixWord] using
          coeffAdderComparisonCarryBit_coeffAdderComparisonCarryBit_wire_ne
            n counterWidth
            (coeffAdderComparisonCarryPrefixIndex n prefixBit) finalBit
            (coeffAdderComparisonCarryPrefixIndex_ne_final
              n finalBit hfinal prefixBit))
      x

/-- The reverse `v := v - u` source adder likewise preserves the final
comparison carry. -/
lemma coeffWorkSubUFromVStep_get_finalComparisonCarry
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hfinal : finalBit.val + 1 = n) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
  have hforward :=
    coeffWorkAddUIntoVStep_get_finalComparisonCarry n counterWidth finalBit
      (coeffWorkSubUFromVStep n counterWidth x) hfinal
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        (coeffAdderComparisonCarryBit n counterWidth finalBit).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := hforward.symm
    _ = (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
      rw [hcancel]

/-- On clean carry/work inputs, the forward `u`-into-`v` carry stage computes
the propagated natural addition carry. -/
lemma coeffWorkAddUIntoV_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat) (j : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coeffWorkAddUIntoVLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.u.val x.1.1.v.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (coeffWorkAddUIntoVLayout n counterWidth) x
  change
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get stage =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.u.val x.1.1.v.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin (n - 1), j.val = m ->
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.u.val x.1.1.v.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (coeffWorkAddUIntoVLayout n counterWidth) j x hwork
        change
          ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get
              stage =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.u.val x.1.1.v.val (j.val + 1)
        change
          ((coeffWorkAddUIntoVLayout n counterWidth).workCarry.bit j).get
              ((coeffWorkAddUIntoVLayout n counterWidth).carryStageIndexStep
                x) =
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.u.val x.1.1.v.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (coeffWorkAddUIntoVLayout n counterWidth) x
          rw [hdata]
          simp [coeffWorkAddUIntoVLayout, coeffAdderUWord_get_testBit,
            coeffAdderVWord_get_testBit, hcarry,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpRec' :
              ((coeffWorkAddUIntoVLayout n counterWidth).workCarry.bit p).get
                  ((coeffWorkAddUIntoVLayout n counterWidth).carryStageIndexStep
                    x) =
                Nat.BinaryArithmetic.natAddCarry
                  x.1.1.u.val x.1.1.v.val (p.val + 1) := by
            simpa [stage, coeffWorkAddUIntoVLayout] using hpRec
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hpRec', hpSucc]
          simp [coeffWorkAddUIntoVLayout, coeffAdderUWord_get_testBit,
            coeffAdderVWord_get_testBit,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before the `u`-into-`v` target sum is the propagated
natural addition carry on clean carry/work inputs. -/
lemma coeffWorkAddUIntoV_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (coeffWorkAddUIntoVLayout n counterWidth) bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (coeffWorkAddUIntoVLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.1.1.u.val x.1.1.v.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (coeffWorkAddUIntoVLayout n counterWidth) x
    rw [hdata]
    simp [coeffWorkAddUIntoVLayout, hcarry,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : bit.val - 1 < n - 1 := by
      have hbit := bit.isLt
      omega
    let j : Fin (n - 1) := ⟨bit.val - 1, hjLt⟩
    have hworkCarry :=
      coeffWorkAddUIntoV_carryStage_get_workCarry_natAddCarry
        n counterWidth j x hcarry hwork
    have hjSucc : j.val + 1 = bit.val := by
      dsimp [j]
      omega
    change
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coeffWorkAddUIntoVLayout n counterWidth) x) =
        Nat.BinaryArithmetic.natAddCarry
          x.1.1.u.val x.1.1.v.val bit.val
    rw [hworkCarry, hjSucc]

/-- On clean carry/work inputs, the forward `u`-into-`v` adder writes the
target `v` word as `v + u`. -/
lemma coeffWorkAddUIntoVStep_get_v_add_testBit_of_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkAddUIntoVStep n counterWidth x).1.1.v.val.testBit bit.val =
      (x.1.1.v + x.1.1.u).val.testBit bit.val := by
  have hright :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (coeffWorkAddUIntoVLayout n counterWidth) bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hright
  have hcarryBit :=
    coeffWorkAddUIntoV_carryBeforeSum_get_natAddCarry
      n counterWidth bit x hcarry hwork
  rw [hcarryBit] at hright
  have hadd :=
    (word_add_testBit_eq_xor3 n x.1.1.u x.1.1.v bit).symm
  calc
    (coeffWorkAddUIntoVStep n counterWidth x).1.1.v.val.testBit bit.val =
        (((x.1.1.v.val.testBit bit.val ^^
              x.1.1.u.val.testBit bit.val) ^^
            Nat.BinaryArithmetic.natAddCarry
              x.1.1.u.val x.1.1.v.val bit.val)) := by
      simpa [coeffWorkAddUIntoVStep, coeffWorkAddUIntoVGates,
        coeffWorkAddUIntoVLayout, coeffAdderUWord_get_testBit,
        coeffAdderVWord_get_testBit, Bool.xor_assoc] using hright
    _ = (x.1.1.v + x.1.1.u).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using hadd

/-- Word-level clean-input endpoint for the forward `u`-into-`v` data path. -/
lemma coeffWorkAddUIntoVStep_get_v_add_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkAddUIntoVStep n counterWidth x).1.1.v =
      x.1.1.v + x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  exact coeffWorkAddUIntoVStep_get_v_add_testBit_of_clean
    n counterWidth bit x hcarry hwork

/-- The concrete `v := v - u` reverse-adder path preserves every source `u`
bit. -/
lemma coeffWorkSubUFromVStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      ((coeffAdderUWord n counterWidth).bit bit).get x := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_uWordBit n counterWidth bit
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        ((coeffAdderUWord n counterWidth).bit bit).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = ((coeffAdderUWord n counterWidth).bit bit).get x := by
      rw [hcancel]

/-- The concrete `v := v - u` reverse-adder path preserves the source `u`
word. -/
lemma coeffWorkSubUFromVStep_get_u
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubUFromVStep n counterWidth x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkSubUFromVStep_get_uWordBit n counterWidth bit x
  simpa [coeffAdderUWord_get_testBit] using h

/-- The concrete `v := v - u` reverse-adder path preserves the `s`
coefficient word. -/
lemma coeffWorkSubUFromVStep_get_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubUFromVStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have hadd :=
    coeffWorkAddUIntoVStep_get_sCoeffValueBit n counterWidth bit
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffWorkSubUFromVStep n counterWidth x).1.1.sCoeff.val.testBit
        bit.val =
        (coeffWorkAddUIntoVStep n counterWidth
          (coeffWorkSubUFromVStep n counterWidth x)).1.1.sCoeff.val.testBit
            bit.val := by
      simpa [coeffAdderSCoeffValueWord_get_testBit] using hadd.symm
    _ = x.1.1.sCoeff.val.testBit bit.val := by
      rw [hcancel]

/-- The concrete `v := v - u` reverse-adder path preserves the `r`
coefficient word. -/
lemma coeffWorkSubUFromVStep_get_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubUFromVStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have hadd :=
    coeffWorkAddUIntoVStep_get_rCoeffValueBit n counterWidth bit
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (coeffWorkSubUFromVStep n counterWidth x).1.1.rCoeff.val.testBit
        bit.val =
        (coeffWorkAddUIntoVStep n counterWidth
          (coeffWorkSubUFromVStep n counterWidth x)).1.1.rCoeff.val.testBit
            bit.val := by
      simpa [coeffAdderRCoeffValueWord_get_testBit] using hadd.symm
    _ = x.1.1.rCoeff.val.testBit bit.val := by
      rw [hcancel]

/-- The concrete `v := v - u` reverse-adder path preserves the dedicated
coefficient-adder carry-in flag. -/
lemma coeffWorkSubUFromVStep_get_coeffCarryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_coeffCarryIn n counterWidth
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        (liftedCoeffAdderCarryInBit n counterWidth).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = (liftedCoeffAdderCarryInBit n counterWidth).get x := by
      rw [hcancel]

/-- The concrete `v := v - u` reverse-adder path preserves every dedicated
coefficient-adder carry-work bit. -/
lemma coeffWorkSubUFromVStep_get_coeffCarryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkSubUFromVStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  have hadd :=
    coeffWorkAddUIntoVStep_get_coeffCarryWorkBit n counterWidth workBit
      (coeffWorkSubUFromVStep n counterWidth x)
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  calc
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkSubUFromVStep n counterWidth x) =
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
          (coeffWorkAddUIntoVStep n counterWidth
            (coeffWorkSubUFromVStep n counterWidth x)) := by
      exact hadd.symm
    _ = ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
      rw [hcancel]

/-- If the reverse `v := v - u` path lands on clean carry/work, its target
word is the width-preserving subtraction endpoint. -/
lemma coeffWorkSubUFromVStep_get_v_sub_of_output_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry :
      (coeffAdderScratchABit n counterWidth).get
          (coeffWorkSubUFromVStep n counterWidth x) = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
            (coeffWorkSubUFromVStep n counterWidth x) = false) :
    (coeffWorkSubUFromVStep n counterWidth x).1.1.v =
      x.1.1.v - x.1.1.u := by
  let z := coeffWorkSubUFromVStep n counterWidth x
  have hadd :=
    coeffWorkAddUIntoVStep_get_v_add_of_clean
      n counterWidth z hcarry hwork
  have hcancel := coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth x
  have hsource := coeffWorkSubUFromVStep_get_u n counterWidth x
  have hv :
      x.1.1.v = z.1.1.v + z.1.1.u := by
    calc
      x.1.1.v =
          (coeffWorkAddUIntoVStep n counterWidth z).1.1.v := by
        rw [hcancel]
      _ = z.1.1.v + z.1.1.u := hadd
  change z.1.1.v = x.1.1.v - x.1.1.u
  rw [← hsource]
  rw [eq_sub_iff_add_eq]
  exact hv.symm

/-- Clean-input target arithmetic endpoint for the concrete `v := v - u`
reverse-adder path. -/
lemma coeffWorkSubUFromVStep_get_v_sub_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkSubUFromVStep n counterWidth x).1.1.v =
      x.1.1.v - x.1.1.u := by
  exact coeffWorkSubUFromVStep_get_v_sub_of_output_clean
    n counterWidth x
    (coeffWorkSubUFromVStep_get_scratchA_clean n counterWidth x hcarry)
    (fun k =>
      coeffWorkSubUFromVStep_get_comparisonCarryPrefix_clean
        n counterWidth k x hwork)

/-- Under compare=false, clean control-work, and clean source-adder inputs, the
compare-selected source-subtract atom writes `v := v - u`. -/
lemma
    coeffWorkCompareSelectedSourceSubtractStep_get_v_sub_of_compare_false_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x).1.1.v =
      x.1.1.v - x.1.1.u := by
  rw [
    coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
      n counterWidth x hcompare hcontrolWork]
  exact coeffWorkSubUFromVStep_get_v_sub_of_clean
    n counterWidth x hcarry hsourceWork

/-- On clean control-work and clean source-adder carry input, the
compare-selected source-subtract atom restores scratchA. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_scratchA_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      false := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_scratchA_clean
      n counterWidth x hcarry
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_scratchA_clean
      n counterWidth x hcarry

/-- On clean control-work and clean comparison-prefix inputs, the
compare-selected source-subtract atom restores each comparison-prefix carry
bit. -/
lemma
    coeffWorkCompareSelectedSourceSubtractStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      false := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_comparisonCarryPrefix_clean
      n counterWidth bit x hsourceWork
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_comparisonCarryPrefix_clean
      n counterWidth bit x hsourceWork

/-- On clean control-work, the compare-selected source-subtract atom preserves
the active flag. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_active
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_active n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_active n counterWidth x

/-- On clean control-work, the compare-selected source-subtract atom preserves
the compare readout. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_compare
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_compare n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_compare n counterWidth x

/-- On clean control-work, the compare-selected source-subtract atom preserves
every stored branch-history bit. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_historyBit
      n counterWidth historyIndex x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_historyBit
      n counterWidth historyIndex x

/-- On clean control-work, the compare-selected source-subtract atom preserves
the second scratch bit. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_scratchB
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_scratchB n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_scratchB n counterWidth x

/-- On clean control-work, the compare-selected source-subtract atom preserves
the dedicated coefficient-adder carry-in bit. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_coeffCarryIn
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_coeffCarryIn n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_coeffCarryIn n counterWidth x

/-- On clean control-work, the compare-selected source-subtract atom restores
the dedicated coefficient-adder carry-in bit. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_coeffCarryIn_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      false := by
  rw [coeffWorkCompareSelectedSourceSubtractStep_get_coeffCarryIn
    n counterWidth x hcontrolWork]
  exact hcontrolWork

/-- On clean control-work, the compare-selected source-subtract atom preserves
each dedicated coefficient-adder carry-work bit. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_coeffCarryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
        n counterWidth x hcompare hcontrolWork]
    exact coeffWorkSubVFromUStep_get_coeffCarryWorkBit
      n counterWidth workBit x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork]
    exact coeffWorkSubUFromVStep_get_coeffCarryWorkBit
      n counterWidth workBit x

/-- On clean control-work and clean coefficient-adder work inputs, the
compare-selected source-subtract atom restores each dedicated coefficient-adder
carry-work bit. -/
lemma coeffWorkCompareSelectedSourceSubtractStep_get_coeffCarryWorkBit_clean
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
      false := by
  rw [coeffWorkCompareSelectedSourceSubtractStep_get_coeffCarryWorkBit
    n counterWidth workBit x hcontrolWork]
  exact hwork workBit

/-- Circuit for `u := u - v` followed by `r := r + s`. -/
def coeffWorkSubVFromUThenAddSIntoRProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkSubVFromUProgram n counterWidth)
    (coefficientAddSIntoRProgram n counterWidth)

/-- Concrete odd-branch atom for `u := u - v` followed by `r := r + s`. -/
def coeffWorkSubVFromUThenAddSIntoRStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coefficientAddSIntoRStep n counterWidth
      (coeffWorkSubVFromUStep n counterWidth x)

/-- The sequential circuit realizes source subtraction `u := u - v` followed
by the coefficient update `r := r + s`. -/
lemma coeffWorkSubVFromUThenAddSIntoR_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkSubVFromUThenAddSIntoRProgram n counterWidth) environment
      (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth) := by
  unfold coeffWorkSubVFromUThenAddSIntoRProgram
    coeffWorkSubVFromUThenAddSIntoRStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkSubVFromUStep n counterWidth)
    (secondStep := coefficientAddSIntoRStep n counterWidth)
    (coeffWorkSubVFromU_realizes n counterWidth)
    (coefficientAddSIntoR_realizes n counterWidth)

/-- Circuit for `v := v - u` followed by `s := s + r`. -/
def coeffWorkSubUFromVThenAddRIntoSProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkSubUFromVProgram n counterWidth)
    (coefficientAddRIntoSProgram n counterWidth)

/-- Concrete odd-branch atom for `v := v - u` followed by `s := s + r`. -/
def coeffWorkSubUFromVThenAddRIntoSStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coefficientAddRIntoSStep n counterWidth
      (coeffWorkSubUFromVStep n counterWidth x)

/-- The sequential circuit realizes source subtraction `v := v - u` followed
by the coefficient update `s := s + r`. -/
lemma coeffWorkSubUFromVThenAddRIntoS_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkSubUFromVThenAddRIntoSProgram n counterWidth) environment
      (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth) := by
  unfold coeffWorkSubUFromVThenAddRIntoSProgram
    coeffWorkSubUFromVThenAddRIntoSStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkSubUFromVStep n counterWidth)
    (secondStep := coefficientAddRIntoSStep n counterWidth)
    (coeffWorkSubUFromV_realizes n counterWidth)
    (coefficientAddRIntoS_realizes n counterWidth)

/-- Compare-selected odd data path for the two odd Kaliski branches.  It first
selects the source subtract by compare, then selects the matching coefficient
add with `scratchA` as the restored clean control-work bit. -/
def coeffWorkCompareSelectedOddDataPathGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  coeffWorkCompareSelectedSourceSubtractGates n counterWidth ++
    coeffWorkCompareSelectedCoefficientAddGates n counterWidth

/-- Base-gate program for the compare-selected odd data path. -/
def coeffWorkCompareSelectedOddDataPathProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectedOddDataPathGates n counterWidth)

/-- Compare-selected odd data path for the two odd Kaliski branches.  It first
selects the source subtract by compare, then selects the matching coefficient
add with `scratchA` as the restored clean control-work bit. -/
def coeffWorkCompareSelectedOddDataPathStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkCompareSelectedCoefficientAddStep n counterWidth
      (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x)

/-- The explicit compare-selected odd data-path gate list has the same folded
semantics as the sequential selected odd data-path step. -/
lemma coeffWorkCompareSelectedOddDataPathStep_eq_gateList
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkCompareSelectedOddDataPathGates n counterWidth) x =
      coeffWorkCompareSelectedOddDataPathStep n counterWidth x := by
  rw [coeffWorkCompareSelectedOddDataPathGates,
    EncodedBit.GateSpec.stepList_append]
  rw [coeffWorkCompareSelectedSourceSubtractStep_eq_gateList]
  rw [coeffWorkCompareSelectedCoefficientAddStep_eq_gateList]
  rfl

/-- The compare-selected odd data-path gate list realizes the sequential
selected odd data-path step. -/
lemma coeffWorkCompareSelectedOddDataPath_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareSelectedOddDataPathProgram n counterWidth) environment
      (coeffWorkCompareSelectedOddDataPathStep n counterWidth) := by
  exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectedOddDataPathGates n counterWidth)
    (coeffWorkCompareSelectedOddDataPathStep_eq_gateList n counterWidth)

/-- Exact physical length of the compare-selected odd data path. -/
lemma coeffWorkCompareSelectedOddDataPathGates_length
    (n counterWidth : Nat) :
    (coeffWorkCompareSelectedOddDataPathGates n counterWidth).length =
      36 * (n - 1) + 44 * n + 8 := by
  simp only [coeffWorkCompareSelectedOddDataPathGates,
    coeffWorkCompareSelectedSourceSubtractGates,
    coeffWorkCompareControlledSubVFromUGates,
    coeffWorkCompareFalseControlledSubUFromVGates,
    coeffWorkCompareSelectedCoefficientAddGates,
    coeffWorkCompareControlledAddSIntoRGates,
    coeffWorkCompareFalseControlledAddRIntoSGates,
    List.length_append, List.length_cons, List.length_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_length_eq,
    coeffWorkSubVFromUGates_length,
    coeffWorkSubVFromUGates_toffoliMultiplicity_sum,
    coeffWorkSubUFromVGates_length,
    coeffWorkSubUFromVGates_toffoliMultiplicity_sum,
    coefficientAddSIntoRGates_length,
    coefficientAddSIntoRGates_toffoliMultiplicity_sum,
    coefficientAddRIntoSGates_length,
    coefficientAddRIntoSGates_toffoliMultiplicity_sum]
  omega

/-- Exact X coordinate of the compare-selected odd data path. -/
lemma coeffWorkCompareSelectedOddDataPathGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkCompareSelectedOddDataPathGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  simp only [coeffWorkCompareSelectedOddDataPathGates,
    coeffWorkCompareSelectedSourceSubtractGates,
    coeffWorkCompareControlledSubVFromUGates,
    coeffWorkCompareFalseControlledSubUFromVGates,
    coeffWorkCompareSelectedCoefficientAddGates,
    coeffWorkCompareControlledAddSIntoRGates,
    coeffWorkCompareFalseControlledAddRIntoSGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum]
  rfl

/-- The compare-selected odd data path contains no CNOT leaf. -/
lemma coeffWorkCompareSelectedOddDataPathGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkCompareSelectedOddDataPathGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [coeffWorkCompareSelectedOddDataPathGates,
    coeffWorkCompareSelectedSourceSubtractGates,
    coeffWorkCompareControlledSubVFromUGates,
    coeffWorkCompareFalseControlledSubUFromVGates,
    coeffWorkCompareSelectedCoefficientAddGates,
    coeffWorkCompareControlledAddSIntoRGates,
    coeffWorkCompareFalseControlledAddRIntoSGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    coeffWorkSubVFromUGates_xMultiplicity_sum,
    coeffWorkSubUFromVGates_xMultiplicity_sum,
    coefficientAddSIntoRGates_xMultiplicity_sum,
    coefficientAddRIntoSGates_xMultiplicity_sum]
  rfl

/-- Exact Toffoli coordinate of the compare-selected odd data path. -/
lemma coeffWorkCompareSelectedOddDataPathGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkCompareSelectedOddDataPathGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      44 * n + 36 * (n - 1) + 4 := by
  simp only [coeffWorkCompareSelectedOddDataPathGates,
    coeffWorkCompareSelectedSourceSubtractGates,
    coeffWorkCompareControlledSubVFromUGates,
    coeffWorkCompareFalseControlledSubUFromVGates,
    coeffWorkCompareSelectedCoefficientAddGates,
    coeffWorkCompareControlledAddSIntoRGates,
    coeffWorkCompareFalseControlledAddRIntoSGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    coeffWorkSubVFromUGates_cnotMultiplicity_sum,
    coeffWorkSubVFromUGates_toffoliMultiplicity_sum,
    coeffWorkSubUFromVGates_cnotMultiplicity_sum,
    coeffWorkSubUFromVGates_toffoliMultiplicity_sum,
    coefficientAddSIntoRGates_cnotMultiplicity_sum,
    coefficientAddSIntoRGates_toffoliMultiplicity_sum,
    coefficientAddRIntoSGates_cnotMultiplicity_sum,
    coefficientAddRIntoSGates_toffoliMultiplicity_sum,
    EncodedBit.GateSpec.toffoliMultiplicity_x]
  omega

/-- If compare is true and the selected source-subtract control/work inputs are
clean, the compare-selected odd data path reduces to `u := u - v; r := r + s`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareSelectedOddDataPathStep n counterWidth x =
      coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x := by
  have hcompareAfterSource :
      (coeffAdderCompareBit n counterWidth).get
          (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
        true := by
    rw [coeffWorkCompareSelectedSourceSubtractStep_get_compare
      n counterWidth x hcontrolWork]
    exact hcompare
  have hscratchAfterSource :
      (coeffAdderScratchABit n counterWidth).get
          (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
        false :=
    coeffWorkCompareSelectedSourceSubtractStep_get_scratchA_clean
      n counterWidth x hcontrolWork hsourceCarry
  have hcoeff :=
    coeffWorkCompareSelectedCoefficientAddStep_eq_addSIntoR_of_compare_true
      n counterWidth
      (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x)
      hcompareAfterSource hscratchAfterSource
  rw [coeffWorkCompareSelectedOddDataPathStep]
  rw [hcoeff]
  rw [
    coeffWorkCompareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
      n counterWidth x hcompare hcontrolWork]
  rfl

/-- If compare is false and the selected source-subtract control/work inputs are
clean, the compare-selected odd data path reduces to `v := v - u; s := s + r`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareSelectedOddDataPathStep n counterWidth x =
      coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x := by
  have hcompareAfterSource :
      (coeffAdderCompareBit n counterWidth).get
          (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
        false := by
    rw [coeffWorkCompareSelectedSourceSubtractStep_get_compare
      n counterWidth x hcontrolWork]
    exact hcompare
  have hscratchAfterSource :
      (coeffAdderScratchABit n counterWidth).get
          (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x) =
        false :=
    coeffWorkCompareSelectedSourceSubtractStep_get_scratchA_clean
      n counterWidth x hcontrolWork hsourceCarry
  have hcoeff :=
    coeffWorkCompareSelectedCoefficientAddStep_eq_addRIntoS_of_compare_false
      n counterWidth
      (coeffWorkCompareSelectedSourceSubtractStep n counterWidth x)
      hcompareAfterSource hscratchAfterSource
  rw [coeffWorkCompareSelectedOddDataPathStep]
  rw [hcoeff]
  rw [
    coeffWorkCompareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
      n counterWidth x hcompare hcontrolWork]
  rfl

private lemma
    coeffWorkCompareSelectedOddDataPathStep_get_counterValueBit_clean
    (n counterWidth : Nat) (counterBit : Fin counterWidth)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry :
      (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderCounterValueBit n counterWidth counterBit).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      (coeffAdderCounterValueBit n counterWidth counterBit).get x := by
  let observed := coeffAdderCounterValueBit n counterWidth counterBit
  have hu : ∀ i : Fin n,
      ((coeffAdderUWord n counterWidth).bit i).wire ≠ observed.wire := by
    intro i
    simpa [observed, coeffAdderUWord, liftedUWord] using
      coeffAdderLiftedRegisterBit_counterValueBit_wire_ne
        n counterWidth (RegisterBits.uValueBit n counterWidth i) counterBit
        (by
          simpa [RegisterBits.uValueBit] using
            RegisterBits.u_counter_wire_ne n counterWidth
              (WireAddress.littleEndianWire i)
              (WireAddress.littleEndianWire counterBit))
  have hv : ∀ i : Fin n,
      ((coeffAdderVWord n counterWidth).bit i).wire ≠ observed.wire := by
    intro i
    simpa [observed, coeffAdderVWord, liftedVWord] using
      coeffAdderLiftedRegisterBit_counterValueBit_wire_ne
        n counterWidth (RegisterBits.vValueBit n counterWidth i) counterBit
        (by
          simpa [RegisterBits.vValueBit] using
            RegisterBits.v_counter_wire_ne n counterWidth
              (WireAddress.littleEndianWire i)
              (WireAddress.littleEndianWire counterBit))
  have hs : ∀ i : Fin (n + 1),
      ((coeffAdderSCoeffWord n counterWidth).bit i).wire ≠ observed.wire := by
    intro i
    simpa [observed, coeffAdderSCoeffWord, liftedSCoeffWord] using
      coeffAdderLiftedRegisterBit_counterValueBit_wire_ne
        n counterWidth (RegisterBits.sCoeffBit n counterWidth i) counterBit
        (RegisterBits.sCoeff_counter_wire_ne n counterWidth i
          (WireAddress.littleEndianWire counterBit))
  have hr : ∀ i : Fin (n + 1),
      ((coeffAdderRCoeffWord n counterWidth).bit i).wire ≠ observed.wire := by
    intro i
    simpa [observed, coeffAdderRCoeffWord, liftedRCoeffWord] using
      coeffAdderLiftedRegisterBit_counterValueBit_wire_ne
        n counterWidth (RegisterBits.rCoeffBit n counterWidth i) counterBit
        (RegisterBits.rCoeff_counter_wire_ne n counterWidth i
          (WireAddress.littleEndianWire counterBit))
  have hcomparisonWork : ∀ j : Fin (n - 1),
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit j).wire ≠
        observed.wire := by
    intro j
    simpa [observed, coeffAdderComparisonCarryPrefixWord] using
      coeffAdderComparisonCarryBit_counterValueBit_wire_ne
        n counterWidth (coeffAdderComparisonCarryPrefixIndex n j) counterBit
  have hcoeffWork : ∀ j : Fin ((n + 1) - 1),
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit j).wire ≠
        observed.wire := by
    intro j
    simpa [observed, liftedCoeffAdderCarryWorkWord] using
      liftedCoeffAdderCarryWorkBit_counterValueBit_wire_ne
        n counterWidth j counterBit
  have haddVIntoU : ∀ y,
      observed.get (coeffWorkAddVIntoUStep n counterWidth y) =
        observed.get y := by
    intro y
    exact coeffWorkAddVIntoUStep_get_observed_of_right_work_ne
      n counterWidth observed hu hcomparisonWork y
  have hsubVFromU : ∀ y,
      observed.get (coeffWorkSubVFromUStep n counterWidth y) =
        observed.get y := by
    intro y
    have hforward := haddVIntoU
      (coeffWorkSubVFromUStep n counterWidth y)
    rw [coeffWorkAddVIntoUStep_comp_subVFromU n counterWidth y] at hforward
    exact hforward.symm
  have haddUIntoV : ∀ y,
      observed.get (coeffWorkAddUIntoVStep n counterWidth y) =
        observed.get y := by
    intro y
    exact coeffWorkAddUIntoVStep_get_observed_of_right_work_ne
      n counterWidth observed hv hcomparisonWork y
  have hsubUFromV : ∀ y,
      observed.get (coeffWorkSubUFromVStep n counterWidth y) =
        observed.get y := by
    intro y
    have hforward := haddUIntoV
      (coeffWorkSubUFromVStep n counterWidth y)
    rw [coeffWorkAddUIntoVStep_comp_subUFromV n counterWidth y] at hforward
    exact hforward.symm
  have haddSIntoR : ∀ y,
      observed.get (coefficientAddSIntoRStep n counterWidth y) =
        observed.get y := by
    intro y
    exact coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth observed hr hcoeffWork y
  have haddRIntoS : ∀ y,
      observed.get (coefficientAddRIntoSStep n counterWidth y) =
        observed.get y := by
    intro y
    exact coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth observed hs hcoeffWork y
  have huGreaterPath : ∀ y,
      observed.get
          (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth y) =
        observed.get y := by
    intro y
    rw [coeffWorkSubVFromUThenAddSIntoRStep]
    rw [haddSIntoR]
    exact hsubVFromU y
  have hvLePath : ∀ y,
      observed.get
          (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth y) =
        observed.get y := by
    intro y
    rw [coeffWorkSubUFromVThenAddRIntoSStep]
    rw [haddRIntoS]
    exact hsubUFromV y
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact huGreaterPath x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h : (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact hvLePath x

/-- The selected odd data path preserves the complete physical padding counter
when its reusable control bits start clean. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_counter_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry :
      (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.counter =
      x.1.1.counter := by
  apply word_eq_of_testBit_eq
  intro counterBit
  have h :=
    coeffWorkCompareSelectedOddDataPathStep_get_counterValueBit_clean
      n counterWidth counterBit x hcontrolWork hsourceCarry
  simpa only [coeffAdderCounterValueBit_get] using h

/-- If the staged comparison readout is valid and `v < u`, the selected odd
data path reduces to the `uGreater` data path `u := u - v; r := r + s`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_valid_lt
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hlt : x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareSelectedOddDataPathStep n counterWidth x =
      coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = true := by
    rw [hcompareValid]
    simp [hlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
      n counterWidth x hcompare hcontrolWork hsourceCarry

/-- If the staged comparison readout is valid and `v < u` is false, the
selected odd data path reduces to the `vLe` data path `v := v - u; s := s + r`.
-/
lemma
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_valid_not_lt
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hnlt : ¬ x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkCompareSelectedOddDataPathStep n counterWidth x =
      coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = false := by
    rw [hcompareValid]
    simp [hnlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
      n counterWidth x hcompare hcontrolWork hsourceCarry

/-- The `u := u - v; r := r + s` atom lands on clean scratchA when the input
scratchA carry-in is clean. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_scratchA_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      false := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_scratchA]
  exact coeffWorkSubVFromUStep_get_scratchA_clean n counterWidth x hcarry

/-- The `v := v - u; s := s + r` atom lands on clean scratchA when the input
scratchA carry-in is clean. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_scratchA_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      false := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_scratchA]
  exact coeffWorkSubUFromVStep_get_scratchA_clean n counterWidth x hcarry

/-- The `u := u - v; r := r + s` atom preserves the active flag. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_active]
  exact coeffWorkSubVFromUStep_get_active n counterWidth x

/-- The `u := u - v; r := r + s` atom preserves the comparison ancilla. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_compare]
  exact coeffWorkSubVFromUStep_get_compare n counterWidth x

/-- The `v := v - u; s := s + r` atom preserves the active flag. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_active]
  exact coeffWorkSubUFromVStep_get_active n counterWidth x

/-- The `v := v - u; s := s + r` atom preserves the comparison ancilla. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_compare]
  exact coeffWorkSubUFromVStep_get_compare n counterWidth x

/-- The `u := u - v; r := r + s` atom preserves every stored branch-history
bit. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_historyBit]
  exact coeffWorkSubVFromUStep_get_historyBit n counterWidth historyIndex x

/-- The `v := v - u; s := s + r` atom preserves every stored branch-history
bit. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_historyBit]
  exact coeffWorkSubUFromVStep_get_historyBit n counterWidth historyIndex x

/-- The `u := u - v; r := r + s` atom preserves the second scratch bit. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_scratchB]
  exact coeffWorkSubVFromUStep_get_scratchB n counterWidth x

/-- The `v := v - u; s := s + r` atom preserves the second scratch bit. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_scratchB]
  exact coeffWorkSubUFromVStep_get_scratchB n counterWidth x

/-- The `u := u - v; r := r + s` atom preserves the untouched `v` source
word. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_v
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x).1.1.v =
      x.1.1.v := by
  let z := coeffWorkSubVFromUStep n counterWidth x
  have hpres :
      (coefficientAddSIntoRStep n counterWidth z).1.1.v = z.1.1.v := by
    apply word_eq_of_testBit_eq
    intro bit
    have h := coefficientAddSIntoRStep_get_vWordBit n counterWidth bit z
    simpa [coeffAdderVWord_get_testBit] using h
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  change (coefficientAddSIntoRStep n counterWidth z).1.1.v = x.1.1.v
  rw [hpres]
  exact coeffWorkSubVFromUStep_get_v n counterWidth x

/-- The `v := v - u; s := s + r` atom preserves the untouched `u` source
word. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_u
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x).1.1.u =
      x.1.1.u := by
  let z := coeffWorkSubUFromVStep n counterWidth x
  have hpres :
      (coefficientAddRIntoSStep n counterWidth z).1.1.u = z.1.1.u := by
    apply word_eq_of_testBit_eq
    intro bit
    have h := coefficientAddRIntoSStep_get_uWordBit n counterWidth bit z
    simpa [coeffAdderUWord_get_testBit] using h
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  change (coefficientAddRIntoSStep n counterWidth z).1.1.u = x.1.1.u
  rw [hpres]
  exact coeffWorkSubUFromVStep_get_u n counterWidth x

/-- The `u := u - v; r := r + s` atom preserves the dedicated coefficient-
adder carry-in bit. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_coeffCarryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_carryIn]
  exact coeffWorkSubVFromUStep_get_coeffCarryIn n counterWidth x

/-- The `v := v - u; s := s + r` atom preserves the dedicated coefficient-
adder carry-in bit. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_coeffCarryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_carryIn]
  exact coeffWorkSubUFromVStep_get_coeffCarryIn n counterWidth x

/-- On clean coefficient-adder work inputs, the `u := u - v; r := r + s` atom
restores each temporary coefficient-adder carry-work bit to false. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hclean :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      false := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  apply coefficientAddSIntoRStep_get_carryWork_clean
  intro k
  rw [coeffWorkSubVFromUStep_get_coeffCarryWorkBit]
  exact hclean k

/-- On clean coefficient-adder work inputs, the `v := v - u; s := s + r` atom
restores each temporary coefficient-adder carry-work bit to false. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hclean :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      false := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  apply coefficientAddRIntoSStep_get_carryWork_clean
  intro k
  rw [coeffWorkSubUFromVStep_get_coeffCarryWorkBit]
  exact hclean k

/-- The `r := r + s` coefficient update preserves each comparison-prefix
carry-work bit after the `u := u - v` source subtraction. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_comparisonCarryPrefix
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubVFromUStep n counterWidth x) := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  simpa [coeffAdderComparisonCarryPrefixWord] using
    coefficientAddSIntoRStep_get_comparisonCarry n counterWidth
      (coeffAdderComparisonCarryPrefixIndex n bit)
      (coeffWorkSubVFromUStep n counterWidth x)

/-- The `u := u - v; r := r + s` atom restores each comparison-prefix carry-work
bit when the input comparison-prefix work is clean. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      false := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep_get_comparisonCarryPrefix]
  exact coeffWorkSubVFromUStep_get_comparisonCarryPrefix_clean
    n counterWidth bit x hwork

/-- The `s := s + r` coefficient update preserves each comparison-prefix
carry-work bit after the `v := v - u` source subtraction. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_comparisonCarryPrefix
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubUFromVStep n counterWidth x) := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  simpa [coeffAdderComparisonCarryPrefixWord] using
    coefficientAddRIntoSStep_get_comparisonCarry n counterWidth
      (coeffAdderComparisonCarryPrefixIndex n bit)
      (coeffWorkSubUFromVStep n counterWidth x)

/-- The `v := v - u; s := s + r` atom restores each comparison-prefix carry-work
bit when the input comparison-prefix work is clean. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      false := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep_get_comparisonCarryPrefix]
  exact coeffWorkSubUFromVStep_get_comparisonCarryPrefix_clean
    n counterWidth bit x hwork

/-- The complete `u := u - v; r := r + s` odd data-path atom preserves the
final comparison carry. -/
lemma
    coeffWorkSubVFromUThenAddSIntoRStep_get_finalComparisonCarry
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hfinal : finalBit.val + 1 = n) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_comparisonCarry]
  exact coeffWorkSubVFromUStep_get_finalComparisonCarry
    n counterWidth finalBit x hfinal

/-- The complete `v := v - u; s := s + r` odd data-path atom preserves the
final comparison carry. -/
lemma
    coeffWorkSubUFromVThenAddRIntoSStep_get_finalComparisonCarry
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hfinal : finalBit.val + 1 = n) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get x := by
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_comparisonCarry]
  exact coeffWorkSubUFromVStep_get_finalComparisonCarry
    n counterWidth finalBit x hfinal

/-- The `u := u - v; r := r + s` atom keeps the source-subtract arithmetic
endpoint for `u` on clean source-adder carry/work inputs. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_u_sub_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x).1.1.u =
      x.1.1.u - x.1.1.v := by
  let z := coeffWorkSubVFromUStep n counterWidth x
  have hpres :
      (coefficientAddSIntoRStep n counterWidth z).1.1.u = z.1.1.u := by
    apply word_eq_of_testBit_eq
    intro bit
    have h := coefficientAddSIntoRStep_get_uWordBit n counterWidth bit z
    simpa [coeffAdderUWord_get_testBit] using h
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  change (coefficientAddSIntoRStep n counterWidth z).1.1.u =
    x.1.1.u - x.1.1.v
  rw [hpres]
  exact coeffWorkSubVFromUStep_get_u_sub_of_clean
    n counterWidth x hcarry hwork

/-- The `u := u - v; r := r + s` atom preserves the untouched `s`
coefficient. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  let z := coeffWorkSubVFromUStep n counterWidth x
  have hpres :
      (coefficientAddSIntoRStep n counterWidth z).1.1.sCoeff =
        z.1.1.sCoeff := by
    apply word_eq_of_testBit_eq
    intro bit
    have h := coefficientAddSIntoRStep_get_sCoeffWordBit
      n counterWidth bit z
    simpa [coeffAdderSCoeffValueWord_get_testBit] using h
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  change (coefficientAddSIntoRStep n counterWidth z).1.1.sCoeff =
    x.1.1.sCoeff
  rw [hpres]
  exact coeffWorkSubVFromUStep_get_sCoeff n counterWidth x

/-- The `u := u - v; r := r + s` atom writes the coefficient target `r` as
`r + s` on clean coefficient-adder carry/work inputs. -/
lemma coeffWorkSubVFromUThenAddSIntoRStep_get_rCoeff_add_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff := by
  let z := coeffWorkSubVFromUStep n counterWidth x
  have hcarryZ :
      (liftedCoeffAdderCarryInBit n counterWidth).get z = false := by
    dsimp [z]
    rw [coeffWorkSubVFromUStep_get_coeffCarryIn]
    exact hcarry
  have hworkZ :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get z =
          false := by
    intro k
    dsimp [z]
    rw [coeffWorkSubVFromUStep_get_coeffCarryWorkBit]
    exact hwork k
  have hmain :=
    coefficientAddSIntoRStep_get_rCoeff_add_of_clean
      n counterWidth z hcarryZ hworkZ
  have hr := coeffWorkSubVFromUStep_get_rCoeff n counterWidth x
  have hs := coeffWorkSubVFromUStep_get_sCoeff n counterWidth x
  rw [coeffWorkSubVFromUThenAddSIntoRStep]
  change (coefficientAddSIntoRStep n counterWidth z).1.1.rCoeff =
    x.1.1.rCoeff + x.1.1.sCoeff
  dsimp [z] at hmain
  rw [hr, hs] at hmain
  exact hmain

/-- The `v := v - u; s := s + r` atom keeps the source-subtract arithmetic
endpoint for `v` on clean source-adder carry/work inputs. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_v_sub_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x).1.1.v =
      x.1.1.v - x.1.1.u := by
  let z := coeffWorkSubUFromVStep n counterWidth x
  have hpres :
      (coefficientAddRIntoSStep n counterWidth z).1.1.v = z.1.1.v := by
    apply word_eq_of_testBit_eq
    intro bit
    have h := coefficientAddRIntoSStep_get_vWordBit n counterWidth bit z
    simpa [coeffAdderVWord_get_testBit] using h
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  change (coefficientAddRIntoSStep n counterWidth z).1.1.v =
    x.1.1.v - x.1.1.u
  rw [hpres]
  exact coeffWorkSubUFromVStep_get_v_sub_of_clean
    n counterWidth x hcarry hwork

/-- The `v := v - u; s := s + r` atom preserves the untouched `r`
coefficient. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  let z := coeffWorkSubUFromVStep n counterWidth x
  have hpres :
      (coefficientAddRIntoSStep n counterWidth z).1.1.rCoeff =
        z.1.1.rCoeff := by
    apply word_eq_of_testBit_eq
    intro bit
    have h := coefficientAddRIntoSStep_get_rCoeffWordBit
      n counterWidth bit z
    simpa [coeffAdderRCoeffValueWord_get_testBit] using h
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  change (coefficientAddRIntoSStep n counterWidth z).1.1.rCoeff =
    x.1.1.rCoeff
  rw [hpres]
  exact coeffWorkSubUFromVStep_get_rCoeff n counterWidth x

/-- The `v := v - u; s := s + r` atom writes the coefficient target `s` as
`s + r` on clean coefficient-adder carry/work inputs. -/
lemma coeffWorkSubUFromVThenAddRIntoSStep_get_sCoeff_add_of_clean
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff := by
  let z := coeffWorkSubUFromVStep n counterWidth x
  have hcarryZ :
      (liftedCoeffAdderCarryInBit n counterWidth).get z = false := by
    dsimp [z]
    rw [coeffWorkSubUFromVStep_get_coeffCarryIn]
    exact hcarry
  have hworkZ :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get z =
          false := by
    intro k
    dsimp [z]
    rw [coeffWorkSubUFromVStep_get_coeffCarryWorkBit]
    exact hwork k
  have hmain :=
    coefficientAddRIntoSStep_get_sCoeff_add_of_clean
      n counterWidth z hcarryZ hworkZ
  have hs := coeffWorkSubUFromVStep_get_sCoeff n counterWidth x
  have hr := coeffWorkSubUFromVStep_get_rCoeff n counterWidth x
  rw [coeffWorkSubUFromVThenAddRIntoSStep]
  change (coefficientAddRIntoSStep n counterWidth z).1.1.sCoeff =
    x.1.1.sCoeff + x.1.1.rCoeff
  dsimp [z] at hmain
  rw [hs, hr] at hmain
  exact hmain

/-- Under compare=true and clean source-subtract inputs, the selected odd data
path writes `u := u - v`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_u_sub_of_compare_true_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.u =
      x.1.1.u - x.1.1.v := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubVFromUThenAddSIntoRStep_get_u_sub_of_clean
    n counterWidth x hsourceCarry hsourceWork

/-- Under a valid staged comparison with `v < u`, the selected odd data path
writes `u := u - v`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_u_sub_of_compare_valid_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hlt : x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.u =
      x.1.1.u - x.1.1.v := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = true := by
    rw [hcompareValid]
    simp [hlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_u_sub_of_compare_true_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry hsourceWork

/-- Under compare=true, clean selected-control inputs, and clean coefficient-
adder work, the selected odd data path writes `r := r + s`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_add_of_compare_true_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hcoeffWork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubVFromUThenAddSIntoRStep_get_rCoeff_add_of_clean
    n counterWidth x hcontrolWork hcoeffWork

/-- Under a valid staged comparison with `v < u` and clean coefficient-adder
work, the selected odd data path writes `r := r + s`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_add_of_compare_valid_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hlt : x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hcoeffWork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = true := by
    rw [hcompareValid]
    simp [hlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_add_of_compare_true_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry hcoeffWork

/-- Under compare=false and clean source-subtract inputs, the selected odd data
path writes `v := v - u`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_v_sub_of_compare_false_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.v =
      x.1.1.v - x.1.1.u := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubUFromVThenAddRIntoSStep_get_v_sub_of_clean
    n counterWidth x hsourceCarry hsourceWork

/-- Under a valid staged comparison with `v < u` false, the selected odd data
path writes `v := v - u`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_v_sub_of_compare_valid_not_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hnlt : ¬ x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.v =
      x.1.1.v - x.1.1.u := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = false := by
    rw [hcompareValid]
    simp [hnlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_v_sub_of_compare_false_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry hsourceWork

/-- Under compare=true and clean selected-control inputs, the selected odd data
path preserves the untouched `v` source word. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_v_of_compare_true_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.v =
      x.1.1.v := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubVFromUThenAddSIntoRStep_get_v n counterWidth x

/-- Under a valid staged comparison with `v < u`, the selected odd data path
preserves the untouched `v` source word. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_v_of_compare_valid_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hlt : x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.v =
      x.1.1.v := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = true := by
    rw [hcompareValid]
    simp [hlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_v_of_compare_true_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry

/-- Under compare=true and clean selected-control inputs, the selected odd data
path preserves the untouched `s` coefficient word. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_of_compare_true_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubVFromUThenAddSIntoRStep_get_sCoeff n counterWidth x

/-- Under a valid staged comparison with `v < u`, the selected odd data path
preserves the untouched `s` coefficient word. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_of_compare_valid_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hlt : x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = true := by
    rw [hcompareValid]
    simp [hlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_of_compare_true_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry

/-- Under compare=false and clean selected-control inputs, the selected odd
data path preserves the untouched `u` source word. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_u_of_compare_false_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.u =
      x.1.1.u := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubUFromVThenAddRIntoSStep_get_u n counterWidth x

/-- Under a valid staged comparison with `v < u` false, the selected odd data
path preserves the untouched `u` source word. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_u_of_compare_valid_not_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hnlt : ¬ x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.u =
      x.1.1.u := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = false := by
    rw [hcompareValid]
    simp [hnlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_u_of_compare_false_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry

/-- Under compare=false and clean selected-control inputs, the selected odd
data path preserves the untouched `r` coefficient word. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_of_compare_false_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubUFromVThenAddRIntoSStep_get_rCoeff n counterWidth x

/-- Under a valid staged comparison with `v < u` false, the selected odd data
path preserves the untouched `r` coefficient word. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_of_compare_valid_not_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hnlt : ¬ x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = false := by
    rw [hcompareValid]
    simp [hnlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_of_compare_false_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry

/-- Under compare=false, clean selected-control inputs, and clean coefficient-
adder work, the selected odd data path writes `s := s + r`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_add_of_compare_false_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hcoeffWork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff := by
  rw [
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
      n counterWidth x hcompare hcontrolWork hsourceCarry]
  exact coeffWorkSubUFromVThenAddRIntoSStep_get_sCoeff_add_of_clean
    n counterWidth x hcontrolWork hcoeffWork

/-- Under a valid staged comparison with `v < u` false and clean coefficient-
adder work, the selected odd data path writes `s := s + r`. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_add_of_compare_valid_not_lt_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompareValid :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hnlt : ¬ x.1.1.v.val < x.1.1.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hcoeffWork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkCompareSelectedOddDataPathStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff := by
  have hcompare : (coeffAdderCompareBit n counterWidth).get x = false := by
    rw [hcompareValid]
    simp [hnlt]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_add_of_compare_false_clean
      n counterWidth x hcompare hcontrolWork hsourceCarry hcoeffWork

/-- On clean selected-control inputs, the selected odd data path restores
scratchA. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_scratchA_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      false := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact coeffWorkSubVFromUThenAddSIntoRStep_get_scratchA_clean
      n counterWidth x hsourceCarry
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact coeffWorkSubUFromVThenAddRIntoSStep_get_scratchA_clean
      n counterWidth x hsourceCarry

/-- On clean selected-control inputs and clean source-subtract work inputs, the
selected odd data path restores each comparison-prefix carry bit. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      false := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact coeffWorkSubVFromUThenAddSIntoRStep_get_comparisonCarryPrefix_clean
      n counterWidth bit x hsourceWork
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact
      coeffWorkSubUFromVThenAddRIntoSStep_get_comparisonCarryPrefix_clean
        n counterWidth bit x hsourceWork

/-- On clean selected-control inputs, the selected odd data path preserves a
clean final comparison carry.  This closes the one comparison-work bit not
covered by the source adders' prefix workspace. -/
lemma
    coeffWorkCompareSelectedOddDataPathStep_get_finalComparisonCarry_clean
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hfinal : finalBit.val + 1 = n)
    (hfinalClean :
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get x = false) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      false := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    rw [coeffWorkSubVFromUThenAddSIntoRStep_get_finalComparisonCarry
      n counterWidth finalBit x hfinal]
    exact hfinalClean
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    rw [coeffWorkSubUFromVThenAddRIntoSStep_get_finalComparisonCarry
      n counterWidth finalBit x hfinal]
    exact hfinalClean

/-- On clean selected-control inputs, the selected odd data path preserves the
active flag. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_active
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact coeffWorkSubVFromUThenAddSIntoRStep_get_active n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact coeffWorkSubUFromVThenAddRIntoSStep_get_active n counterWidth x

/-- On clean selected-control inputs, the selected odd data path preserves the
compare readout. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_compare
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact coeffWorkSubVFromUThenAddSIntoRStep_get_compare n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact coeffWorkSubUFromVThenAddRIntoSStep_get_compare n counterWidth x

/-- On clean selected-control inputs, the selected odd data path preserves
every stored branch-history bit. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact coeffWorkSubVFromUThenAddSIntoRStep_get_historyBit
      n counterWidth historyIndex x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact coeffWorkSubUFromVThenAddRIntoSStep_get_historyBit
      n counterWidth historyIndex x

/-- On clean selected-control inputs, the selected odd data path preserves the
second scratch bit. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_scratchB
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact coeffWorkSubVFromUThenAddSIntoRStep_get_scratchB
      n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact coeffWorkSubUFromVThenAddRIntoSStep_get_scratchB
      n counterWidth x

/-- On clean selected-control inputs, the selected odd data path preserves the
dedicated coefficient-adder carry-in bit. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_coeffCarryIn
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact
      coeffWorkSubVFromUThenAddSIntoRStep_get_coeffCarryIn
        n counterWidth x
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact
      coeffWorkSubUFromVThenAddRIntoSStep_get_coeffCarryIn
        n counterWidth x

/-- On clean selected-control inputs, the selected odd data path restores the
dedicated coefficient-adder carry-in bit. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_coeffCarryIn_clean
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      false := by
  rw [coeffWorkCompareSelectedOddDataPathStep_get_coeffCarryIn
    n counterWidth x hcontrolWork hsourceCarry]
  exact hcontrolWork

/-- On clean selected-control inputs and clean coefficient-adder work inputs,
the selected odd data path restores each dedicated coefficient-adder carry-work
bit. -/
lemma coeffWorkCompareSelectedOddDataPathStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hsourceCarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hclean :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coeffWorkCompareSelectedOddDataPathStep n counterWidth x) =
      false := by
  by_cases hcompare :
      (coeffAdderCompareBit n counterWidth).get x = true
  · rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_true
        n counterWidth x hcompare hcontrolWork hsourceCarry]
    exact coeffWorkSubVFromUThenAddSIntoRStep_get_carryWork_clean
      n counterWidth bit x hclean
  · have hcompareFalse :
        (coeffAdderCompareBit n counterWidth).get x = false := by
      cases h :
          (coeffAdderCompareBit n counterWidth).get x <;> simp_all
    rw [
      coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_false
        n counterWidth x hcompareFalse hcontrolWork hsourceCarry]
    exact coeffWorkSubUFromVThenAddRIntoSStep_get_carryWork_clean
      n counterWidth bit x hclean

/-! ## Coefficient-work sequencing scaffold -/

/-- Lift a comparison-work state update over the trailing dedicated
coefficient-adder work object. -/
def liftComparisonWorkStepToCoeffAdderWork
    (n counterWidth : Nat)
    (step :
      RegistersWithComparisonWork n counterWidth ->
        RegistersWithComparisonWork n counterWidth) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x => (step x.1, x.2)

/-- Lift an actual comparison-work circuit over the trailing dedicated
coefficient-adder work object. -/
def liftComparisonWorkProgramToCoeffAdderWork
    (n counterWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical
          (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (coeffAdderWorkEncoding n).width program

/-- Lifting an actual comparison-work circuit preserves its semantic action
while leaving the coefficient-adder work object unchanged. -/
lemma liftComparisonWorkProgramToCoeffAdderWork_realizes
    (n counterWidth : Nat)
    {program : UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical
          (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum}
    {step :
      RegistersWithComparisonWork n counterWidth ->
        RegistersWithComparisonWork n counterWidth}
    (h : UnitaryCircuit.Realizes
      (registersWithComparisonWorkEncoding n counterWidth) program environment step) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (liftComparisonWorkProgramToCoeffAdderWork n counterWidth program) environment
      (liftComparisonWorkStepToCoeffAdderWork n counterWidth step) := by
  exact UnitaryCircuit.Realizes.onBinaryPrefix
    (right := coeffAdderWorkEncoding n) h

/-- The comparison-controlled `u`/`v` swap circuit lifted over the trailing
coefficient-adder workspace. -/
def coeffWorkCompareControlledUVSwapProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (compareControlledUVSwapProgram n counterWidth)

/-- The comparison-controlled `u`/`v` swap lifted to the coefficient-adder
workspace. -/
def coeffWorkCompareControlledUVSwapStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (compareControlledUVSwapStep n counterWidth)

/-- The lifted comparison-controlled `u`/`v` swap circuit realizes its step. -/
lemma coeffWorkCompareControlledUVSwap_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareControlledUVSwapProgram n counterWidth) environment
      (coeffWorkCompareControlledUVSwapStep n counterWidth) := by
  exact liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (compareControlledUVSwap_realizes n counterWidth)

/-- The comparison-controlled `r`/`s` swap circuit lifted over the trailing
coefficient-adder workspace. -/
def coeffWorkCompareControlledRSSwapProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (compareControlledRSSwapProgram n counterWidth)

/-- The comparison-controlled `r`/`s` coefficient swap lifted to the
coefficient-adder workspace. -/
def coeffWorkCompareControlledRSSwapStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (compareControlledRSSwapStep n counterWidth)

/-- The lifted comparison-controlled `r`/`s` swap circuit realizes its step. -/
lemma coeffWorkCompareControlledRSSwap_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareControlledRSSwapProgram n counterWidth) environment
      (coeffWorkCompareControlledRSSwapStep n counterWidth) := by
  exact liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (compareControlledRSSwap_realizes n counterWidth)

/-- Circuit for the coefficient-work-lifted sequence of the
comparison-controlled `u`/`v` and `r`/`s` swaps. -/
def coeffWorkCompareControlledSwapsProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkCompareControlledUVSwapProgram n counterWidth)
    (coeffWorkCompareControlledRSSwapProgram n counterWidth)

/-- Coefficient-work-lifted sequence of the comparison-controlled `u`/`v` and
`r`/`s` swaps.  This is a composition scaffold for the swap-based Kaliski
round data path, not the full branch arithmetic update
[HJN+20, modular-arithmetic.tex:176-195]. -/
def coeffWorkCompareControlledSwapsStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkCompareControlledRSSwapStep n counterWidth
      (coeffWorkCompareControlledUVSwapStep n counterWidth x)

/-- The sequential lifted swap circuit realizes both controlled swaps. -/
lemma coeffWorkCompareControlledSwaps_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareControlledSwapsProgram n counterWidth) environment
      (coeffWorkCompareControlledSwapsStep n counterWidth) := by
  unfold coeffWorkCompareControlledSwapsProgram
    coeffWorkCompareControlledSwapsStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkCompareControlledUVSwapStep n counterWidth)
    (secondStep := coeffWorkCompareControlledRSSwapStep n counterWidth)
    (coeffWorkCompareControlledUVSwap_realizes n counterWidth)
    (coeffWorkCompareControlledRSSwap_realizes n counterWidth)

/-- The lifted `u`/`v` swap preserves the coefficient-adder work object. -/
lemma coeffWorkCompareControlledUVSwapStep_get_coeffAdderWork
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkCompareControlledUVSwapStep n counterWidth x).2 = x.2 := by
  rfl

/-- The lifted `r`/`s` swap preserves the coefficient-adder work object. -/
lemma coeffWorkCompareControlledRSSwapStep_get_coeffAdderWork
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkCompareControlledRSSwapStep n counterWidth x).2 = x.2 := by
  rfl

/-- The lifted paired swap sequence preserves the coefficient-adder work
object. -/
lemma coeffWorkCompareControlledSwapsStep_get_coeffAdderWork
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkCompareControlledSwapsStep n counterWidth x).2 = x.2 := by
  rfl

/-- The lifted paired swap sequence preserves the coefficient-adder carry-in
flag. -/
lemma coeffWorkCompareControlledSwapsStep_get_carryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- The lifted paired swap sequence preserves each coefficient-adder temporary
carry-work bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_carryWorkBit
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get x := by
  rfl

/-- The lifted paired swap sequence preserves the comparison ancilla. -/
lemma coeffWorkCompareControlledSwapsStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  simpa [coeffWorkCompareControlledSwapsStep,
    coeffWorkCompareControlledRSSwapStep,
    coeffWorkCompareControlledUVSwapStep,
    liftComparisonWorkStepToCoeffAdderWork, coeffAdderCompareBit,
    liftComparisonStateBitToCoeffAdderWork,
    BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep]
    using compareControlledUVRSSwapStep_get_compare n counterWidth x.1

/-- The lifted paired swap sequence preserves the active flag. -/
lemma coeffWorkCompareControlledSwapsStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  simpa [coeffWorkCompareControlledSwapsStep,
    coeffWorkCompareControlledRSSwapStep,
    coeffWorkCompareControlledUVSwapStep,
    liftComparisonWorkStepToCoeffAdderWork, coeffAdderActiveBit,
    liftComparisonStateBitToCoeffAdderWork,
    BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep]
    using compareControlledUVRSSwapStep_get_active n counterWidth x.1

/-- The lifted paired swap sequence preserves every stored branch-history
bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  simpa [coeffWorkCompareControlledSwapsStep,
    coeffWorkCompareControlledRSSwapStep,
    coeffWorkCompareControlledUVSwapStep,
    liftComparisonWorkStepToCoeffAdderWork, coeffAdderHistoryBit,
    liftComparisonStateBitToCoeffAdderWork,
    BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep]
    using compareControlledUVRSSwapStep_get_historyBit
      n counterWidth historyIndex x.1

/-- The lifted paired swap sequence preserves the first scratch bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  simpa [coeffWorkCompareControlledSwapsStep,
    coeffWorkCompareControlledRSSwapStep,
    coeffWorkCompareControlledUVSwapStep,
    liftComparisonWorkStepToCoeffAdderWork, coeffAdderScratchABit,
    liftComparisonStateBitToCoeffAdderWork,
    BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep]
    using compareControlledUVRSSwapStep_get_scratchA n counterWidth x.1

/-- The lifted paired swap sequence preserves the second scratch bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  simpa [coeffWorkCompareControlledSwapsStep,
    coeffWorkCompareControlledRSSwapStep,
    coeffWorkCompareControlledUVSwapStep,
    liftComparisonWorkStepToCoeffAdderWork, coeffAdderScratchBBit,
    liftComparisonStateBitToCoeffAdderWork,
    BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep]
    using compareControlledUVRSSwapStep_get_scratchB n counterWidth x.1

/-- The lifted paired swap sequence preserves every comparison-work carry
bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  simpa [coeffWorkCompareControlledSwapsStep,
    coeffWorkCompareControlledRSSwapStep,
    coeffWorkCompareControlledUVSwapStep,
    liftComparisonWorkStepToCoeffAdderWork,
    coeffAdderComparisonCarryBit, liftComparisonStateBitToCoeffAdderWork,
    BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep]
    using
      compareControlledUVRSSwapStep_get_comparisonCarry
        n counterWidth workBit x.1

/-- The lifted paired swap sends the selected `v` value bit to `u` when
compare is set, and otherwise preserves the selected `u` value bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderVWord n counterWidth).bit bit).get x
      else
        ((coeffAdderUWord n counterWidth).bit bit).get x := by
  by_cases hcompare : (liftedCompareBit n counterWidth).get x.1 = true <;>
    simpa [coeffWorkCompareControlledSwapsStep,
      coeffWorkCompareControlledRSSwapStep,
      coeffWorkCompareControlledUVSwapStep,
      liftComparisonWorkStepToCoeffAdderWork, coeffAdderUWord,
      coeffAdderVWord, coeffAdderCompareBit,
      liftComparisonStateBitToCoeffAdderWork,
      BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep,
      hcompare] using
        compareControlledUVRSSwapStep_get_uWordBit
          n counterWidth bit x.1

/-- The lifted paired swap sends the selected `u` value bit to `v` when
compare is set, and otherwise preserves the selected `v` value bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderUWord n counterWidth).bit bit).get x
      else
        ((coeffAdderVWord n counterWidth).bit bit).get x := by
  by_cases hcompare : (liftedCompareBit n counterWidth).get x.1 = true <;>
    simpa [coeffWorkCompareControlledSwapsStep,
      coeffWorkCompareControlledRSSwapStep,
      coeffWorkCompareControlledUVSwapStep,
      liftComparisonWorkStepToCoeffAdderWork, coeffAdderUWord,
      coeffAdderVWord, coeffAdderCompareBit,
      liftComparisonStateBitToCoeffAdderWork,
      BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep,
      hcompare] using
        compareControlledUVRSSwapStep_get_vWordBit
          n counterWidth bit x.1

/-- The lifted paired swap sends the selected `s` coefficient bit to `r` when
compare is set, and otherwise preserves the selected `r` coefficient bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffWord n counterWidth).bit bit).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderSCoeffWord n counterWidth).bit bit).get x
      else
        ((coeffAdderRCoeffWord n counterWidth).bit bit).get x := by
  by_cases hcompare : (liftedCompareBit n counterWidth).get x.1 = true <;>
    simpa [coeffWorkCompareControlledSwapsStep,
      coeffWorkCompareControlledRSSwapStep,
      coeffWorkCompareControlledUVSwapStep,
      liftComparisonWorkStepToCoeffAdderWork, coeffAdderRCoeffWord,
      coeffAdderSCoeffWord, coeffAdderCompareBit,
      liftComparisonStateBitToCoeffAdderWork,
      BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep,
      hcompare] using
        compareControlledUVRSSwapStep_get_rCoeffWordBit
          n counterWidth bit x.1

/-- The lifted paired swap sends the selected `r` coefficient bit to `s` when
compare is set, and otherwise preserves the selected `s` coefficient bit. -/
lemma coeffWorkCompareControlledSwapsStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffWord n counterWidth).bit bit).get
        (coeffWorkCompareControlledSwapsStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderRCoeffWord n counterWidth).bit bit).get x
      else
        ((coeffAdderSCoeffWord n counterWidth).bit bit).get x := by
  by_cases hcompare : (liftedCompareBit n counterWidth).get x.1 = true <;>
    simpa [coeffWorkCompareControlledSwapsStep,
      coeffWorkCompareControlledRSSwapStep,
      coeffWorkCompareControlledUVSwapStep,
      liftComparisonWorkStepToCoeffAdderWork, coeffAdderRCoeffWord,
      coeffAdderSCoeffWord, coeffAdderCompareBit,
      liftComparisonStateBitToCoeffAdderWork,
      BinaryLabelEncoding.prodLeftBit, compareControlledUVRSSwapStep,
      hcompare] using
        compareControlledUVRSSwapStep_get_sCoeffWordBit
          n counterWidth bit x.1

/-! ## Swap-then-add sequencing scaffold -/

/-- Sequence the comparison-controlled swap scaffold with the `r`-into-`s`
coefficient adder.  This packages one swap-selected coefficient-add data-path
slice in a single circuit object; it is not yet a controlled branch update
or full Montgomery--Kaliski round [HJN+20, modular-arithmetic.tex:176-195;
RNSL17, ECDLP.tex:399-421; VBE95, 9511018.tex:237-264,591-618]. -/
def coeffWorkSwapsThenAddRIntoSProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkCompareControlledSwapsProgram n counterWidth)
    (coefficientAddRIntoSProgram n counterWidth)

/-- Semantic step for the comparison-controlled swap scaffold followed by the
`r`-into-`s` coefficient adder. -/
def coeffWorkSwapsThenAddRIntoSStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coefficientAddRIntoSStep n counterWidth
      (coeffWorkCompareControlledSwapsStep n counterWidth x)

/-- The swap-selected `r`-into-`s` circuit realizes its sequential step. -/
lemma coeffWorkSwapsThenAddRIntoS_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkSwapsThenAddRIntoSProgram n counterWidth) environment
      (coeffWorkSwapsThenAddRIntoSStep n counterWidth) := by
  unfold coeffWorkSwapsThenAddRIntoSProgram
    coeffWorkSwapsThenAddRIntoSStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkCompareControlledSwapsStep n counterWidth)
    (secondStep := coefficientAddRIntoSStep n counterWidth)
    (coeffWorkCompareControlledSwaps_realizes n counterWidth)
    (coefficientAddRIntoS_realizes n counterWidth)

/-- In the swap-selected `r`-into-`s` coefficient-add scaffold, the source
`r` bit is the post-swap `r` bit. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x
      else
        ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_rCoeffWordBit]
  have h :=
    coeffWorkCompareControlledSwapsStep_get_rCoeffWordBit n counterWidth
      (WireAddress.littleEndianWire bit) x
  simpa [coeffAdderRCoeffValueWord, coeffAdderSCoeffValueWord,
    coeffAdderRCoeffWord, coeffAdderSCoeffWord, liftedRCoeffValueWord,
    liftedSCoeffValueWord, liftedRCoeffWord, liftedSCoeffWord,
    RegisterBits.rCoeffValueBit, RegisterBits.sCoeffValueBit] using h

/-- Gate-list target-bit formula for the swap-selected `r`-into-`s`
coefficient-add scaffold. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      ((((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
          (coeffWorkCompareControlledSwapsStep n counterWidth x) ^^
        ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
          (coeffWorkCompareControlledSwapsStep n counterWidth x)) ^^
        (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
          (coefficientAddRIntoSLayout n counterWidth) bit).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coefficientAddRIntoSLayout n counterWidth)
            (coeffWorkCompareControlledSwapsStep n counterWidth x))) := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  exact
    coefficientAddRIntoSStep_get_sCoeffWordBit
      n counterWidth bit
      (coeffWorkCompareControlledSwapsStep n counterWidth x)

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves the
comparison ancilla. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_compare]
  rw [coeffWorkCompareControlledSwapsStep_get_compare]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves the
active flag. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_active]
  rw [coeffWorkCompareControlledSwapsStep_get_active]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves every
stored branch-history bit. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_historyBit]
  rw [coeffWorkCompareControlledSwapsStep_get_historyBit]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves the first
scratch bit. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_scratchA]
  rw [coeffWorkCompareControlledSwapsStep_get_scratchA]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves the second
scratch bit. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_scratchB]
  rw [coeffWorkCompareControlledSwapsStep_get_scratchB]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves every
comparison-work carry bit. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_comparisonCarry]
  rw [coeffWorkCompareControlledSwapsStep_get_comparisonCarry]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves the
post-swap `u` value bit formula. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderVWord n counterWidth).bit bit).get x
      else
        ((coeffAdderUWord n counterWidth).bit bit).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_uWordBit]
  rw [coeffWorkCompareControlledSwapsStep_get_uWordBit]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves the
post-swap `v` value bit formula. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderUWord n counterWidth).bit bit).get x
      else
        ((coeffAdderVWord n counterWidth).bit bit).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_vWordBit]
  rw [coeffWorkCompareControlledSwapsStep_get_vWordBit]

/-- The swap-selected `r`-into-`s` coefficient-add scaffold preserves the
dedicated coefficient-adder carry-in flag. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_carryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  rw [coefficientAddRIntoSStep_get_carryIn]
  rw [coeffWorkCompareControlledSwapsStep_get_carryIn]

/-- On clean coefficient-adder work inputs, the swap-selected `r`-into-`s`
coefficient-add scaffold restores each temporary carry-work bit to false. -/
lemma coeffWorkSwapsThenAddRIntoSStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hclean :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddRIntoSStep n counterWidth x) =
      false := by
  rw [coeffWorkSwapsThenAddRIntoSStep]
  apply coefficientAddRIntoSStep_get_carryWork_clean
  intro k
  rw [coeffWorkCompareControlledSwapsStep_get_carryWorkBit]
  exact hclean k

/-- Sequence the comparison-controlled swap scaffold with the `s`-into-`r`
coefficient adder.  This symmetric scaffold is still only a concrete
swap-plus-adder slice, not a full branch arithmetic update [HJN+20,
modular-arithmetic.tex:176-195; RNSL17, ECDLP.tex:399-421; VBE95,
9511018.tex:237-264,591-618]. -/
def coeffWorkSwapsThenAddSIntoRProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkCompareControlledSwapsProgram n counterWidth)
    (coefficientAddSIntoRProgram n counterWidth)

/-- Semantic step for the comparison-controlled swap scaffold followed by the
`s`-into-`r` coefficient adder. -/
def coeffWorkSwapsThenAddSIntoRStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coefficientAddSIntoRStep n counterWidth
      (coeffWorkCompareControlledSwapsStep n counterWidth x)

/-- The swap-selected `s`-into-`r` circuit realizes its sequential step. -/
lemma coeffWorkSwapsThenAddSIntoR_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkSwapsThenAddSIntoRProgram n counterWidth) environment
      (coeffWorkSwapsThenAddSIntoRStep n counterWidth) := by
  unfold coeffWorkSwapsThenAddSIntoRProgram
    coeffWorkSwapsThenAddSIntoRStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkCompareControlledSwapsStep n counterWidth)
    (secondStep := coefficientAddSIntoRStep n counterWidth)
    (coeffWorkCompareControlledSwaps_realizes n counterWidth)
    (coefficientAddSIntoR_realizes n counterWidth)

/-- In the swap-selected `s`-into-`r` coefficient-add scaffold, the source
`s` bit is the post-swap `s` bit. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x
      else
        ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_sCoeffWordBit]
  have h :=
    coeffWorkCompareControlledSwapsStep_get_sCoeffWordBit n counterWidth
      (WireAddress.littleEndianWire bit) x
  simpa [coeffAdderRCoeffValueWord, coeffAdderSCoeffValueWord,
    coeffAdderRCoeffWord, coeffAdderSCoeffWord, liftedRCoeffValueWord,
    liftedSCoeffValueWord, liftedRCoeffWord, liftedSCoeffWord,
    RegisterBits.rCoeffValueBit, RegisterBits.sCoeffValueBit] using h

/-- Gate-list target-bit formula for the swap-selected `s`-into-`r`
coefficient-add scaffold. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      ((((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
          (coeffWorkCompareControlledSwapsStep n counterWidth x) ^^
        ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
          (coeffWorkCompareControlledSwapsStep n counterWidth x)) ^^
        (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
          (coefficientAddSIntoRLayout n counterWidth) bit).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (coefficientAddSIntoRLayout n counterWidth)
            (coeffWorkCompareControlledSwapsStep n counterWidth x))) := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  exact
    coefficientAddSIntoRStep_get_rCoeffWordBit
      n counterWidth bit
      (coeffWorkCompareControlledSwapsStep n counterWidth x)

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves the
comparison ancilla. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_compare]
  rw [coeffWorkCompareControlledSwapsStep_get_compare]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves the
active flag. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_active]
  rw [coeffWorkCompareControlledSwapsStep_get_active]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves every
stored branch-history bit. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_historyBit]
  rw [coeffWorkCompareControlledSwapsStep_get_historyBit]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves the first
scratch bit. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_scratchA]
  rw [coeffWorkCompareControlledSwapsStep_get_scratchA]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves the second
scratch bit. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_scratchB]
  rw [coeffWorkCompareControlledSwapsStep_get_scratchB]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves every
comparison-work carry bit. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_comparisonCarry]
  rw [coeffWorkCompareControlledSwapsStep_get_comparisonCarry]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves the
post-swap `u` value bit formula. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderVWord n counterWidth).bit bit).get x
      else
        ((coeffAdderUWord n counterWidth).bit bit).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_uWordBit]
  rw [coeffWorkCompareControlledSwapsStep_get_uWordBit]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves the
post-swap `v` value bit formula. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      if (coeffAdderCompareBit n counterWidth).get x then
        ((coeffAdderUWord n counterWidth).bit bit).get x
      else
        ((coeffAdderVWord n counterWidth).bit bit).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_vWordBit]
  rw [coeffWorkCompareControlledSwapsStep_get_vWordBit]

/-- The swap-selected `s`-into-`r` coefficient-add scaffold preserves the
dedicated coefficient-adder carry-in flag. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_carryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  rw [coefficientAddSIntoRStep_get_carryIn]
  rw [coeffWorkCompareControlledSwapsStep_get_carryIn]

/-- On clean coefficient-adder work inputs, the swap-selected `s`-into-`r`
coefficient-add scaffold restores each temporary carry-work bit to false. -/
lemma coeffWorkSwapsThenAddSIntoRStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hclean :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (coeffWorkSwapsThenAddSIntoRStep n counterWidth x) =
      false := by
  rw [coeffWorkSwapsThenAddSIntoRStep]
  apply coefficientAddSIntoRStep_get_carryWork_clean
  intro k
  rw [coeffWorkCompareControlledSwapsStep_get_carryWorkBit]
  exact hclean k

lemma controlledAdjacentShiftLeftStep_get_observed_of_word_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control observed : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (hobserved : ∀ i, (word.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (EncodedBit.Word.controlledAdjacentShiftLeftStep control word hcontrol
          hword x) =
      observed.get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [EncodedBit.Word.controlledAdjacentShiftLeftGates] at hgate
  rcases List.mem_flatMap.mp hgate with ⟨i, _hi, hgate⟩
  simp only [EncodedBit.Word.controlledAdjacentSwapGates,
    EncodedBit.controlledSwapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with hgate | hgate | hgate <;> subst gate
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentLeftIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y

lemma controlledAdjacentShiftRightStep_get_observed_of_word_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control observed : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (hobserved : ∀ i, (word.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (EncodedBit.Word.controlledAdjacentShiftRightStep control word hcontrol
          hword x) =
      observed.get x := by
  unfold EncodedBit.Word.controlledAdjacentShiftRightStep
    EncodedBit.Word.controlledAdjacentShiftRightGates
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hleft :
      gate ∈ EncodedBit.Word.controlledAdjacentShiftLeftGates control word
        hcontrol hword := by
    simpa using List.mem_reverse.mp hgate
  rw [EncodedBit.Word.controlledAdjacentShiftLeftGates] at hleft
  rcases List.mem_flatMap.mp hleft with ⟨i, _hi, hleft⟩
  simp only [EncodedBit.Word.controlledAdjacentSwapGates,
    EncodedBit.controlledSwapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hleft
  rcases hleft with hleft | hleft | hleft <;> subst gate
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentLeftIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y

lemma adjacentShiftLeftStep_get_observed_of_word_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (observed : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (hobserved : ∀ i, (word.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (EncodedBit.Word.adjacentShiftLeftStep word hword x) =
      observed.get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [EncodedBit.Word.adjacentShiftLeftGates] at hgate
  rcases List.mem_flatMap.mp hgate with ⟨i, _hi, hgate⟩
  simp only [EncodedBit.Word.adjacentSwapGates,
    EncodedBit.swapGates, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with hgate | hgate | hgate <;> subst gate
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentLeftIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y

lemma adjacentShiftRightStep_get_observed_of_word_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (observed : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (hobserved : ∀ i, (word.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (EncodedBit.Word.adjacentShiftRightStep word hword x) =
      observed.get x := by
  unfold EncodedBit.Word.adjacentShiftRightStep
    EncodedBit.Word.adjacentShiftRightGates
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hleft :
      gate ∈ EncodedBit.Word.adjacentShiftLeftGates word hword := by
    simpa using List.mem_reverse.mp hgate
  rw [EncodedBit.Word.adjacentShiftLeftGates] at hleft
  rcases List.mem_flatMap.mp hleft with ⟨i, _hi, hleft⟩
  simp only [EncodedBit.Word.adjacentSwapGates,
    EncodedBit.swapGates, List.mem_cons, List.not_mem_nil, or_false] at hleft
  rcases hleft with hleft | hleft | hleft <;> subst gate
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentLeftIndex width i)) y
  · intro y
    exact EncodedBit.get_flip_of_wire_ne _ _
      (hobserved (EncodedBit.Word.adjacentRightIndex width i)) y

private lemma controlledSwapStep_eq_self_of_control_false
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire)
    (x : Data)
    (hcontrol : control.get x = false) :
    EncodedBit.controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight x = x := by
  unfold EncodedBit.controlledSwapStep EncodedBit.controlledSwapGates
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.toffoliStep, hcontrol]

private lemma controlledSwapStep_eq_swapStep_of_control_true
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire)
    (x : Data)
    (hcontrol : control.get x = true) :
    EncodedBit.controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight x =
      EncodedBit.swapStep left right hleftRight x := by
  unfold EncodedBit.controlledSwapStep EncodedBit.controlledSwapGates
    EncodedBit.swapStep EncodedBit.swapGates
  simp only [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step, id_eq]
  unfold EncodedBit.toffoliStep EncodedBit.cnotStep
  have hcontrolRight :
      control.get (right.flip x) = true := by
    rw [EncodedBit.get_flip_of_wire_ne right control (Ne.symm hcontrolRight),
      hcontrol]
  have hcontrolLeft :
      control.get (left.flip x) = true := by
    rw [EncodedBit.get_flip_of_wire_ne left control (Ne.symm hcontrolLeft),
      hcontrol]
  by_cases hl : left.get x <;>
    by_cases hr : right.get x <;>
    simp [hcontrol, hcontrolRight, hcontrolLeft, hl, hr,
      EncodedBit.get_flip_self,
      EncodedBit.get_flip_of_wire_ne,
      Ne.symm hleftRight, EncodedBit.flip_flip, EncodedBit.flip_comm]

private lemma controlledSwapStep_eq_of_control_get_eq
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (controlA controlB left right : EncodedBit encoding)
    (hAleft : controlA.wire ≠ left.wire)
    (hAright : controlA.wire ≠ right.wire)
    (hBleft : controlB.wire ≠ left.wire)
    (hBright : controlB.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire)
    (x : Data)
    (hcontrols : controlA.get x = controlB.get x) :
    EncodedBit.controlledSwapStep controlA left right
        hAleft hAright hleftRight x =
      EncodedBit.controlledSwapStep controlB left right
        hBleft hBright hleftRight x := by
  by_cases hcA : controlA.get x
  · have hcB : controlB.get x = true := by
      simpa [hcA] using hcontrols.symm
    rw [controlledSwapStep_eq_swapStep_of_control_true
      controlA left right hAleft hAright hleftRight x hcA]
    rw [controlledSwapStep_eq_swapStep_of_control_true
      controlB left right hBleft hBright hleftRight x hcB]
  · have hcAFalse : controlA.get x = false := Bool.eq_false_of_not_eq_true hcA
    have hcB : controlB.get x = false := by
      rw [← hcontrols]
      exact hcAFalse
    rw [controlledSwapStep_eq_self_of_control_false
      controlA left right hAleft hAright hleftRight x hcAFalse]
    rw [controlledSwapStep_eq_self_of_control_false
      controlB left right hBleft hBright hleftRight x hcB]

private lemma controlledAdjacentSwapIndexListStep_eq_of_control_get_eq
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (controlA controlB : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrolA : ∀ i, controlA.wire ≠ (word.bit i).wire)
    (hcontrolB : ∀ i, controlB.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (indices : List (Fin (width - 1)))
    (x : Data)
    (hcontrols : controlA.get x = controlB.get x) :
    EncodedBit.GateSpec.stepList
        (indices.flatMap
          (EncodedBit.Word.controlledAdjacentSwapGates
            controlA word hcontrolA hword)) x =
      EncodedBit.GateSpec.stepList
        (indices.flatMap
          (EncodedBit.Word.controlledAdjacentSwapGates
            controlB word hcontrolB hword)) x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons]
      rw [EncodedBit.GateSpec.stepList_append,
        EncodedBit.GateSpec.stepList_append]
      have hhead :
          EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates controlA word
                hcontrolA hword i) x =
            EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates controlB word
                hcontrolB hword i) x := by
        simpa [EncodedBit.Word.controlledAdjacentSwapGates,
          EncodedBit.controlledSwapStep] using
          controlledSwapStep_eq_of_control_get_eq
            controlA controlB
            (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
            (word.bit (EncodedBit.Word.adjacentRightIndex width i))
            (hcontrolA (EncodedBit.Word.adjacentLeftIndex width i))
            (hcontrolA (EncodedBit.Word.adjacentRightIndex width i))
            (hcontrolB (EncodedBit.Word.adjacentLeftIndex width i))
            (hcontrolB (EncodedBit.Word.adjacentRightIndex width i))
            (hword (EncodedBit.Word.adjacentLeftIndex width i)
              (EncodedBit.Word.adjacentRightIndex width i)
              (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex width i))
            x hcontrols
      have hcontrolsY :
          controlA.get
              (EncodedBit.GateSpec.stepList
                (EncodedBit.Word.controlledAdjacentSwapGates controlA word
                  hcontrolA hword i) x) =
            controlB.get
              (EncodedBit.GateSpec.stepList
                (EncodedBit.Word.controlledAdjacentSwapGates controlA word
                  hcontrolA hword i) x) := by
        rw [show
          EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates controlA word
                hcontrolA hword i) x =
            EncodedBit.controlledSwapStep controlA
              (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
              (word.bit (EncodedBit.Word.adjacentRightIndex width i))
              (hcontrolA (EncodedBit.Word.adjacentLeftIndex width i))
              (hcontrolA (EncodedBit.Word.adjacentRightIndex width i))
              (hword (EncodedBit.Word.adjacentLeftIndex width i)
                (EncodedBit.Word.adjacentRightIndex width i)
                (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex
                  width i))
              x by
          rfl]
        rw [EncodedBit.controlledSwapStep_get_control
          controlA
          (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
          (word.bit (EncodedBit.Word.adjacentRightIndex width i))
          (hcontrolA (EncodedBit.Word.adjacentLeftIndex width i))
          (hcontrolA (EncodedBit.Word.adjacentRightIndex width i))
          (hword (EncodedBit.Word.adjacentLeftIndex width i)
            (EncodedBit.Word.adjacentRightIndex width i)
            (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex width i))]
        rw [EncodedBit.controlledSwapStep_get_observed_of_swap_ne
          controlA
          (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
          (word.bit (EncodedBit.Word.adjacentRightIndex width i))
          controlB
          (hcontrolA (EncodedBit.Word.adjacentLeftIndex width i))
          (hcontrolA (EncodedBit.Word.adjacentRightIndex width i))
          (hword (EncodedBit.Word.adjacentLeftIndex width i)
            (EncodedBit.Word.adjacentRightIndex width i)
            (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex width i))
          (Ne.symm (hcontrolB (EncodedBit.Word.adjacentLeftIndex width i)))
          (Ne.symm (hcontrolB (EncodedBit.Word.adjacentRightIndex width i)))]
        exact hcontrols
      calc
        EncodedBit.GateSpec.stepList
            (rest.flatMap
              (EncodedBit.Word.controlledAdjacentSwapGates controlA word
                hcontrolA hword))
            (EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates controlA word
                hcontrolA hword i) x) =
          EncodedBit.GateSpec.stepList
            (rest.flatMap
              (EncodedBit.Word.controlledAdjacentSwapGates controlB word
                hcontrolB hword))
            (EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates controlA word
                hcontrolA hword i) x) := by
            exact ih _ hcontrolsY
        _ =
          EncodedBit.GateSpec.stepList
            (rest.flatMap
              (EncodedBit.Word.controlledAdjacentSwapGates controlB word
                hcontrolB hword))
            (EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates controlB word
                hcontrolB hword i) x) := by
            rw [hhead]

private lemma controlledAdjacentSwapIndexListStep_eq_self_of_control_false
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (indices : List (Fin (width - 1)))
    (x : Data)
    (hcontrolFalse : control.get x = false) :
    EncodedBit.GateSpec.stepList
        (indices.flatMap
          (EncodedBit.Word.controlledAdjacentSwapGates control word hcontrol
            hword)) x =
      x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons]
      rw [EncodedBit.GateSpec.stepList_append]
      have hhead :
          EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates control word
                hcontrol hword i) x =
            x := by
        simpa [EncodedBit.Word.controlledAdjacentSwapGates,
          EncodedBit.controlledSwapStep] using
          controlledSwapStep_eq_self_of_control_false
            control
            (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
            (word.bit (EncodedBit.Word.adjacentRightIndex width i))
            (hcontrol (EncodedBit.Word.adjacentLeftIndex width i))
            (hcontrol (EncodedBit.Word.adjacentRightIndex width i))
            (hword (EncodedBit.Word.adjacentLeftIndex width i)
              (EncodedBit.Word.adjacentRightIndex width i)
              (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex width i))
            x hcontrolFalse
      rw [hhead]
      exact ih x hcontrolFalse

lemma controlledAdjacentShiftLeftStep_eq_self_of_control_false
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data)
    (hcontrolFalse : control.get x = false) :
    EncodedBit.Word.controlledAdjacentShiftLeftStep control word hcontrol
        hword x =
      x := by
  unfold EncodedBit.Word.controlledAdjacentShiftLeftStep
    EncodedBit.Word.controlledAdjacentShiftLeftGates
  exact controlledAdjacentSwapIndexListStep_eq_self_of_control_false
    control word hcontrol hword (List.ofFn fun i : Fin (width - 1) => i) x
    hcontrolFalse

lemma controlledAdjacentShiftRightStep_eq_self_of_control_false
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data)
    (hcontrolFalse : control.get x = false) :
    EncodedBit.Word.controlledAdjacentShiftRightStep control word hcontrol
        hword x =
      x := by
  have hcontrolAfterRight :
      control.get
          (EncodedBit.Word.controlledAdjacentShiftRightStep control word
            hcontrol hword x) =
        false := by
    rw [controlledAdjacentShiftRightStep_get_observed_of_word_ne
      control control word hcontrol hword
      (fun i => Ne.symm (hcontrol i)) x]
    exact hcontrolFalse
  have hleftSelf :=
    controlledAdjacentShiftLeftStep_eq_self_of_control_false
      control word hcontrol hword
      (EncodedBit.Word.controlledAdjacentShiftRightStep control word hcontrol
        hword x)
      hcontrolAfterRight
  have hinv :=
    EncodedBit.Word.controlledAdjacentShiftLeftStep_controlledAdjacentShiftRightStep
      control word hcontrol hword x
  rw [hleftSelf] at hinv
  exact hinv

private lemma controlledAdjacentSwapIndexListStep_eq_adjacentSwapIndexListStep_of_control_true
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (indices : List (Fin (width - 1)))
    (x : Data)
    (hcontrolTrue : control.get x = true) :
    EncodedBit.GateSpec.stepList
        (indices.flatMap
          (EncodedBit.Word.controlledAdjacentSwapGates control word hcontrol
            hword)) x =
      EncodedBit.GateSpec.stepList
        (indices.flatMap (EncodedBit.Word.adjacentSwapGates word hword)) x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons]
      rw [EncodedBit.GateSpec.stepList_append,
        EncodedBit.GateSpec.stepList_append]
      have hhead :
          EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates control word
                hcontrol hword i) x =
            EncodedBit.GateSpec.stepList
              (EncodedBit.Word.adjacentSwapGates word hword i) x := by
        simpa [EncodedBit.Word.controlledAdjacentSwapGates,
          EncodedBit.Word.adjacentSwapGates, EncodedBit.controlledSwapStep,
          EncodedBit.swapStep] using
          controlledSwapStep_eq_swapStep_of_control_true
            control
            (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
            (word.bit (EncodedBit.Word.adjacentRightIndex width i))
            (hcontrol (EncodedBit.Word.adjacentLeftIndex width i))
            (hcontrol (EncodedBit.Word.adjacentRightIndex width i))
            (hword (EncodedBit.Word.adjacentLeftIndex width i)
              (EncodedBit.Word.adjacentRightIndex width i)
              (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex width i))
            x hcontrolTrue
      have hcontrolAfter :
          control.get
              (EncodedBit.GateSpec.stepList
                (EncodedBit.Word.controlledAdjacentSwapGates control word
                  hcontrol hword i) x) =
            true := by
        rw [show
          EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates control word
                hcontrol hword i) x =
            EncodedBit.controlledSwapStep control
              (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
              (word.bit (EncodedBit.Word.adjacentRightIndex width i))
              (hcontrol (EncodedBit.Word.adjacentLeftIndex width i))
              (hcontrol (EncodedBit.Word.adjacentRightIndex width i))
              (hword (EncodedBit.Word.adjacentLeftIndex width i)
                (EncodedBit.Word.adjacentRightIndex width i)
                (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex
                  width i))
              x by
          rfl]
        rw [EncodedBit.controlledSwapStep_get_control
          control
          (word.bit (EncodedBit.Word.adjacentLeftIndex width i))
          (word.bit (EncodedBit.Word.adjacentRightIndex width i))
          (hcontrol (EncodedBit.Word.adjacentLeftIndex width i))
          (hcontrol (EncodedBit.Word.adjacentRightIndex width i))
          (hword (EncodedBit.Word.adjacentLeftIndex width i)
            (EncodedBit.Word.adjacentRightIndex width i)
            (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex width i))]
        exact hcontrolTrue
      calc
        EncodedBit.GateSpec.stepList
            (rest.flatMap
              (EncodedBit.Word.controlledAdjacentSwapGates control word
                hcontrol hword))
            (EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates control word
                hcontrol hword i) x) =
          EncodedBit.GateSpec.stepList
            (rest.flatMap (EncodedBit.Word.adjacentSwapGates word hword))
            (EncodedBit.GateSpec.stepList
              (EncodedBit.Word.controlledAdjacentSwapGates control word
                hcontrol hword i) x) := by
            exact ih _ hcontrolAfter
        _ =
          EncodedBit.GateSpec.stepList
            (rest.flatMap (EncodedBit.Word.adjacentSwapGates word hword))
            (EncodedBit.GateSpec.stepList
              (EncodedBit.Word.adjacentSwapGates word hword i) x) := by
            rw [hhead]

lemma controlledAdjacentShiftLeftStep_eq_adjacentShiftLeftStep_of_control_true
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data)
    (hcontrolTrue : control.get x = true) :
    EncodedBit.Word.controlledAdjacentShiftLeftStep control word hcontrol
        hword x =
      EncodedBit.Word.adjacentShiftLeftStep word hword x := by
  unfold EncodedBit.Word.controlledAdjacentShiftLeftStep
    EncodedBit.Word.controlledAdjacentShiftLeftGates
    EncodedBit.Word.adjacentShiftLeftStep
    EncodedBit.Word.adjacentShiftLeftGates
  exact
    controlledAdjacentSwapIndexListStep_eq_adjacentSwapIndexListStep_of_control_true
      control word hcontrol hword (List.ofFn fun i : Fin (width - 1) => i) x
      hcontrolTrue

lemma controlledAdjacentShiftRightStep_eq_adjacentShiftRightStep_of_control_true
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data)
    (hcontrolTrue : control.get x = true) :
    EncodedBit.Word.controlledAdjacentShiftRightStep control word hcontrol
        hword x =
      EncodedBit.Word.adjacentShiftRightStep word hword x := by
  have hcontrolAfterRight :
      control.get
          (EncodedBit.Word.controlledAdjacentShiftRightStep control word
            hcontrol hword x) =
        true := by
    rw [controlledAdjacentShiftRightStep_get_observed_of_word_ne
      control control word hcontrol hword
      (fun i => Ne.symm (hcontrol i)) x]
    exact hcontrolTrue
  have hleftEq :=
    controlledAdjacentShiftLeftStep_eq_adjacentShiftLeftStep_of_control_true
      control word hcontrol hword
      (EncodedBit.Word.controlledAdjacentShiftRightStep control word hcontrol
        hword x)
      hcontrolAfterRight
  have hcontrolledInv :=
    EncodedBit.Word.controlledAdjacentShiftLeftStep_controlledAdjacentShiftRightStep
      control word hcontrol hword x
  have hleftControlled :
      EncodedBit.Word.adjacentShiftLeftStep word hword
          (EncodedBit.Word.controlledAdjacentShiftRightStep control word
            hcontrol hword x) =
        x := by
    rw [← hleftEq]
    exact hcontrolledInv
  calc
    EncodedBit.Word.controlledAdjacentShiftRightStep control word hcontrol
        hword x =
      EncodedBit.Word.adjacentShiftRightStep word hword
        (EncodedBit.Word.adjacentShiftLeftStep word hword
          (EncodedBit.Word.controlledAdjacentShiftRightStep control word
            hcontrol hword x)) := by
        rw [EncodedBit.Word.adjacentShiftRightStep_adjacentShiftLeftStep]
    _ = EncodedBit.Word.adjacentShiftRightStep word hword x := by
        rw [hleftControlled]

lemma controlledAdjacentShiftLeftStep_eq_of_control_get_eq
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (controlA controlB : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrolA : ∀ i, controlA.wire ≠ (word.bit i).wire)
    (hcontrolB : ∀ i, controlB.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data)
    (hcontrols : controlA.get x = controlB.get x) :
    EncodedBit.Word.controlledAdjacentShiftLeftStep
        controlA word hcontrolA hword x =
      EncodedBit.Word.controlledAdjacentShiftLeftStep
        controlB word hcontrolB hword x := by
  unfold EncodedBit.Word.controlledAdjacentShiftLeftStep
    EncodedBit.Word.controlledAdjacentShiftLeftGates
  exact controlledAdjacentSwapIndexListStep_eq_of_control_get_eq
    controlA controlB word hcontrolA hcontrolB hword
    (List.ofFn fun i : Fin (width - 1) => i) x hcontrols

private lemma controlledAdjacentSwapGates_reverse
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    (EncodedBit.Word.controlledAdjacentSwapGates control word hcontrol hword
      i).reverse =
      EncodedBit.Word.controlledAdjacentSwapGates control word hcontrol hword
        i := by
  simp [EncodedBit.Word.controlledAdjacentSwapGates,
    EncodedBit.controlledSwapGates]

lemma controlledAdjacentShiftRightStep_eq_of_control_get_eq
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (controlA controlB : EncodedBit encoding)
    (word : EncodedBit.Word encoding width)
    (hcontrolA : ∀ i, controlA.wire ≠ (word.bit i).wire)
    (hcontrolB : ∀ i, controlB.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data)
    (hcontrols : controlA.get x = controlB.get x) :
    EncodedBit.Word.controlledAdjacentShiftRightStep
        controlA word hcontrolA hword x =
      EncodedBit.Word.controlledAdjacentShiftRightStep
        controlB word hcontrolB hword x := by
  unfold EncodedBit.Word.controlledAdjacentShiftRightStep
    EncodedBit.Word.controlledAdjacentShiftRightGates
    EncodedBit.Word.controlledAdjacentShiftLeftGates
  rw [List.reverse_flatMap, List.reverse_flatMap]
  have hfunA :
      List.reverse ∘
          EncodedBit.Word.controlledAdjacentSwapGates controlA word hcontrolA
            hword =
        EncodedBit.Word.controlledAdjacentSwapGates controlA word hcontrolA
          hword := by
    funext i
    exact controlledAdjacentSwapGates_reverse controlA word hcontrolA hword i
  have hfunB :
      List.reverse ∘
          EncodedBit.Word.controlledAdjacentSwapGates controlB word hcontrolB
            hword =
        EncodedBit.Word.controlledAdjacentSwapGates controlB word hcontrolB
          hword := by
    funext i
    exact controlledAdjacentSwapGates_reverse controlB word hcontrolB hword i
  rw [hfunA, hfunB]
  exact controlledAdjacentSwapIndexListStep_eq_of_control_get_eq
    controlA controlB word hcontrolA hcontrolB hword
    (List.ofFn fun i : Fin (width - 1) => i).reverse x hcontrols

/-! ## Compact coefficient addition -/

namespace Compact

/-- Little-endian `r` coefficient bit in the compact carrier. -/
def rCoeffValueBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (encoding n counterWidth) :=
  liftCoreBit n counterWidth
    (RegisterBits.rCoeffValueBit n counterWidth bit)

/-- Little-endian `s` coefficient bit in the compact carrier. -/
def sCoeffValueBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (encoding n counterWidth) :=
  liftCoreBit n counterWidth
    (RegisterBits.sCoeffValueBit n counterWidth bit)

/-- Little-endian `r` coefficient word in the compact carrier. -/
def rCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) (n + 1) where
  bit := rCoeffValueBit n counterWidth

/-- Little-endian `s` coefficient word in the compact carrier. -/
def sCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) (n + 1) where
  bit := sCoeffValueBit n counterWidth

@[simp] lemma rCoeffValueBit_get (n counterWidth : Nat)
    (bit : Fin (n + 1)) (x : Registers n counterWidth) :
    (rCoeffValueBit n counterWidth bit).get x =
      x.core.rCoeff.val.testBit bit.val := by
  simp [rCoeffValueBit]

@[simp] lemma sCoeffValueBit_get (n counterWidth : Nat)
    (bit : Fin (n + 1)) (x : Registers n counterWidth) :
    (sCoeffValueBit n counterWidth bit).get x =
      x.core.sCoeff.val.testBit bit.val := by
  simp [sCoeffValueBit]

/-- A compact carrier with the whole reusable shared workspace clean. -/
def coefficientAddCleanInput (n counterWidth : Nat)
    (core : MK.Registers n counterWidth) (target : Word n) :
    Registers n counterWidth where
  core := core
  shared := cleanSharedWork n counterWidth
  target := target

lemma coefficientCarryInBit_get_coefficientAddCleanInput
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientCarryInBit n counterWidth).get
        (coefficientAddCleanInput n counterWidth core target) = false := by
  simp [coefficientAddCleanInput, cleanSharedWork, cleanCoeffAdderWork]

lemma coefficientCarryWorkBit_get_coefficientAddCleanInput
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (bit : Fin n) :
    (coefficientCarryWorkBit n counterWidth bit).get
        (coefficientAddCleanInput n counterWidth core target) = false := by
  change (BinaryLabelEncoding.finIdentityBit n bit).get
      (PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1)) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit

/-- Compact VBE layout for adding the `r` coefficient into the `s`
coefficient.  It borrows the one shared carry-in/bank owned by the compact
carrier. -/
def coefficientAddRIntoSLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1) where
  left := rCoeffValueWord n counterWidth
  right := sCoeffValueWord n counterWidth
  carryIn := coefficientCarryInBit n counterWidth
  workCarry := coefficientCarryWorkWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact liftCoreBit_wire_ne n counterWidth
      (rCoeff_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  rightRight_ne := by
    intro i j hij
    exact liftCoreBit_wire_ne n counterWidth
      (sCoeff_sCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  leftRight_ne := by
    intro i j
    exact liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire j)
        (WireAddress.littleEndianWire i)))
  leftCarryIn_ne := by
    intro i
    simpa [rCoeffValueWord, rCoeffValueBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth i)
  rightCarryIn_ne := by
    intro i
    simpa [sCoeffValueWord, sCoeffValueBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.sCoeffValueBit n counterWidth i)
  leftWork_ne := by
    intro i j
    simpa [rCoeffValueWord, rCoeffValueBit, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth i) j
  rightWork_ne := by
    intro i j
    simpa [sCoeffValueWord, sCoeffValueBit, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.sCoeffValueBit n counterWidth i) j
  carryInWork_ne := by
    intro j
    exact coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
      n counterWidth j
  workWork_ne := by
    intro i j hij
    exact coefficientCarryWorkBit_wire_ne n counterWidth hij

/-- Compact VBE layout for adding the `s` coefficient into the `r`
coefficient. -/
def coefficientAddSIntoRLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1) where
  left := sCoeffValueWord n counterWidth
  right := rCoeffValueWord n counterWidth
  carryIn := coefficientCarryInBit n counterWidth
  workCarry := coefficientCarryWorkWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    exact liftCoreBit_wire_ne n counterWidth
      (sCoeff_sCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  rightRight_ne := by
    intro i j hij
    exact liftCoreBit_wire_ne n counterWidth
      (rCoeff_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  leftRight_ne := by
    intro i j
    exact liftCoreBit_wire_ne n counterWidth
      (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j))
  leftCarryIn_ne := by
    intro i
    simpa [sCoeffValueWord, sCoeffValueBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.sCoeffValueBit n counterWidth i)
  rightCarryIn_ne := by
    intro i
    simpa [rCoeffValueWord, rCoeffValueBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth i)
  leftWork_ne := by
    intro i j
    simpa [sCoeffValueWord, sCoeffValueBit, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.sCoeffValueBit n counterWidth i) j
  rightWork_ne := by
    intro i j
    simpa [rCoeffValueWord, rCoeffValueBit, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth i) j
  carryInWork_ne := by
    intro j
    exact coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
      n counterWidth j
  workWork_ne := by
    intro i j hij
    exact coefficientCarryWorkBit_wire_ne n counterWidth hij

/-- Actual compact gate list for adding `r` into `s`. -/
def coefficientAddRIntoSGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (coefficientAddRIntoSLayout n counterWidth)

/-- Actual compact gate list for adding `s` into `r`. -/
def coefficientAddSIntoRGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (coefficientAddSIntoRLayout n counterWidth)

/-- The compact `r`-into-`s` adder contains no X gates. -/
lemma coefficientAddRIntoSGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((coefficientAddRIntoSGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [coefficientAddRIntoSGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
      (coefficientAddRIntoSLayout n counterWidth))

/-- The compact `r`-into-`s` adder has the exact CNOT coordinate. -/
lemma coefficientAddRIntoSGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddRIntoSGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (n + 1) := by
  simpa only [coefficientAddRIntoSGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
      (coefficientAddRIntoSLayout n counterWidth))

/-- The compact `r`-into-`s` adder has the exact Toffoli coordinate. -/
lemma coefficientAddRIntoSGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddRIntoSGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  simpa only [coefficientAddRIntoSGates, Nat.add_sub_cancel] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
      (coefficientAddRIntoSLayout n counterWidth))

/-- The compact `r`-into-`s` schedule has exact physical length. -/
lemma coefficientAddRIntoSGates_length (n counterWidth : Nat) :
    (coefficientAddRIntoSGates n counterWidth).length = 8 * n + 2 := by
  simp only [coefficientAddRIntoSGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length]
  omega

/-- The compact `s`-into-`r` adder contains no X gates. -/
lemma coefficientAddSIntoRGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((coefficientAddSIntoRGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [coefficientAddSIntoRGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
      (coefficientAddSIntoRLayout n counterWidth))

/-- The compact `s`-into-`r` adder has the exact CNOT coordinate. -/
lemma coefficientAddSIntoRGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddSIntoRGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (n + 1) := by
  simpa only [coefficientAddSIntoRGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
      (coefficientAddSIntoRLayout n counterWidth))

/-- The compact `s`-into-`r` adder has the exact Toffoli coordinate. -/
lemma coefficientAddSIntoRGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coefficientAddSIntoRGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  simpa only [coefficientAddSIntoRGates, Nat.add_sub_cancel] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
      (coefficientAddSIntoRLayout n counterWidth))

/-- The compact `s`-into-`r` schedule has exact physical length. -/
lemma coefficientAddSIntoRGates_length (n counterWidth : Nat) :
    (coefficientAddSIntoRGates n counterWidth).length = 8 * n + 2 := by
  simp only [coefficientAddSIntoRGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length]
  omega

/-- Compiled compact program for adding `r` into `s`. -/
def coefficientAddRIntoSProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram
    (coefficientAddRIntoSLayout n counterWidth)

/-- Compiled compact program for adding `s` into `r`. -/
def coefficientAddSIntoRProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram
    (coefficientAddSIntoRLayout n counterWidth)

/-- Folded compact step for adding `r` into `s`. -/
def coefficientAddRIntoSStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
    (coefficientAddRIntoSLayout n counterWidth)

/-- Folded compact step for adding `s` into `r`. -/
def coefficientAddSIntoRStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
    (coefficientAddSIntoRLayout n counterWidth)

/-- The compact `r`-into-`s` program realizes its actual gate-list step. -/
lemma coefficientAddRIntoS_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (coefficientAddRIntoSProgram n counterWidth) environment
      (coefficientAddRIntoSStep n counterWidth) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes
    (coefficientAddRIntoSLayout n counterWidth)

/-- The compact `s`-into-`r` program realizes its actual gate-list step. -/
lemma coefficientAddSIntoR_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (coefficientAddSIntoRProgram n counterWidth) environment
      (coefficientAddSIntoRStep n counterWidth) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes
    (coefficientAddSIntoRLayout n counterWidth)

/-- The compiled compact `r`-into-`s` program retains its exact X count. -/
lemma coefficientAddRIntoSProgram_x_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (coefficientAddRIntoSProgram n counterWidth).eventCost = 0 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coefficientAddRIntoSGates n counterWidth)).eventCost = 0
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    coefficientAddRIntoSGates_xMultiplicity_sum]

/-- The compiled compact `r`-into-`s` program retains its exact CNOT count. -/
lemma coefficientAddRIntoSProgram_cnot_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (coefficientAddRIntoSProgram n counterWidth).eventCost =
      2 * (n + 1) := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coefficientAddRIntoSGates n counterWidth)).eventCost = 2 * (n + 1)
  rw [EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    coefficientAddRIntoSGates_cnotMultiplicity_sum]

/-- The compiled compact `r`-into-`s` program retains its exact Toffoli count. -/
lemma coefficientAddRIntoSProgram_toffoli_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (coefficientAddRIntoSProgram n counterWidth).eventCost = 6 * n := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coefficientAddRIntoSGates n counterWidth)).eventCost = 6 * n
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    coefficientAddRIntoSGates_toffoliMultiplicity_sum]

/-- The compiled compact `s`-into-`r` program retains its exact X count. -/
lemma coefficientAddSIntoRProgram_x_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (coefficientAddSIntoRProgram n counterWidth).eventCost = 0 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coefficientAddSIntoRGates n counterWidth)).eventCost = 0
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    coefficientAddSIntoRGates_xMultiplicity_sum]

/-- The compiled compact `s`-into-`r` program retains its exact CNOT count. -/
lemma coefficientAddSIntoRProgram_cnot_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (coefficientAddSIntoRProgram n counterWidth).eventCost =
      2 * (n + 1) := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coefficientAddSIntoRGates n counterWidth)).eventCost = 2 * (n + 1)
  rw [EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    coefficientAddSIntoRGates_cnotMultiplicity_sum]

/-- The compiled compact `s`-into-`r` program retains its exact Toffoli count. -/
lemma coefficientAddSIntoRProgram_toffoli_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (coefficientAddSIntoRProgram n counterWidth).eventCost = 6 * n := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coefficientAddSIntoRGates n counterWidth)).eventCost = 6 * n
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    coefficientAddSIntoRGates_toffoliMultiplicity_sum]

/-! ### Shared clean-adder reasoning -/

/-- The generic clean-carry schedule preserves any observation outside its
right/target word and borrowed carry bank. -/
private lemma coefficientAddStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (observed : EncodedBit (encoding n counterWidth))
    (hright : ∀ bit : Fin (n + 1),
      (layout.right.bit bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin n,
      (layout.workCarry.bit bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
      observed.get x := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      layout observed hright hwork x
  simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- On clean borrowed carry work, an arbitrary compact coefficient layout
computes the natural carry propagated from its specified left and right words. -/
private lemma coefficientAdd_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (left right : Word (n + 1)) (j : Fin n)
    (x : Registers n counterWidth)
    (hleft : ∀ bit : Fin (n + 1),
      (layout.left.bit bit).get x = left.val.testBit bit.val)
    (hright : ∀ bit : Fin (n + 1),
      (layout.right.bit bit).get x = right.val.testBit bit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ bit : Fin n, (layout.workCarry.bit bit).get x = false) :
    (layout.workCarry.bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left.val right.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x
  change (layout.workCarry.bit j).get stage =
    Nat.BinaryArithmetic.natAddCarry left.val right.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin n, j.val = m ->
      (layout.workCarry.bit j).get stage =
        Nat.BinaryArithmetic.natAddCarry left.val right.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            layout j x hwork
        change (layout.workCarry.bit j).get stage =
          Nat.BinaryArithmetic.natAddCarry left.val right.val (j.val + 1)
        change
          (layout.workCarry.bit j).get
              (layout.carryStageIndexStep x) =
            Nat.BinaryArithmetic.natAddCarry
              left.val right.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              layout x
          rw [hdata]
          change Bool.carry
              ((layout.left.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              ((layout.right.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              (layout.carryIn.get x) =
            Nat.BinaryArithmetic.natAddCarry
              left.val right.val (j.val + 1)
          rw [hleft, hright, hcarry]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let previous :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex
              (n := n + 1) j hzero
          have hpreviousLt : previous.val < m := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hprevious := ih previous.val hpreviousLt previous rfl
          have hprevious' :
              (layout.workCarry.bit previous).get
                  (layout.carryStageIndexStep x) =
                Nat.BinaryArithmetic.natAddCarry
                  left.val right.val (previous.val + 1) := by
            simpa only [stage] using hprevious
          have hpreviousSucc : previous.val + 1 = j.val := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hprevious', hpreviousSucc]
          change Bool.carry
              ((layout.left.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              ((layout.right.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex j)).get x)
              (Nat.BinaryArithmetic.natAddCarry left.val right.val j.val) =
            Bool.carry
              (left.val.testBit j.val) (right.val.testBit j.val)
              (Nat.BinaryArithmetic.natAddCarry left.val right.val j.val)
          rw [hleft, hright]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex]
  exact hmain j.val j rfl

/-- The carry selected before an arbitrary compact coefficient target bit is
the natural addition carry when the borrowed bank is clean. -/
private lemma coefficientAdd_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (left right : Word (n + 1)) (bit : Fin (n + 1))
    (x : Registers n counterWidth)
    (hleft : ∀ leftBit : Fin (n + 1),
      (layout.left.bit leftBit).get x = left.val.testBit leftBit.val)
    (hright : ∀ rightBit : Fin (n + 1),
      (layout.right.bit rightBit).get x = right.val.testBit rightBit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ workBit : Fin n,
      (layout.workCarry.bit workBit).get x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum layout bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left.val right.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        layout x
    rw [hdata]
    simp [hcarry, Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hworkLt : bit.val - 1 < n := by
      have hbit := bit.isLt
      omega
    let workBit : Fin n := ⟨bit.val - 1, hworkLt⟩
    have hworkCarry :=
      coefficientAdd_carryStage_get_workCarry_natAddCarry
        n counterWidth layout left right workBit x
        hleft hright hcarry hwork
    have hworkSucc : workBit.val + 1 = bit.val := by
      dsimp [workBit]
      omega
    change (layout.workCarry.bit workBit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left.val right.val bit.val
    rw [hworkCarry, hworkSucc]

/-- The generic compact VBE step writes its right word as its old right word
plus its preserved left word on clean carry input. -/
private lemma coefficientAdd_cleanStep_get_right_add_testBit_of_clean
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (left right : Word (n + 1)) (bit : Fin (n + 1))
    (x : Registers n counterWidth)
    (hleft : ∀ leftBit : Fin (n + 1),
      (layout.left.bit leftBit).get x = left.val.testBit leftBit.val)
    (hright : ∀ rightBit : Fin (n + 1),
      (layout.right.bit rightBit).get x = right.val.testBit rightBit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ workBit : Fin n,
      (layout.workCarry.bit workBit).get x = false) :
    (layout.right.bit bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
      (right + left).val.testBit bit.val := by
  have hrightStep :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      layout bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hrightStep
  have hcarryBit :=
    coefficientAdd_carryBeforeSum_get_natAddCarry
      n counterWidth layout left right bit x hleft hright hcarry hwork
  rw [hcarryBit] at hrightStep
  have hadd :=
    (word_add_testBit_eq_xor3 (n + 1) left right bit).symm
  calc
    (layout.right.bit bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
        ((right.val.testBit bit.val ^^ left.val.testBit bit.val) ^^
          Nat.BinaryArithmetic.natAddCarry left.val right.val bit.val) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        hleft, hright, Bool.xor_assoc] using hrightStep
    _ = (right + left).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using hadd

/-- The compact `r`-into-`s` step preserves every observation disjoint from
the `s` target word and the borrowed VBE carry bank. -/
lemma coefficientAddRIntoSStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hright : ∀ bit : Fin (n + 1),
      (sCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (coefficientAddRIntoSStep n counterWidth x) =
      observed.get x := by
  have h := coefficientAddStep_get_observed_of_right_work_ne
    n counterWidth (coefficientAddRIntoSLayout n counterWidth) observed
    (by
      intro bit
      simpa [coefficientAddRIntoSLayout, sCoeffValueWord] using hright bit)
    (by
      intro bit
      simpa [coefficientAddRIntoSLayout, coefficientCarryWorkWord]
        using hwork bit)
    x
  simpa [coefficientAddRIntoSStep] using h

/-- The compact `s`-into-`r` step preserves every observation disjoint from
the `r` target word and the borrowed VBE carry bank. -/
lemma coefficientAddSIntoRStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hright : ∀ bit : Fin (n + 1),
      (rCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (coefficientAddSIntoRStep n counterWidth x) =
      observed.get x := by
  have h := coefficientAddStep_get_observed_of_right_work_ne
    n counterWidth (coefficientAddSIntoRLayout n counterWidth) observed
    (by
      intro bit
      simpa [coefficientAddSIntoRLayout, rCoeffValueWord] using hright bit)
    (by
      intro bit
      simpa [coefficientAddSIntoRLayout, coefficientCarryWorkWord]
        using hwork bit)
    x
  simpa [coefficientAddSIntoRStep] using h

/-- The `r` source coefficient is preserved by the compact `r`-into-`s`
adder. -/
lemma coefficientAddRIntoSStep_get_rCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (rCoeffValueBit n counterWidth bit).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (rCoeffValueBit n counterWidth bit).get x := by
  have h := PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
    (coefficientAddRIntoSLayout n counterWidth) bit x
  simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
    rCoeffValueWord, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep]
    using h

/-- The `s` source coefficient is preserved by the compact `s`-into-`r`
adder. -/
lemma coefficientAddSIntoRStep_get_sCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (sCoeffValueBit n counterWidth bit).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (sCoeffValueBit n counterWidth bit).get x := by
  have h := PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
    (coefficientAddSIntoRLayout n counterWidth) bit x
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    sCoeffValueWord, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep]
    using h

/-- On a clean compact workspace, `r` is added into `s` bitwise modulo
`2^(n+1)`. -/
lemma coefficientAddRIntoSStep_get_sCoeff_add_testBit_of_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (bit : Fin (n + 1)) :
    (coefficientAddRIntoSStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.sCoeff.val.testBit
        bit.val =
      (core.sCoeff + core.rCoeff).val.testBit bit.val := by
  let input := coefficientAddCleanInput n counterWidth core target
  have h := coefficientAdd_cleanStep_get_right_add_testBit_of_clean
    n counterWidth (coefficientAddRIntoSLayout n counterWidth)
    core.rCoeff core.sCoeff bit input
    (by
      intro leftBit
      change (rCoeffValueBit n counterWidth leftBit).get input =
        core.rCoeff.val.testBit leftBit.val
      simp only [rCoeffValueBit_get, input, coefficientAddCleanInput])
    (by
      intro rightBit
      change (sCoeffValueBit n counterWidth rightBit).get input =
        core.sCoeff.val.testBit rightBit.val
      simp only [sCoeffValueBit_get, input, coefficientAddCleanInput])
    (by
      change (coefficientCarryInBit n counterWidth).get input = false
      simpa only [input] using
        coefficientCarryInBit_get_coefficientAddCleanInput
          n counterWidth core target)
    (by
      intro workBit
      change (coefficientCarryWorkBit n counterWidth workBit).get input = false
      simpa only [input] using
        coefficientCarryWorkBit_get_coefficientAddCleanInput
          n counterWidth core target workBit)
  calc
    (coefficientAddRIntoSStep n counterWidth input).core.sCoeff.val.testBit
        bit.val =
        (sCoeffValueBit n counterWidth bit).get
          (coefficientAddRIntoSStep n counterWidth input) := by
      symm
      exact sCoeffValueBit_get n counterWidth bit
        (coefficientAddRIntoSStep n counterWidth input)
    _ = (core.sCoeff + core.rCoeff).val.testBit bit.val := by
      simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
        sCoeffValueWord] using h

/-- On a clean compact workspace, `s` is added into `r` bitwise modulo
`2^(n+1)`. -/
lemma coefficientAddSIntoRStep_get_rCoeff_add_testBit_of_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (bit : Fin (n + 1)) :
    (coefficientAddSIntoRStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.rCoeff.val.testBit
        bit.val =
      (core.rCoeff + core.sCoeff).val.testBit bit.val := by
  let input := coefficientAddCleanInput n counterWidth core target
  have h := coefficientAdd_cleanStep_get_right_add_testBit_of_clean
    n counterWidth (coefficientAddSIntoRLayout n counterWidth)
    core.sCoeff core.rCoeff bit input
    (by
      intro leftBit
      change (sCoeffValueBit n counterWidth leftBit).get input =
        core.sCoeff.val.testBit leftBit.val
      simp only [sCoeffValueBit_get, input, coefficientAddCleanInput])
    (by
      intro rightBit
      change (rCoeffValueBit n counterWidth rightBit).get input =
        core.rCoeff.val.testBit rightBit.val
      simp only [rCoeffValueBit_get, input, coefficientAddCleanInput])
    (by
      change (coefficientCarryInBit n counterWidth).get input = false
      simpa only [input] using
        coefficientCarryInBit_get_coefficientAddCleanInput
          n counterWidth core target)
    (by
      intro workBit
      change (coefficientCarryWorkBit n counterWidth workBit).get input = false
      simpa only [input] using
        coefficientCarryWorkBit_get_coefficientAddCleanInput
          n counterWidth core target workBit)
  calc
    (coefficientAddSIntoRStep n counterWidth input).core.rCoeff.val.testBit
        bit.val =
        (rCoeffValueBit n counterWidth bit).get
          (coefficientAddSIntoRStep n counterWidth input) := by
      symm
      exact rCoeffValueBit_get n counterWidth bit
        (coefficientAddSIntoRStep n counterWidth input)
    _ = (core.rCoeff + core.sCoeff).val.testBit bit.val := by
      simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
        rCoeffValueWord] using h

/-- Word-level clean endpoint for compact `r`-into-`s` coefficient addition. -/
lemma coefficientAddRIntoSStep_sCoeff_of_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddRIntoSStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.sCoeff =
      core.sCoeff + core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  exact coefficientAddRIntoSStep_get_sCoeff_add_testBit_of_clean
    n counterWidth core target bit

/-- Word-level clean endpoint for compact `s`-into-`r` coefficient addition. -/
lemma coefficientAddSIntoRStep_rCoeff_of_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddSIntoRStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.rCoeff =
      core.rCoeff + core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  exact coefficientAddSIntoRStep_get_rCoeff_add_testBit_of_clean
    n counterWidth core target bit

/-- The source word remains unchanged at the compact `r`-into-`s` endpoint. -/
lemma coefficientAddRIntoSStep_rCoeff_of_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddRIntoSStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.rCoeff =
      core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  let input := coefficientAddCleanInput n counterWidth core target
  calc
    (coefficientAddRIntoSStep n counterWidth input).core.rCoeff.val.testBit
        bit.val =
        (rCoeffValueBit n counterWidth bit).get
          (coefficientAddRIntoSStep n counterWidth input) := by
      symm
      exact rCoeffValueBit_get n counterWidth bit
        (coefficientAddRIntoSStep n counterWidth input)
    _ = (rCoeffValueBit n counterWidth bit).get input :=
      coefficientAddRIntoSStep_get_rCoeffValueBit n counterWidth bit input
    _ = core.rCoeff.val.testBit bit.val :=
      rCoeffValueBit_get n counterWidth bit input

/-- The source word remains unchanged at the compact `s`-into-`r` endpoint. -/
lemma coefficientAddSIntoRStep_sCoeff_of_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddSIntoRStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.sCoeff =
      core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  let input := coefficientAddCleanInput n counterWidth core target
  calc
    (coefficientAddSIntoRStep n counterWidth input).core.sCoeff.val.testBit
        bit.val =
        (sCoeffValueBit n counterWidth bit).get
          (coefficientAddSIntoRStep n counterWidth input) := by
      symm
      exact sCoeffValueBit_get n counterWidth bit
        (coefficientAddSIntoRStep n counterWidth input)
    _ = (sCoeffValueBit n counterWidth bit).get input :=
      coefficientAddSIntoRStep_get_sCoeffValueBit n counterWidth bit input
    _ = core.sCoeff.val.testBit bit.val :=
      sCoeffValueBit_get n counterWidth bit input

/-- The generic compact clean-carry step restores the whole VBE carry object
when its carry-in and work lenses are the shared compact bank. -/
private lemma coefficientAddStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (core : MK.Registers n counterWidth) (target : Word n)
    (hcarryIn : layout.carryIn = coefficientCarryInBit n counterWidth)
    (hworkCarry : ∀ bit : Fin n,
      layout.workCarry.bit bit = coefficientCarryWorkBit n counterWidth bit) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
      (coefficientAddCleanInput n counterWidth core target)).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  change (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
      (coefficientAddCleanInput n counterWidth core target)).shared.coefficientAdder =
      (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1))
  apply Prod.ext
  · have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
        layout (coefficientAddCleanInput n counterWidth core target)
    have hcarry :
        (coefficientCarryInBit n counterWidth).get
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
              (coefficientAddCleanInput n counterWidth core target)) = false := by
      rw [← hcarryIn]
      calc
        layout.carryIn.get
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
              (coefficientAddCleanInput n counterWidth core target)) =
            layout.carryIn.get
              (coefficientAddCleanInput n counterWidth core target) := by
          simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep]
            using hdata
        _ = false := by
          rw [hcarryIn]
          exact coefficientCarryInBit_get_coefficientAddCleanInput
            n counterWidth core target
    simpa only [coefficientCarryInBit_get] using hcarry
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    change (coefficientCarryWorkBit n counterWidth bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
          (coefficientAddCleanInput n counterWidth core target)) = false
    rw [← hworkCarry bit]
    have hwork :=
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
        layout bit (coefficientAddCleanInput n counterWidth core target) (by
          intro workBit
          rw [hworkCarry workBit]
          exact coefficientCarryWorkBit_get_coefficientAddCleanInput
            n counterWidth core target workBit)
    simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using hwork

/-- A compact coefficient addition restores an arbitrary initially clean VBE
carry object.  This form is used after routing has changed other shared fields
without changing the reusable carry bank. -/
private lemma coefficientAddStep_coefficientAdder_cleanEndpoint_of_clean
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (x : Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false)
    (hcarryIn : layout.carryIn = coefficientCarryInBit n counterWidth)
    (hworkCarry : ∀ bit : Fin n,
      layout.workCarry.bit bit = coefficientCarryWorkBit n counterWidth bit) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
      x).shared.coefficientAdder = cleanCoeffAdderWork n := by
  change (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
      x).shared.coefficientAdder =
      (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1))
  apply Prod.ext
  · have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
        layout x
    have hcarryOut :
        (coefficientCarryInBit n counterWidth).get
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
          false := by
      rw [← hcarryIn]
      calc
        layout.carryIn.get
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
            layout.carryIn.get x := by
          simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep]
            using hdata
        _ = false := by rw [hcarryIn]; exact hcarry
    simpa only [coefficientCarryInBit_get] using hcarryOut
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    change (coefficientCarryWorkBit n counterWidth bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) = false
    rw [← hworkCarry bit]
    have hclean :=
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
        layout bit x (by
          intro workBit
          rw [hworkCarry workBit]
          exact hwork workBit)
    simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using hclean

/-- The generic compact clean-carry step returns the complete named shared
workspace to its clean value once its target word is disjoint from the three
non-VBE shared fields. -/
private lemma coefficientAddStep_shared_cleanEndpoint
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (core : MK.Registers n counterWidth) (target : Word n)
    (hcarryIn : layout.carryIn = coefficientCarryInBit n counterWidth)
    (hworkCarry : ∀ bit : Fin n,
      layout.workCarry.bit bit = coefficientCarryWorkBit n counterWidth bit)
    (hcorrection : ∀ rightBit : Fin (n + 1),
      ∀ correctionBit : Fin (counterWidth - 1),
      (layout.right.bit rightBit).wire ≠
        (correctionCounterValueBit n counterWidth correctionBit).wire)
    (hpath : ∀ rightBit : Fin (n + 1),
      (layout.right.bit rightBit).wire ≠ (pathBit n counterWidth).wire)
    (hcontrol : ∀ rightBit : Fin (n + 1),
      (layout.right.bit rightBit).wire ≠ (controlBit n counterWidth).wire) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
      (coefficientAddCleanInput n counterWidth core target)).shared =
      cleanSharedWork n counterWidth := by
  apply (sharedWorkTupleEquiv n counterWidth).injective
  change
    ((PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
      (coefficientAddCleanInput n counterWidth core target)).shared.coefficientAdder,
      ((PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
        (coefficientAddCleanInput n counterWidth core target)).shared.correctionCounter,
        ((PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
          (coefficientAddCleanInput n counterWidth core target)).shared.path,
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
            (coefficientAddCleanInput n counterWidth core target)).shared.control))) =
      (cleanCoeffAdderWork n, (0, (false, false)))
  apply Prod.ext
  · exact coefficientAddStep_coefficientAdder_cleanEndpoint
      n counterWidth layout core target hcarryIn hworkCarry
  · apply Prod.ext
    · apply word_eq_of_testBit_eq
      intro correctionBit
      have h := coefficientAddStep_get_observed_of_right_work_ne
        n counterWidth layout
        (correctionCounterValueBit n counterWidth correctionBit)
        (fun rightBit => hcorrection rightBit correctionBit)
        (by
          intro workBit
          rw [hworkCarry workBit]
          simpa only [correctionCounterValueBit] using
            Ne.symm
              (correctionCounterBit_coefficientCarryWorkBit_wire_ne
                n counterWidth
                (WireAddress.littleEndianWire correctionBit) workBit))
        (coefficientAddCleanInput n counterWidth core target)
      simpa only [correctionCounterValueBit_get, coefficientAddCleanInput,
        cleanSharedWork] using h
    · apply Prod.ext
      · have h := coefficientAddStep_get_observed_of_right_work_ne
          n counterWidth layout (pathBit n counterWidth) hpath
          (by
            intro workBit
            rw [hworkCarry workBit]
            exact Ne.symm
              (pathBit_coefficientCarryWorkBit_wire_ne
                n counterWidth workBit))
          (coefficientAddCleanInput n counterWidth core target)
        simpa only [pathBit_get, coefficientAddCleanInput, cleanSharedWork]
          using h
      · have h := coefficientAddStep_get_observed_of_right_work_ne
          n counterWidth layout (controlBit n counterWidth) hcontrol
          (by
            intro workBit
            rw [hworkCarry workBit]
            exact Ne.symm
              (controlBit_coefficientCarryWorkBit_wire_ne
                n counterWidth workBit))
          (coefficientAddCleanInput n counterWidth core target)
        simpa only [controlBit_get, coefficientAddCleanInput, cleanSharedWork]
          using h

/-- The generic compact clean-carry step leaves the public target word
unchanged when its target and work wires are disjoint from it. -/
private lemma coefficientAddStep_target_cleanEndpoint
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) (n + 1))
    (core : MK.Registers n counterWidth) (target : Word n)
    (hworkCarry : ∀ bit : Fin n,
      layout.workCarry.bit bit = coefficientCarryWorkBit n counterWidth bit)
    (hrightTarget : ∀ rightBit : Fin (n + 1), ∀ targetBit : Fin n,
      (layout.right.bit rightBit).wire ≠
        (targetValueBit n counterWidth targetBit).wire) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout
      (coefficientAddCleanInput n counterWidth core target)).target = target := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h := coefficientAddStep_get_observed_of_right_work_ne
    n counterWidth layout (targetValueBit n counterWidth targetBit)
    (fun rightBit => hrightTarget rightBit targetBit)
    (by
      intro workBit
      rw [hworkCarry workBit]
      simpa only [coefficientCarryWorkBit, targetValueBit] using
        liftSharedBit_targetBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth workBit)
          (WireAddress.littleEndianWire targetBit))
    (coefficientAddCleanInput n counterWidth core target)
  simpa only [targetValueBit_get, coefficientAddCleanInput] using h

/-- The `r`-into-`s` compact coefficient addition restores the complete shared
bank, including the carry-in and every VBE carry bit. -/
lemma coefficientAddRIntoSStep_shared_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddRIntoSStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).shared =
      cleanSharedWork n counterWidth := by
  simpa [coefficientAddRIntoSStep] using
    coefficientAddStep_shared_cleanEndpoint n counterWidth
      (coefficientAddRIntoSLayout n counterWidth) core target (by rfl) (by
        intro bit
        rfl)
      (by
        intro rightBit correctionBit
        simpa [coefficientAddRIntoSLayout, sCoeffValueWord,
          sCoeffValueBit, correctionCounterValueBit, correctionCounterBit]
          using liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.sCoeffValueBit n counterWidth rightBit)
            (sharedCorrectionCounterBit n counterWidth
              (WireAddress.littleEndianWire correctionBit)))
      (by
        intro rightBit
        simpa [coefficientAddRIntoSLayout, sCoeffValueWord,
          sCoeffValueBit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.sCoeffValueBit n counterWidth rightBit)
            (sharedPathBit n counterWidth))
      (by
        intro rightBit
        simpa [coefficientAddRIntoSLayout, sCoeffValueWord,
          sCoeffValueBit, controlBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.sCoeffValueBit n counterWidth rightBit)
            (sharedControlBit n counterWidth))

/-- The `s`-into-`r` compact coefficient addition restores the complete shared
bank, including the carry-in and every VBE carry bit. -/
lemma coefficientAddSIntoRStep_shared_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddSIntoRStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).shared =
      cleanSharedWork n counterWidth := by
  simpa [coefficientAddSIntoRStep] using
    coefficientAddStep_shared_cleanEndpoint n counterWidth
      (coefficientAddSIntoRLayout n counterWidth) core target (by rfl) (by
        intro bit
        rfl)
      (by
        intro rightBit correctionBit
        simpa [coefficientAddSIntoRLayout, rCoeffValueWord,
          rCoeffValueBit, correctionCounterValueBit, correctionCounterBit]
          using liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.rCoeffValueBit n counterWidth rightBit)
            (sharedCorrectionCounterBit n counterWidth
              (WireAddress.littleEndianWire correctionBit)))
      (by
        intro rightBit
        simpa [coefficientAddSIntoRLayout, rCoeffValueWord,
          rCoeffValueBit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.rCoeffValueBit n counterWidth rightBit)
            (sharedPathBit n counterWidth))
      (by
        intro rightBit
        simpa [coefficientAddSIntoRLayout, rCoeffValueWord,
          rCoeffValueBit, controlBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.rCoeffValueBit n counterWidth rightBit)
            (sharedControlBit n counterWidth))

/-- The compact `r`-into-`s` addition restores an arbitrary clean reusable
VBE carry bank, independently of the other shared routing fields. -/
lemma coefficientAddRIntoSStep_coefficientAdder_cleanEndpoint_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (coefficientAddRIntoSStep n counterWidth x).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  simpa [coefficientAddRIntoSStep] using
    coefficientAddStep_coefficientAdder_cleanEndpoint_of_clean
      n counterWidth (coefficientAddRIntoSLayout n counterWidth) x
      hcarry hwork (by rfl) (by intro bit; rfl)

/-- The compact `s`-into-`r` addition restores an arbitrary clean reusable
VBE carry bank, independently of the other shared routing fields. -/
lemma coefficientAddSIntoRStep_coefficientAdder_cleanEndpoint_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (coefficientAddSIntoRStep n counterWidth x).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  simpa [coefficientAddSIntoRStep] using
    coefficientAddStep_coefficientAdder_cleanEndpoint_of_clean
      n counterWidth (coefficientAddSIntoRLayout n counterWidth) x
      hcarry hwork (by rfl) (by intro bit; rfl)

/-- The compact `r`-into-`s` coefficient addition leaves the public target
word unchanged. -/
lemma coefficientAddRIntoSStep_target_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddRIntoSStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).target = target := by
  simpa [coefficientAddRIntoSStep] using
    coefficientAddStep_target_cleanEndpoint n counterWidth
      (coefficientAddRIntoSLayout n counterWidth) core target (by
        intro bit
        rfl)
      (by
        intro rightBit targetBit
        simpa [coefficientAddRIntoSLayout, sCoeffValueWord,
          sCoeffValueBit, targetValueBit] using
          liftCoreBit_targetBit_wire_ne n counterWidth
            (RegisterBits.sCoeffValueBit n counterWidth rightBit)
            (WireAddress.littleEndianWire targetBit))

/-- The compact `s`-into-`r` coefficient addition leaves the public target
word unchanged. -/
lemma coefficientAddSIntoRStep_target_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (coefficientAddSIntoRStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).target = target := by
  simpa [coefficientAddSIntoRStep] using
    coefficientAddStep_target_cleanEndpoint n counterWidth
      (coefficientAddSIntoRLayout n counterWidth) core target (by
        intro bit
        rfl)
      (by
        intro rightBit targetBit
        simpa [coefficientAddSIntoRLayout, rCoeffValueWord,
          rCoeffValueBit, targetValueBit] using
          liftCoreBit_targetBit_wire_ne n counterWidth
            (RegisterBits.rCoeffValueBit n counterWidth rightBit)
            (WireAddress.littleEndianWire targetBit))

/-! ## Compact source-register subtraction -/

/-- The first `n - 1` cells of the one reusable VBE bank.  An `n`-bit
source subtract needs exactly this prefix as its temporary carry word; the
remaining bank cell is not addressed by this schedule. -/
def sourceCarryWorkPrefixIndex (n : Nat) (bit : Fin (n - 1)) : Fin n :=
  ⟨bit.val, by omega⟩

/-- One borrowed source-subtract carry-work bit in the compact carrier. -/
def sourceCarryWorkPrefixBit (n counterWidth : Nat) (bit : Fin (n - 1)) :
    EncodedBit (encoding n counterWidth) :=
  coefficientCarryWorkBit n counterWidth
    (sourceCarryWorkPrefixIndex n bit)

/-- The borrowed VBE carry prefix viewed as the work word for an `n`-bit
source-register adder. -/
def sourceCarryWorkPrefixWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) (n - 1) where
  bit := sourceCarryWorkPrefixBit n counterWidth

/-- Compact VBE layout whose forward direction is `u := u + v`; reversing
the physical schedule gives the source subtraction `u := u - v`.  The
carry-in is the existing core `scratchA` bit and the work word is only the
prefix of the shared coefficient-carry bank. -/
def sourceAddVIntoULayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n where
  left := vValueWord n counterWidth
  right := uValueWord n counterWidth
  carryIn := scratchABit n counterWidth
  workCarry := sourceCarryWorkPrefixWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    simpa [vValueWord, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (v_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)
          (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  rightRight_ne := by
    intro i j hij
    simpa [uValueWord, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (u_u_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)
          (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  leftRight_ne := by
    intro i j
    simpa [vValueWord, uValueWord, RegisterBits.vValueBit,
      RegisterBits.uValueBit] using
      (liftCoreBit_wire_ne n counterWidth
        (RegisterBits.u_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire j)
          (WireAddress.littleEndianWire i))).symm
  leftCarryIn_ne := by
    intro i
    simpa [vValueWord, scratchABit, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.v_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  rightCarryIn_ne := by
    intro i
    simpa [uValueWord, scratchABit, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.u_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  leftWork_ne := by
    intro i j
    simpa [vValueWord, sourceCarryWorkPrefixWord,
      sourceCarryWorkPrefixBit, RegisterBits.vValueBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth i)
        (sourceCarryWorkPrefixIndex n j)
  rightWork_ne := by
    intro i j
    simpa [uValueWord, sourceCarryWorkPrefixWord,
      sourceCarryWorkPrefixBit, RegisterBits.uValueBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth i)
        (sourceCarryWorkPrefixIndex n j)
  carryInWork_ne := by
    intro j
    simpa [scratchABit, sourceCarryWorkPrefixWord,
      sourceCarryWorkPrefixBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth)
        (sourceCarryWorkPrefixIndex n j)
  workWork_ne := by
    intro i j hij
    apply coefficientCarryWorkBit_wire_ne n counterWidth
    intro h
    apply hij
    apply Fin.ext
    simpa [sourceCarryWorkPrefixIndex] using congrArg Fin.val h

/-- Compact VBE layout whose forward direction is `v := v + u`; reversing
the physical schedule gives the source subtraction `v := v - u`. -/
def sourceAddUIntoVLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n where
  left := uValueWord n counterWidth
  right := vValueWord n counterWidth
  carryIn := scratchABit n counterWidth
  workCarry := sourceCarryWorkPrefixWord n counterWidth
  leftLeft_ne := by
    intro i j hij
    simpa [uValueWord, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (u_u_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)
          (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  rightRight_ne := by
    intro i j hij
    simpa [vValueWord, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (v_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)
          (WireAddress.littleEndianWire j) (littleEndianWire_ne hij))
  leftRight_ne := by
    intro i j
    simpa [uValueWord, vValueWord, RegisterBits.uValueBit,
      RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.u_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)
          (WireAddress.littleEndianWire j))
  leftCarryIn_ne := by
    intro i
    simpa [uValueWord, scratchABit, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.u_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  rightCarryIn_ne := by
    intro i
    simpa [vValueWord, scratchABit, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.v_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  leftWork_ne := by
    intro i j
    simpa [uValueWord, sourceCarryWorkPrefixWord,
      sourceCarryWorkPrefixBit, RegisterBits.uValueBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth i)
        (sourceCarryWorkPrefixIndex n j)
  rightWork_ne := by
    intro i j
    simpa [vValueWord, sourceCarryWorkPrefixWord,
      sourceCarryWorkPrefixBit, RegisterBits.vValueBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth i)
        (sourceCarryWorkPrefixIndex n j)
  carryInWork_ne := by
    intro j
    simpa [scratchABit, sourceCarryWorkPrefixWord,
      sourceCarryWorkPrefixBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth)
        (sourceCarryWorkPrefixIndex n j)
  workWork_ne := by
    intro i j hij
    apply coefficientCarryWorkBit_wire_ne n counterWidth
    intro h
    apply hij
    apply Fin.ext
    simpa [sourceCarryWorkPrefixIndex] using congrArg Fin.val h

/-- Actual forward gate list for `u := u + v` on the compact source words. -/
def sourceAddVIntoUGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (sourceAddVIntoULayout n counterWidth)

/-- Actual forward gate list for `v := v + u` on the compact source words. -/
def sourceAddUIntoVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (sourceAddUIntoVLayout n counterWidth)

/-- The physical reverse of the compact `v`-into-`u` adder, implementing
`u := u - v`. -/
def sourceSubVFromUGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  (sourceAddVIntoUGates n counterWidth).reverse

/-- The physical reverse of the compact `u`-into-`v` adder, implementing
`v := v - u`. -/
def sourceSubUFromVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  (sourceAddUIntoVGates n counterWidth).reverse

/-- Folded forward compact source addition `u := u + v`. -/
def sourceAddVIntoUStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (sourceAddVIntoUGates n counterWidth)

/-- Folded forward compact source addition `v := v + u`. -/
def sourceAddUIntoVStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (sourceAddUIntoVGates n counterWidth)

/-- Folded compact source subtraction `u := u - v`. -/
def sourceSubVFromUStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (sourceSubVFromUGates n counterWidth)

/-- Folded compact source subtraction `v := v - u`. -/
def sourceSubUFromVStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (sourceSubUFromVGates n counterWidth)

/-- Circuit for the compact source subtraction `u := u - v`. -/
def sourceSubVFromUProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (sourceSubVFromUGates n counterWidth)

/-- Circuit for the compact source subtraction `v := v - u`. -/
def sourceSubUFromVProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (sourceSubUFromVGates n counterWidth)

/-- The compact `u := u - v` program realizes the reverse physical schedule. -/
lemma sourceSubVFromU_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (sourceSubVFromUProgram n counterWidth) environment
      (sourceSubVFromUStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (sourceSubVFromUGates n counterWidth)

/-- The compact `v := v - u` program realizes the reverse physical schedule. -/
lemma sourceSubUFromV_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (sourceSubUFromVProgram n counterWidth) environment
      (sourceSubUFromVStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (sourceSubUFromVGates n counterWidth)

/-- Exact X coordinate of either compact source-add schedule. -/
private lemma sourceAddGates_xMultiplicity_sum
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n) :
    ((PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
    layout

/-- Exact CNOT coordinate of either compact source-add schedule. -/
private lemma sourceAddGates_cnotMultiplicity_sum
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n) :
    ((PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * n := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
    layout

/-- Exact Toffoli coordinate of either compact source-add schedule. -/
private lemma sourceAddGates_toffoliMultiplicity_sum
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n) :
    ((PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * (n - 1) := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
    layout

/-- Exact physical length of either compact source-add schedule. -/
private lemma sourceAddGates_length
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).length =
      6 * (n - 1) + 2 * n := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length layout

/-- The compact `u := u - v` source schedule has no X gates. -/
lemma sourceSubVFromUGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((sourceSubVFromUGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [sourceSubVFromUGates, sourceAddVIntoUGates,
    List.map_reverse, List.sum_reverse] using
    sourceAddGates_xMultiplicity_sum n counterWidth
      (sourceAddVIntoULayout n counterWidth)

/-- The compact `u := u - v` source schedule has exact CNOT count. -/
lemma sourceSubVFromUGates_cnotMultiplicity_sum (n counterWidth : Nat) :
    ((sourceSubVFromUGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * n := by
  simpa only [sourceSubVFromUGates, sourceAddVIntoUGates,
    List.map_reverse, List.sum_reverse] using
    sourceAddGates_cnotMultiplicity_sum n counterWidth
      (sourceAddVIntoULayout n counterWidth)

/-- The compact `u := u - v` source schedule has exact Toffoli count. -/
lemma sourceSubVFromUGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((sourceSubVFromUGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * (n - 1) := by
  simpa only [sourceSubVFromUGates, sourceAddVIntoUGates,
    List.map_reverse, List.sum_reverse] using
    sourceAddGates_toffoliMultiplicity_sum n counterWidth
      (sourceAddVIntoULayout n counterWidth)

/-- The compact `u := u - v` source schedule has exact physical length. -/
lemma sourceSubVFromUGates_length (n counterWidth : Nat) :
    (sourceSubVFromUGates n counterWidth).length = 6 * (n - 1) + 2 * n := by
  simpa only [sourceSubVFromUGates, sourceAddVIntoUGates,
    List.length_reverse] using
    sourceAddGates_length n counterWidth
      (sourceAddVIntoULayout n counterWidth)

/-- The compact `v := v - u` source schedule has no X gates. -/
lemma sourceSubUFromVGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((sourceSubUFromVGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [sourceSubUFromVGates, sourceAddUIntoVGates,
    List.map_reverse, List.sum_reverse] using
    sourceAddGates_xMultiplicity_sum n counterWidth
      (sourceAddUIntoVLayout n counterWidth)

/-- The compact `v := v - u` source schedule has exact CNOT count. -/
lemma sourceSubUFromVGates_cnotMultiplicity_sum (n counterWidth : Nat) :
    ((sourceSubUFromVGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * n := by
  simpa only [sourceSubUFromVGates, sourceAddUIntoVGates,
    List.map_reverse, List.sum_reverse] using
    sourceAddGates_cnotMultiplicity_sum n counterWidth
      (sourceAddUIntoVLayout n counterWidth)

/-- The compact `v := v - u` source schedule has exact Toffoli count. -/
lemma sourceSubUFromVGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((sourceSubUFromVGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * (n - 1) := by
  simpa only [sourceSubUFromVGates, sourceAddUIntoVGates,
    List.map_reverse, List.sum_reverse] using
    sourceAddGates_toffoliMultiplicity_sum n counterWidth
      (sourceAddUIntoVLayout n counterWidth)

/-- The compact `v := v - u` source schedule has exact physical length. -/
lemma sourceSubUFromVGates_length (n counterWidth : Nat) :
    (sourceSubUFromVGates n counterWidth).length = 6 * (n - 1) + 2 * n := by
  simpa only [sourceSubUFromVGates, sourceAddUIntoVGates,
    List.length_reverse] using
    sourceAddGates_length n counterWidth
      (sourceAddUIntoVLayout n counterWidth)

/-- The compiled `u := u - v` circuit retains the exact X count. -/
lemma sourceSubVFromUProgram_x_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (sourceSubVFromUProgram n counterWidth).eventCost = 0 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (sourceSubVFromUGates n counterWidth)).eventCost = 0
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    sourceSubVFromUGates_xMultiplicity_sum]

/-- The compiled `u := u - v` circuit retains the exact CNOT count. -/
lemma sourceSubVFromUProgram_cnot_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (sourceSubVFromUProgram n counterWidth).eventCost = 2 * n := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (sourceSubVFromUGates n counterWidth)).eventCost = 2 * n
  rw [EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    sourceSubVFromUGates_cnotMultiplicity_sum]

/-- The compiled `u := u - v` circuit retains the exact Toffoli count. -/
lemma sourceSubVFromUProgram_toffoli_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (sourceSubVFromUProgram n counterWidth).eventCost = 6 * (n - 1) := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (sourceSubVFromUGates n counterWidth)).eventCost = 6 * (n - 1)
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    sourceSubVFromUGates_toffoliMultiplicity_sum]

/-- The compiled `v := v - u` circuit retains the exact X count. -/
lemma sourceSubUFromVProgram_x_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (sourceSubUFromVProgram n counterWidth).eventCost = 0 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (sourceSubUFromVGates n counterWidth)).eventCost = 0
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    sourceSubUFromVGates_xMultiplicity_sum]

/-- The compiled `v := v - u` circuit retains the exact CNOT count. -/
lemma sourceSubUFromVProgram_cnot_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (sourceSubUFromVProgram n counterWidth).eventCost = 2 * n := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (sourceSubUFromVGates n counterWidth)).eventCost = 2 * n
  rw [EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    sourceSubUFromVGates_cnotMultiplicity_sum]

/-- The compiled `v := v - u` circuit retains the exact Toffoli count. -/
lemma sourceSubUFromVProgram_toffoli_count (n counterWidth : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (sourceSubUFromVProgram n counterWidth).eventCost = 6 * (n - 1) := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (sourceSubUFromVGates n counterWidth)).eventCost = 6 * (n - 1)
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    sourceSubUFromVGates_toffoliMultiplicity_sum]

/-! ### Shared source-add/subtract reasoning -/

/-- On clean borrowed carry work, an arbitrary compact source-add layout
computes the natural carry propagated from its specified source and target
words. -/
private lemma sourceAdd_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (left right : Word n) (j : Fin (n - 1))
    (x : Registers n counterWidth)
    (hleft : ∀ bit : Fin n,
      (layout.left.bit bit).get x = left.val.testBit bit.val)
    (hright : ∀ bit : Fin n,
      (layout.right.bit bit).get x = right.val.testBit bit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ bit : Fin (n - 1),
      (layout.workCarry.bit bit).get x = false) :
    (layout.workCarry.bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left.val right.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x
  change (layout.workCarry.bit j).get stage =
    Nat.BinaryArithmetic.natAddCarry left.val right.val (j.val + 1)
  have hmain : ∀ m, ∀ workBit : Fin (n - 1), workBit.val = m ->
      (layout.workCarry.bit workBit).get stage =
        Nat.BinaryArithmetic.natAddCarry
          left.val right.val (workBit.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro workBit hworkBit
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            layout workBit x hwork
        change (layout.workCarry.bit workBit).get stage =
          Nat.BinaryArithmetic.natAddCarry
            left.val right.val (workBit.val + 1)
        change
          (layout.workCarry.bit workBit).get
              (layout.carryStageIndexStep x) =
            Nat.BinaryArithmetic.natAddCarry
              left.val right.val (workBit.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : workBit.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              layout x
          rw [hdata]
          change Bool.carry
              ((layout.left.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex workBit)).get x)
              ((layout.right.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex workBit)).get x)
              (layout.carryIn.get x) =
            Nat.BinaryArithmetic.natAddCarry
              left.val right.val (workBit.val + 1)
          rw [hleft, hright, hcarry]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let previous :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex workBit hzero
          have hpreviousLt : previous.val < m := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hprevious := ih previous.val hpreviousLt previous rfl
          have hprevious' :
              (layout.workCarry.bit previous).get
                  (layout.carryStageIndexStep x) =
                Nat.BinaryArithmetic.natAddCarry
                  left.val right.val (previous.val + 1) := by
            simpa only [stage] using hprevious
          have hpreviousSucc : previous.val + 1 = workBit.val := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hprevious', hpreviousSucc]
          change Bool.carry
              ((layout.left.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex workBit)).get x)
              ((layout.right.bit
                (PlainAdder.Schedule.CarryWorkLayout.lowIndex workBit)).get x)
              (Nat.BinaryArithmetic.natAddCarry
                left.val right.val workBit.val) =
            Bool.carry
              (left.val.testBit workBit.val)
              (right.val.testBit workBit.val)
              (Nat.BinaryArithmetic.natAddCarry
                left.val right.val workBit.val)
          rw [hleft, hright]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex]
  exact hmain j.val j rfl

/-- The carry selected before an arbitrary compact source-add target bit is
the natural addition carry when the borrowed scratch/carry prefix is clean. -/
private lemma sourceAdd_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (left right : Word n) (bit : Fin n)
    (x : Registers n counterWidth)
    (hleft : ∀ leftBit : Fin n,
      (layout.left.bit leftBit).get x = left.val.testBit leftBit.val)
    (hright : ∀ rightBit : Fin n,
      (layout.right.bit rightBit).get x = right.val.testBit rightBit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ workBit : Fin (n - 1),
      (layout.workCarry.bit workBit).get x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum layout bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left.val right.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        layout x
    rw [hdata]
    simp [hcarry, Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hworkLt : bit.val - 1 < n - 1 := by
      have hbit := bit.isLt
      omega
    let workBit : Fin (n - 1) := ⟨bit.val - 1, hworkLt⟩
    have hworkCarry :=
      sourceAdd_carryStage_get_workCarry_natAddCarry
        n counterWidth layout left right workBit x
        hleft hright hcarry hwork
    have hworkSucc : workBit.val + 1 = bit.val := by
      dsimp [workBit]
      omega
    change (layout.workCarry.bit workBit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left.val right.val bit.val
    rw [hworkCarry, hworkSucc]

/-- A clean compact source-add writes its target word as target plus source. -/
private lemma sourceAdd_cleanStep_get_right_add_testBit_of_clean
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (left right : Word n) (bit : Fin n)
    (x : Registers n counterWidth)
    (hleft : ∀ leftBit : Fin n,
      (layout.left.bit leftBit).get x = left.val.testBit leftBit.val)
    (hright : ∀ rightBit : Fin n,
      (layout.right.bit rightBit).get x = right.val.testBit rightBit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : ∀ workBit : Fin (n - 1),
      (layout.workCarry.bit workBit).get x = false) :
    (layout.right.bit bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
      (right + left).val.testBit bit.val := by
  have hrightStep :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      layout bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hrightStep
  have hcarryBit :=
    sourceAdd_carryBeforeSum_get_natAddCarry
      n counterWidth layout left right bit x hleft hright hcarry hwork
  rw [hcarryBit] at hrightStep
  have hadd := (word_add_testBit_eq_xor3 n left right bit).symm
  calc
    (layout.right.bit bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
        (((right.val.testBit bit.val ^^
              left.val.testBit bit.val) ^^
            Nat.BinaryArithmetic.natAddCarry
              left.val right.val bit.val)) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        hleft, hright, Bool.xor_assoc] using hrightStep
    _ = (right + left).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using hadd

/-- The reverse of a compact source-add preserves the left/source readout. -/
private lemma sourceSubStep_get_left
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (bit : Fin n) (x : Registers n counterWidth) :
    (layout.left.bit bit).get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x) =
      (layout.left.bit bit).get x := by
  have hadd := PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
    layout bit
      (EncodedBit.GateSpec.stepList
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x)
  have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x
  calc
    (layout.left.bit bit).get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x) =
        (layout.left.bit bit).get
          (EncodedBit.GateSpec.stepList
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout)
              (EncodedBit.GateSpec.stepList
                (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
                  x)) := by
      exact hadd.symm
    _ = (layout.left.bit bit).get x := by
      simpa only [List.reverse_reverse] using congrArg
        (fun y => (layout.left.bit bit).get y) hcancel

/-- The reverse of a compact source-add preserves its scratch carry-in. -/
private lemma sourceSubStep_get_carryIn
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (x : Registers n counterWidth) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x) =
      layout.carryIn.get x := by
  have hadd :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      layout
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x)
  have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x
  calc
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x) =
        layout.carryIn.get
          (EncodedBit.GateSpec.stepList
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout)
              (EncodedBit.GateSpec.stepList
                (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
                  x)) := by
      exact hadd.symm
    _ = layout.carryIn.get x := by
      simpa only [List.reverse_reverse] using congrArg
        (fun y => layout.carryIn.get y) hcancel

/-- The reverse of a compact source-add also restores a clean borrowed VBE
carry-prefix. -/
private lemma sourceSubStep_get_workCarry_clean
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (bit : Fin (n - 1)) (x : Registers n counterWidth)
    (hclean : ∀ workBit : Fin (n - 1),
      (layout.workCarry.bit workBit).get x = false) :
    (layout.workCarry.bit bit).get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x) =
      false := by
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_reverse_get_workCarry_clean
      layout bit x hclean

/-- An observation outside a compact source-add target and borrowed VBE prefix
is preserved even when the schedule is run in reverse. -/
private lemma sourceSubStep_get_observed_of_right_work_ne
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (observed : EncodedBit (encoding n counterWidth))
    (hright : ∀ bit : Fin n,
      (layout.right.bit bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin (n - 1),
      (layout.workCarry.bit bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x) =
      observed.get x := by
  have hadd :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      layout observed hright hwork
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x)
  have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x
  calc
    observed.get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x) =
        observed.get
          (EncodedBit.GateSpec.stepList
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout)
              (EncodedBit.GateSpec.stepList
                (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
                  x)) := by
      exact hadd.symm
    _ = observed.get x := by
      simpa only [List.reverse_reverse] using congrArg
        (fun y => observed.get y) hcancel

/-- An observation disjoint from the `u` target word and borrowed prefix is
preserved by the compact source subtraction `u := u - v`. -/
private lemma sourceSubVFromUStep_get_observed_of_u_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hright : ∀ bit : Fin n,
      ((uValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (sourceSubVFromUStep n counterWidth x) = observed.get x := by
  have h := sourceSubStep_get_observed_of_right_work_ne
    n counterWidth (sourceAddVIntoULayout n counterWidth) observed
    (by
      intro bit
      simpa only [sourceAddVIntoULayout] using hright bit)
    (by
      intro bit
      simpa [sourceAddVIntoULayout, sourceCarryWorkPrefixWord] using
        hwork bit)
    x
  simpa only [sourceSubVFromUStep, sourceSubVFromUGates,
    sourceAddVIntoUGates] using h

/-- An observation disjoint from the `v` target word and borrowed prefix is
preserved by the compact source subtraction `v := v - u`. -/
private lemma sourceSubUFromVStep_get_observed_of_v_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hright : ∀ bit : Fin n,
      ((vValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (sourceSubUFromVStep n counterWidth x) = observed.get x := by
  have h := sourceSubStep_get_observed_of_right_work_ne
    n counterWidth (sourceAddUIntoVLayout n counterWidth) observed
    (by
      intro bit
      simpa only [sourceAddUIntoVLayout] using hright bit)
    (by
      intro bit
      simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord] using
        hwork bit)
    x
  simpa only [sourceSubUFromVStep, sourceSubUFromVGates,
    sourceAddUIntoVGates] using h

/-- A clean compact shared workspace makes every borrowed source-subtract
carry-prefix bit clean. -/
private lemma sourceCarryWorkPrefixBit_get_cleanInput
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (bit : Fin (n - 1)) :
    (sourceCarryWorkPrefixBit n counterWidth bit).get
        (coefficientAddCleanInput n counterWidth core target) = false := by
  change (coefficientCarryWorkBit n counterWidth
      (sourceCarryWorkPrefixIndex n bit)).get
        (coefficientAddCleanInput n counterWidth core target) = false
  exact coefficientCarryWorkBit_get_coefficientAddCleanInput
    n counterWidth core target (sourceCarryWorkPrefixIndex n bit)

/-- Reversing an `n`-bit source adder restores the whole reusable VBE object.
The source schedule touches only the first `n-1` work cells; the proof treats
the remaining cell as a physically disjoint observation. -/
private lemma sourceSubStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (core : MK.Registers n counterWidth) (target : Word n)
    (hworkPrefix : ∀ bit : Fin (n - 1),
      layout.workCarry.bit bit = sourceCarryWorkPrefixBit n counterWidth bit)
    (hrightCarry : ∀ bit : Fin n,
      (layout.right.bit bit).wire ≠
        (coefficientCarryInBit n counterWidth).wire)
    (hrightWork : ∀ rightBit : Fin n, ∀ workBit : Fin n,
      (layout.right.bit rightBit).wire ≠
        (coefficientCarryWorkBit n counterWidth workBit).wire) :
    (EncodedBit.GateSpec.stepList
      (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
      (coefficientAddCleanInput n counterWidth core target)).shared.coefficientAdder =
        cleanCoeffAdderWork n := by
  change _ = (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1))
  apply Prod.ext
  · change (coefficientCarryInBit n counterWidth).get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
          (coefficientAddCleanInput n counterWidth core target)) = false
    rw [sourceSubStep_get_observed_of_right_work_ne
      n counterWidth layout (coefficientCarryInBit n counterWidth)
      hrightCarry]
    · exact coefficientCarryInBit_get_coefficientAddCleanInput
        n counterWidth core target
    · intro bit
      rw [hworkPrefix bit]
      exact (coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
        n counterWidth (sourceCarryWorkPrefixIndex n bit)).symm
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    change (coefficientCarryWorkBit n counterWidth workBit).get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
          (coefficientAddCleanInput n counterWidth core target)) = false
    by_cases hprefix : workBit.val < n - 1
    · let prefixBit : Fin (n - 1) := ⟨workBit.val, hprefix⟩
      have hclean := sourceSubStep_get_workCarry_clean n counterWidth layout
        prefixBit (coefficientAddCleanInput n counterWidth core target) (by
          intro bit
          rw [hworkPrefix bit]
          exact sourceCarryWorkPrefixBit_get_cleanInput
            n counterWidth core target bit)
      have hindex : sourceCarryWorkPrefixIndex n prefixBit = workBit := by
        apply Fin.ext
        rfl
      simpa [hworkPrefix prefixBit, sourceCarryWorkPrefixBit, hindex] using hclean
    · rw [sourceSubStep_get_observed_of_right_work_ne
        n counterWidth layout (coefficientCarryWorkBit n counterWidth workBit)
        (fun rightBit => hrightWork rightBit workBit)]
      · exact coefficientCarryWorkBit_get_coefficientAddCleanInput
          n counterWidth core target workBit
      · intro prefixBit
        rw [hworkPrefix prefixBit]
        apply coefficientCarryWorkBit_wire_ne n counterWidth
        intro heq
        have hval := congrArg Fin.val heq
        have hlt := prefixBit.isLt
        simp [sourceCarryWorkPrefixIndex] at hval
        omega

/-- Reversing an `n`-bit source adder restores an arbitrary clean reusable
VBE object.  Unlike the constructor-specialized lemma above, this form can be
used after a selector has changed only routing and comparison bits. -/
private lemma sourceSubStep_coefficientAdder_cleanEndpoint_of_clean
    (n counterWidth : Nat)
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding n counterWidth) n)
    (x : Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false)
    (hworkPrefix : ∀ bit : Fin (n - 1),
      layout.workCarry.bit bit = sourceCarryWorkPrefixBit n counterWidth bit)
    (hrightCarry : ∀ bit : Fin n,
      (layout.right.bit bit).wire ≠
        (coefficientCarryInBit n counterWidth).wire)
    (hrightWork : ∀ rightBit : Fin n, ∀ workBit : Fin n,
      (layout.right.bit rightBit).wire ≠
        (coefficientCarryWorkBit n counterWidth workBit).wire) :
    (EncodedBit.GateSpec.stepList
      (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
      x).shared.coefficientAdder = cleanCoeffAdderWork n := by
  change _ = (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1))
  apply Prod.ext
  · change (coefficientCarryInBit n counterWidth).get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
          x) = false
    rw [sourceSubStep_get_observed_of_right_work_ne
      n counterWidth layout (coefficientCarryInBit n counterWidth)
      hrightCarry]
    · exact hcarry
    · intro bit
      rw [hworkPrefix bit]
      exact (coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
        n counterWidth (sourceCarryWorkPrefixIndex n bit)).symm
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    change (coefficientCarryWorkBit n counterWidth workBit).get
        (EncodedBit.GateSpec.stepList
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse
          x) = false
    by_cases hprefix : workBit.val < n - 1
    · let prefixBit : Fin (n - 1) := ⟨workBit.val, hprefix⟩
      have hclean := sourceSubStep_get_workCarry_clean n counterWidth layout
        prefixBit x (by
          intro bit
          rw [hworkPrefix bit]
          exact hwork (sourceCarryWorkPrefixIndex n bit))
      have hindex : sourceCarryWorkPrefixIndex n prefixBit = workBit := by
        apply Fin.ext
        rfl
      simpa [hworkPrefix prefixBit, sourceCarryWorkPrefixBit, hindex] using hclean
    · rw [sourceSubStep_get_observed_of_right_work_ne
        n counterWidth layout (coefficientCarryWorkBit n counterWidth workBit)
        (fun rightBit => hrightWork rightBit workBit)]
      · exact hwork workBit
      · intro prefixBit
        rw [hworkPrefix prefixBit]
        apply coefficientCarryWorkBit_wire_ne n counterWidth
        intro heq
        have hval := congrArg Fin.val heq
        have hlt := prefixBit.isLt
        simp [sourceCarryWorkPrefixIndex] at hval
        omega

/-- The compact `u := u-v` source path restores any clean VBE bank. -/
lemma sourceSubVFromUStep_coefficientAdder_cleanEndpoint_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (sourceSubVFromUStep n counterWidth x).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  simpa [sourceSubVFromUStep, sourceSubVFromUGates, sourceAddVIntoUGates] using
    sourceSubStep_coefficientAdder_cleanEndpoint_of_clean n counterWidth
      (sourceAddVIntoULayout n counterWidth) x hcarry hwork (by
        intro bit
        rfl)
      (by
        intro bit
        simpa [sourceAddVIntoULayout, uValueWord,
          RegisterBits.uValueBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
            (RegisterBits.uValueBit n counterWidth bit))
      (by
        intro rightBit workBit
        simpa [sourceAddVIntoULayout, uValueWord,
          RegisterBits.uValueBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
            (RegisterBits.uValueBit n counterWidth rightBit) workBit)

/-- The compact `v := v-u` source path restores any clean VBE bank. -/
lemma sourceSubUFromVStep_coefficientAdder_cleanEndpoint_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (sourceSubUFromVStep n counterWidth x).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  simpa [sourceSubUFromVStep, sourceSubUFromVGates, sourceAddUIntoVGates] using
    sourceSubStep_coefficientAdder_cleanEndpoint_of_clean n counterWidth
      (sourceAddUIntoVLayout n counterWidth) x hcarry hwork (by
        intro bit
        rfl)
      (by
        intro bit
        simpa [sourceAddUIntoVLayout, vValueWord,
          RegisterBits.vValueBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth bit))
      (by
        intro rightBit workBit
        simpa [sourceAddUIntoVLayout, vValueWord,
          RegisterBits.vValueBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth rightBit) workBit)

/-- The compact `u := u-v` source path restores the complete VBE bank. -/
lemma sourceSubVFromUStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (sourceSubVFromUStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).shared.coefficientAdder =
        cleanCoeffAdderWork n := by
  simpa [sourceSubVFromUStep, sourceSubVFromUGates, sourceAddVIntoUGates] using
    sourceSubStep_coefficientAdder_cleanEndpoint n counterWidth
      (sourceAddVIntoULayout n counterWidth) core target (by
        intro bit
        rfl)
      (by
        intro bit
        simpa [sourceAddVIntoULayout, uValueWord,
          RegisterBits.uValueBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
            (RegisterBits.uValueBit n counterWidth bit))
      (by
        intro rightBit workBit
        simpa [sourceAddVIntoULayout, uValueWord,
          RegisterBits.uValueBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
            (RegisterBits.uValueBit n counterWidth rightBit) workBit)

/-- The compact `v := v-u` source path restores the complete VBE bank. -/
lemma sourceSubUFromVStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (sourceSubUFromVStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).shared.coefficientAdder =
        cleanCoeffAdderWork n := by
  simpa [sourceSubUFromVStep, sourceSubUFromVGates, sourceAddUIntoVGates] using
    sourceSubStep_coefficientAdder_cleanEndpoint n counterWidth
      (sourceAddUIntoVLayout n counterWidth) core target (by
        intro bit
        rfl)
      (by
        intro bit
        simpa [sourceAddUIntoVLayout, vValueWord,
          RegisterBits.vValueBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth bit))
      (by
        intro rightBit workBit
        simpa [sourceAddUIntoVLayout, vValueWord,
          RegisterBits.vValueBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth rightBit) workBit)

/-- On a clean scratch/carry prefix, the forward compact `v`-into-`u` adder
writes `u` as `u + v`. -/
lemma sourceAddVIntoUStep_get_u_add_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hscratch : (scratchABit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).get x = false) :
    (sourceAddVIntoUStep n counterWidth x).core.u =
      x.core.u + x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := sourceAdd_cleanStep_get_right_add_testBit_of_clean
    n counterWidth (sourceAddVIntoULayout n counterWidth)
    x.core.v x.core.u bit x
    (by
      intro leftBit
      change ((vValueWord n counterWidth).bit leftBit).get x =
        x.core.v.val.testBit leftBit.val
      exact vValueWord_get n counterWidth leftBit x)
    (by
      intro rightBit
      change ((uValueWord n counterWidth).bit rightBit).get x =
        x.core.u.val.testBit rightBit.val
      exact uValueWord_get n counterWidth rightBit x)
    (by
      simpa [sourceAddVIntoULayout] using hscratch)
    (by
      intro workBit
      simpa [sourceAddVIntoULayout, sourceCarryWorkPrefixWord] using
        hwork workBit)
  calc
    (sourceAddVIntoUStep n counterWidth x).core.u.val.testBit bit.val =
        ((uValueWord n counterWidth).bit bit).get
          (sourceAddVIntoUStep n counterWidth x) := by
      symm
      exact uValueWord_get n counterWidth bit
        (sourceAddVIntoUStep n counterWidth x)
    _ = (x.core.u + x.core.v).val.testBit bit.val := by
      simpa [sourceAddVIntoUStep, sourceAddVIntoUGates,
        sourceAddVIntoULayout, uValueWord,
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- On a clean scratch/carry prefix, the forward compact `u`-into-`v` adder
writes `v` as `v + u`. -/
lemma sourceAddUIntoVStep_get_v_add_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hscratch : (scratchABit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).get x = false) :
    (sourceAddUIntoVStep n counterWidth x).core.v =
      x.core.v + x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := sourceAdd_cleanStep_get_right_add_testBit_of_clean
    n counterWidth (sourceAddUIntoVLayout n counterWidth)
    x.core.u x.core.v bit x
    (by
      intro leftBit
      change ((uValueWord n counterWidth).bit leftBit).get x =
        x.core.u.val.testBit leftBit.val
      exact uValueWord_get n counterWidth leftBit x)
    (by
      intro rightBit
      change ((vValueWord n counterWidth).bit rightBit).get x =
        x.core.v.val.testBit rightBit.val
      exact vValueWord_get n counterWidth rightBit x)
    (by
      simpa [sourceAddUIntoVLayout] using hscratch)
    (by
      intro workBit
      simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord] using
        hwork workBit)
  calc
    (sourceAddUIntoVStep n counterWidth x).core.v.val.testBit bit.val =
        ((vValueWord n counterWidth).bit bit).get
          (sourceAddUIntoVStep n counterWidth x) := by
      symm
      exact vValueWord_get n counterWidth bit
        (sourceAddUIntoVStep n counterWidth x)
    _ = (x.core.v + x.core.u).val.testBit bit.val := by
      simpa [sourceAddUIntoVStep, sourceAddUIntoVGates,
        sourceAddUIntoVLayout, vValueWord,
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- The reverse compact `v`-into-`u` path preserves the source word `v`. -/
lemma sourceSubVFromUStep_get_v
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (sourceSubVFromUStep n counterWidth x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := sourceSubStep_get_left n counterWidth
    (sourceAddVIntoULayout n counterWidth) bit x
  calc
    (sourceSubVFromUStep n counterWidth x).core.v.val.testBit bit.val =
        ((vValueWord n counterWidth).bit bit).get
          (sourceSubVFromUStep n counterWidth x) := by
      symm
      exact vValueWord_get n counterWidth bit
        (sourceSubVFromUStep n counterWidth x)
    _ = ((vValueWord n counterWidth).bit bit).get x := by
      simpa [sourceSubVFromUStep, sourceSubVFromUGates,
        sourceAddVIntoUGates, sourceAddVIntoULayout, vValueWord] using h
    _ = x.core.v.val.testBit bit.val :=
      vValueWord_get n counterWidth bit x

/-- The reverse compact `u`-into-`v` path preserves the source word `u`. -/
lemma sourceSubUFromVStep_get_u
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (sourceSubUFromVStep n counterWidth x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := sourceSubStep_get_left n counterWidth
    (sourceAddUIntoVLayout n counterWidth) bit x
  calc
    (sourceSubUFromVStep n counterWidth x).core.u.val.testBit bit.val =
        ((uValueWord n counterWidth).bit bit).get
          (sourceSubUFromVStep n counterWidth x) := by
      symm
      exact uValueWord_get n counterWidth bit
        (sourceSubUFromVStep n counterWidth x)
    _ = ((uValueWord n counterWidth).bit bit).get x := by
      simpa [sourceSubUFromVStep, sourceSubUFromVGates,
        sourceAddUIntoVGates, sourceAddUIntoVLayout, uValueWord] using h
    _ = x.core.u.val.testBit bit.val :=
      uValueWord_get n counterWidth bit x

/-- Both reverse compact source paths preserve the core scratch carry bit. -/
lemma sourceSubVFromUStep_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (sourceSubVFromUStep n counterWidth x).core.scratchA = x.core.scratchA := by
  have h := sourceSubStep_get_carryIn n counterWidth
    (sourceAddVIntoULayout n counterWidth) x
  have hgetter :
      (scratchABit n counterWidth).get
          (sourceSubVFromUStep n counterWidth x) =
        (scratchABit n counterWidth).get x := by
    simpa only [sourceSubVFromUStep, sourceSubVFromUGates,
      sourceAddVIntoUGates, sourceAddVIntoULayout] using h
  simpa only [scratchABit_get] using hgetter

/-- Both reverse compact source paths preserve the core scratch carry bit. -/
lemma sourceSubUFromVStep_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (sourceSubUFromVStep n counterWidth x).core.scratchA = x.core.scratchA := by
  have h := sourceSubStep_get_carryIn n counterWidth
    (sourceAddUIntoVLayout n counterWidth) x
  have hgetter :
      (scratchABit n counterWidth).get
          (sourceSubUFromVStep n counterWidth x) =
        (scratchABit n counterWidth).get x := by
    simpa only [sourceSubUFromVStep, sourceSubUFromVGates,
      sourceAddUIntoVGates, sourceAddUIntoVLayout] using h
  simpa only [scratchABit_get] using hgetter

/-- Forward and reverse compact `v`-into-`u` schedules are inverse. -/
lemma sourceSubVFromUStep_comp_addVIntoU
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    sourceSubVFromUStep n counterWidth
        (sourceAddVIntoUStep n counterWidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (sourceAddVIntoUGates n counterWidth) x

/-- Forward and reverse compact `v`-into-`u` schedules are inverse. -/
lemma sourceAddVIntoUStep_comp_subVFromU
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    sourceAddVIntoUStep n counterWidth
        (sourceSubVFromUStep n counterWidth x) = x := by
  have h := EncodedBit.GateSpec.stepList_reverse_stepList
    (sourceAddVIntoUGates n counterWidth).reverse x
  simpa [sourceAddVIntoUStep, sourceSubVFromUStep,
    sourceSubVFromUGates] using h

/-- Forward and reverse compact `u`-into-`v` schedules are inverse. -/
lemma sourceSubUFromVStep_comp_addUIntoV
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    sourceSubUFromVStep n counterWidth
        (sourceAddUIntoVStep n counterWidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (sourceAddUIntoVGates n counterWidth) x

/-- Forward and reverse compact `u`-into-`v` schedules are inverse. -/
lemma sourceAddUIntoVStep_comp_subUFromV
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    sourceAddUIntoVStep n counterWidth
        (sourceSubUFromVStep n counterWidth x) = x := by
  have h := EncodedBit.GateSpec.stepList_reverse_stepList
    (sourceAddUIntoVGates n counterWidth).reverse x
  simpa [sourceAddUIntoVStep, sourceSubUFromVStep,
    sourceSubUFromVGates] using h

/-- With clean scratch and borrowed VBE prefix, the physical reverse of
`u := u + v` implements `u := u - v`. -/
lemma sourceSubVFromUStep_get_u_sub_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hscratch : (scratchABit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).get x = false) :
    (sourceSubVFromUStep n counterWidth x).core.u =
      x.core.u - x.core.v := by
  let z := sourceSubVFromUStep n counterWidth x
  have hcarryZ : (scratchABit n counterWidth).get z = false := by
    dsimp [z]
    calc
      (scratchABit n counterWidth).get
          (sourceSubVFromUStep n counterWidth x) =
          (scratchABit n counterWidth).get x := by
        simpa only [scratchABit_get] using
          (sourceSubVFromUStep_get_scratchA n counterWidth x)
      _ = false := hscratch
  have hworkZ : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).get z = false := by
    intro bit
    dsimp [z]
    exact sourceSubStep_get_workCarry_clean n counterWidth
      (sourceAddVIntoULayout n counterWidth) bit x (by
        intro workBit
        simpa [sourceAddVIntoULayout, sourceCarryWorkPrefixWord] using
          hwork workBit)
  have hadd := sourceAddVIntoUStep_get_u_add_of_clean
    n counterWidth z hcarryZ hworkZ
  have hcancel := sourceAddVIntoUStep_comp_subVFromU n counterWidth x
  have hsource := sourceSubVFromUStep_get_v n counterWidth x
  have hu : x.core.u = z.core.u + z.core.v := by
    calc
      x.core.u = (sourceAddVIntoUStep n counterWidth z).core.u := by
        rw [hcancel]
      _ = z.core.u + z.core.v := hadd
  change z.core.u = x.core.u - x.core.v
  rw [← hsource]
  rw [eq_sub_iff_add_eq]
  exact hu.symm

/-- With clean scratch and borrowed VBE prefix, the physical reverse of
`v := v + u` implements `v := v - u`. -/
lemma sourceSubUFromVStep_get_v_sub_of_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hscratch : (scratchABit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).get x = false) :
    (sourceSubUFromVStep n counterWidth x).core.v =
      x.core.v - x.core.u := by
  let z := sourceSubUFromVStep n counterWidth x
  have hcarryZ : (scratchABit n counterWidth).get z = false := by
    dsimp [z]
    calc
      (scratchABit n counterWidth).get
          (sourceSubUFromVStep n counterWidth x) =
          (scratchABit n counterWidth).get x := by
        simpa only [scratchABit_get] using
          (sourceSubUFromVStep_get_scratchA n counterWidth x)
      _ = false := hscratch
  have hworkZ : ∀ bit : Fin (n - 1),
      (sourceCarryWorkPrefixBit n counterWidth bit).get z = false := by
    intro bit
    dsimp [z]
    exact sourceSubStep_get_workCarry_clean n counterWidth
      (sourceAddUIntoVLayout n counterWidth) bit x (by
        intro workBit
        simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord] using
          hwork workBit)
  have hadd := sourceAddUIntoVStep_get_v_add_of_clean
    n counterWidth z hcarryZ hworkZ
  have hcancel := sourceAddUIntoVStep_comp_subUFromV n counterWidth x
  have hsource := sourceSubUFromVStep_get_u n counterWidth x
  have hv : x.core.v = z.core.v + z.core.u := by
    calc
      x.core.v = (sourceAddUIntoVStep n counterWidth z).core.v := by
        rw [hcancel]
      _ = z.core.v + z.core.u := hadd
  change z.core.v = x.core.v - x.core.u
  rw [← hsource]
  rw [eq_sub_iff_add_eq]
  exact hv.symm

/-- Every core readout disjoint from the `u` target word is preserved by the
compact source subtraction `u := u - v`.  The source-subtract carry prefix is
in shared workspace, so a core readout is automatically disjoint from it. -/
lemma sourceSubVFromUStep_get_coreBit_of_disjoint
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hright : ∀ bit : Fin n,
      (RegisterBits.uValueBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (sourceSubVFromUStep n counterWidth x).core =
      observed.get x.core := by
  have h := sourceSubStep_get_observed_of_right_work_ne
    n counterWidth (sourceAddVIntoULayout n counterWidth)
    (liftCoreBit n counterWidth observed)
    (by
      intro bit
      simpa [sourceAddVIntoULayout, uValueWord] using
        liftCoreBit_wire_ne n counterWidth (hright bit))
    (by
      intro workBit
      simpa [sourceAddVIntoULayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth observed
          (sourceCarryWorkPrefixIndex n workBit)).symm)
    x
  simpa only [sourceSubVFromUStep, sourceSubVFromUGates,
    sourceAddVIntoUGates, liftCoreBit_get] using h

/-- Every core readout disjoint from the `v` target word is preserved by the
compact source subtraction `v := v - u`. -/
lemma sourceSubUFromVStep_get_coreBit_of_disjoint
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hright : ∀ bit : Fin n,
      (RegisterBits.vValueBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (sourceSubUFromVStep n counterWidth x).core =
      observed.get x.core := by
  have h := sourceSubStep_get_observed_of_right_work_ne
    n counterWidth (sourceAddUIntoVLayout n counterWidth)
    (liftCoreBit n counterWidth observed)
    (by
      intro bit
      simpa [sourceAddUIntoVLayout, vValueWord] using
        liftCoreBit_wire_ne n counterWidth (hright bit))
    (by
      intro workBit
      simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth observed
          (sourceCarryWorkPrefixIndex n workBit)).symm)
    x
  simpa only [sourceSubUFromVStep, sourceSubUFromVGates,
    sourceAddUIntoVGates, liftCoreBit_get] using h

/-- Clean-work word endpoint for compact `u := u - v`.  The clean shared
workspace supplies the borrowed VBE prefix; `scratchA` remains an explicit
core precondition because it is the schedule carry-in. -/
lemma sourceSubVFromUStep_u_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (hscratch : core.scratchA = false) :
    (sourceSubVFromUStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.u =
      core.u - core.v := by
  exact sourceSubVFromUStep_get_u_sub_of_clean n counterWidth
    (coefficientAddCleanInput n counterWidth core target)
    (by
      simpa only [scratchABit_get, coefficientAddCleanInput] using hscratch)
    (sourceCarryWorkPrefixBit_get_cleanInput n counterWidth core target)

/-- Clean-work word endpoint for compact `v := v - u`. -/
lemma sourceSubUFromVStep_v_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (hscratch : core.scratchA = false) :
    (sourceSubUFromVStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.v =
      core.v - core.u := by
  exact sourceSubUFromVStep_get_v_sub_of_clean n counterWidth
    (coefficientAddCleanInput n counterWidth core target)
    (by
      simpa only [scratchABit_get, coefficientAddCleanInput] using hscratch)
    (sourceCarryWorkPrefixBit_get_cleanInput n counterWidth core target)

/-- Clean-work source endpoint for compact `u := u - v`. -/
lemma sourceSubVFromUStep_v_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (sourceSubVFromUStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.v = core.v :=
  sourceSubVFromUStep_get_v n counterWidth
    (coefficientAddCleanInput n counterWidth core target)

/-- Clean-work source endpoint for compact `v := v - u`. -/
lemma sourceSubUFromVStep_u_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (sourceSubUFromVStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.u = core.u :=
  sourceSubUFromVStep_get_u n counterWidth
    (coefficientAddCleanInput n counterWidth core target)

/-- The compact source subtraction `u := u - v` leaves the public target
word untouched. -/
lemma sourceSubVFromUStep_target_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (sourceSubVFromUStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).target = target := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h := sourceSubStep_get_observed_of_right_work_ne
    n counterWidth (sourceAddVIntoULayout n counterWidth)
    (targetValueBit n counterWidth targetBit)
    (by
      intro rightBit
      simpa [sourceAddVIntoULayout, uValueWord, targetValueBit] using
        liftCoreBit_targetBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth rightBit)
          (WireAddress.littleEndianWire targetBit))
    (by
      intro workBit
      simpa only [sourceAddVIntoULayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, coefficientCarryWorkBit,
        targetValueBit] using
        liftSharedBit_targetBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth
            (sourceCarryWorkPrefixIndex n workBit))
          (WireAddress.littleEndianWire targetBit))
    (coefficientAddCleanInput n counterWidth core target)
  simpa only [sourceSubVFromUStep, sourceSubVFromUGates,
    sourceAddVIntoUGates, targetValueBit_get,
    coefficientAddCleanInput] using h

/-- The compact source subtraction `v := v - u` leaves the public target
word untouched. -/
lemma sourceSubUFromVStep_target_cleanEndpoint
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) :
    (sourceSubUFromVStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).target = target := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h := sourceSubStep_get_observed_of_right_work_ne
    n counterWidth (sourceAddUIntoVLayout n counterWidth)
    (targetValueBit n counterWidth targetBit)
    (by
      intro rightBit
      simpa [sourceAddUIntoVLayout, vValueWord, targetValueBit] using
        liftCoreBit_targetBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth rightBit)
          (WireAddress.littleEndianWire targetBit))
    (by
      intro workBit
      simpa only [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, coefficientCarryWorkBit,
        targetValueBit] using
        liftSharedBit_targetBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth
            (sourceCarryWorkPrefixIndex n workBit))
          (WireAddress.littleEndianWire targetBit))
    (coefficientAddCleanInput n counterWidth core target)
  simpa only [sourceSubUFromVStep, sourceSubUFromVGates,
    sourceAddUIntoVGates, targetValueBit_get,
    coefficientAddCleanInput] using h

/-! ## Compact compare-selected source subtraction -/

/-- A negative-control wrapper for an encoded gate list.  The surrounding X
gates invert the dispatch bit only while the clean-work controlled list is
executed. -/
private def compareFalseControlledListWithWorkGates
    {n counterWidth : Nat}
    (control work : EncodedBit (encoding n counterWidth))
    (gates : List (EncodedBit.GateSpec (encoding n counterWidth)))
    (hcontrol : ∀ gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  [EncodedBit.GateSpec.x control] ++
    EncodedBit.GateSpec.controlledListWithWorkGates control work gates
      hcontrol hwork hcontrolWork ++
    [EncodedBit.GateSpec.x control]

/-- A negative-control wrapper executes its source list when the dispatch bit
is false and its clean auxiliary work bit is false. -/
private lemma
    compareFalseControlledListWithWorkStep_eq_stepList_of_control_false
    {n counterWidth : Nat}
    (control work : EncodedBit (encoding n counterWidth))
    (gates : List (EncodedBit.GateSpec (encoding n counterWidth)))
    (hcontrol : ∀ gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (x : Registers n counterWidth)
    (hcontrolFalse : control.get x = false)
    (hworkClean : work.get x = false) :
    EncodedBit.GateSpec.stepList
        (compareFalseControlledListWithWorkGates control work gates hcontrol
          hwork hcontrolWork) x =
      EncodedBit.GateSpec.stepList gates x := by
  let y := control.flip x
  have hcontrolFlip : control.get y = true := by
    dsimp [y]
    rw [EncodedBit.get_flip_self, hcontrolFalse]
    rfl
  have hworkFlip : work.get y = false := by
    dsimp [y]
    rw [EncodedBit.get_flip_of_wire_ne control work hcontrolWork]
    exact hworkClean
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates control work gates
            hcontrol hwork hcontrolWork) y =
        EncodedBit.GateSpec.stepList gates y := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
        control work gates hcontrol hwork hcontrolWork y hcontrolFlip hworkFlip
  have hcomm :
      EncodedBit.GateSpec.stepList gates y =
        control.flip (EncodedBit.GateSpec.stepList gates x) := by
    dsimp [y]
    exact EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
      gates control hcontrol x
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates control work gates
        hcontrol hwork hcontrolWork ++ [EncodedBit.GateSpec.x control])
      (control.flip x) = EncodedBit.GateSpec.stepList gates x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [show control.flip x = y by rfl, hmiddle, hcomm]
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.flip_flip]

/-- A negative-control wrapper is a no-op when its dispatch bit is true. -/
private lemma
    compareFalseControlledListWithWorkStep_eq_self_of_control_true
    {n counterWidth : Nat}
    (control work : EncodedBit (encoding n counterWidth))
    (gates : List (EncodedBit.GateSpec (encoding n counterWidth)))
    (hcontrol : ∀ gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (x : Registers n counterWidth)
    (hcontrolTrue : control.get x = true) :
    EncodedBit.GateSpec.stepList
        (compareFalseControlledListWithWorkGates control work gates hcontrol
          hwork hcontrolWork) x = x := by
  let y := control.flip x
  have hcontrolFlip : control.get y = false := by
    dsimp [y]
    rw [EncodedBit.get_flip_self, hcontrolTrue]
    rfl
  have hmiddle :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates control work gates
            hcontrol hwork hcontrolWork) y = y := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        control work gates hcontrol hwork hcontrolWork y hcontrolFlip
  change EncodedBit.GateSpec.stepList
      (EncodedBit.GateSpec.controlledListWithWorkGates control work gates
        hcontrol hwork hcontrolWork ++ [EncodedBit.GateSpec.x control])
      (control.flip x) = x
  rw [EncodedBit.GateSpec.stepList_append]
  rw [show control.flip x = y by rfl, hmiddle]
  change control.flip y = x
  dsimp [y]
  exact EncodedBit.flip_flip control x

/-- The reverse `u := u - v` gate list is disjoint from the comparison
dispatch bit. -/
lemma sourceSubVFromUGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ sourceSubVFromUGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (compareBit n counterWidth) gate := by
  intro gate hmem
  have hforward : gate ∈ sourceAddVIntoUGates n counterWidth := by
    simpa [sourceSubVFromUGates] using hmem
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (sourceAddVIntoULayout n counterWidth) (compareBit n counterWidth)
    (fun i => by
      simpa [sourceAddVIntoULayout, vValueWord, compareBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (fun i => by
      simpa [sourceAddVIntoULayout, uValueWord, compareBit,
        RegisterBits.uValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (by
      simpa [sourceAddVIntoULayout, scratchABit, compareBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_scratchA_wire_ne n counterWidth)).symm)
    (fun j => by
      simpa [sourceAddVIntoULayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, compareBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sourceCarryWorkPrefixIndex n j)).symm)
    gate hforward

/-- The reverse `u := u - v` gate list is disjoint from `scratchB`, the
separate clean work bit used to control it. -/
lemma sourceSubVFromUGates_bitDisjoint_scratchB
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ sourceSubVFromUGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (scratchBBit n counterWidth) gate := by
  intro gate hmem
  have hforward : gate ∈ sourceAddVIntoUGates n counterWidth := by
    simpa [sourceSubVFromUGates] using hmem
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (sourceAddVIntoULayout n counterWidth) (scratchBBit n counterWidth)
    (fun i => by
      simpa [sourceAddVIntoULayout, vValueWord, scratchBBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (fun i => by
      simpa [sourceAddVIntoULayout, uValueWord, scratchBBit,
        RegisterBits.uValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (by
      simpa [sourceAddVIntoULayout, scratchABit, scratchBBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.scratchA_scratchB_wire_ne n counterWidth))
    (fun j => by
      simpa [sourceAddVIntoULayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, scratchBBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (sourceCarryWorkPrefixIndex n j)).symm)
    gate hforward

/-- The reverse `v := v - u` gate list is disjoint from the comparison
dispatch bit. -/
lemma sourceSubUFromVGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ sourceSubUFromVGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (compareBit n counterWidth) gate := by
  intro gate hmem
  have hforward : gate ∈ sourceAddUIntoVGates n counterWidth := by
    simpa [sourceSubUFromVGates] using hmem
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (sourceAddUIntoVLayout n counterWidth) (compareBit n counterWidth)
    (fun i => by
      simpa [sourceAddUIntoVLayout, uValueWord, compareBit,
        RegisterBits.uValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (fun i => by
      simpa [sourceAddUIntoVLayout, vValueWord, compareBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (by
      simpa [sourceAddUIntoVLayout, scratchABit, compareBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_scratchA_wire_ne n counterWidth)).symm)
    (fun j => by
      simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, compareBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sourceCarryWorkPrefixIndex n j)).symm)
    gate hforward

/-- The reverse `v := v - u` gate list is disjoint from `scratchB`, the
separate clean work bit used to control it. -/
lemma sourceSubUFromVGates_bitDisjoint_scratchB
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ sourceSubUFromVGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (scratchBBit n counterWidth) gate := by
  intro gate hmem
  have hforward : gate ∈ sourceAddUIntoVGates n counterWidth := by
    simpa [sourceSubUFromVGates] using hmem
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (sourceAddUIntoVLayout n counterWidth) (scratchBBit n counterWidth)
    (fun i => by
      simpa [sourceAddUIntoVLayout, uValueWord, scratchBBit,
        RegisterBits.uValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (fun i => by
      simpa [sourceAddUIntoVLayout, vValueWord, scratchBBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (by
      simpa [sourceAddUIntoVLayout, scratchABit, scratchBBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.scratchA_scratchB_wire_ne n counterWidth))
    (fun j => by
      simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, scratchBBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (sourceCarryWorkPrefixIndex n j)).symm)
    gate hforward

/-- The reverse compact source subtraction `u := u-v` stays within the
core/shared carrier and is disjoint from every public target bit. -/
lemma sourceSubVFromUGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ sourceSubVFromUGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hmem
  have hforward : gate ∈ sourceAddVIntoUGates n counterWidth := by
    simpa [sourceSubVFromUGates] using hmem
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (sourceAddVIntoULayout n counterWidth)
    (targetValueBit n counterWidth targetIndex)
    (fun i => by
      simpa [sourceAddVIntoULayout, vValueWord] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i) targetIndex)
    (fun i => by
      simpa [sourceAddVIntoULayout, uValueWord] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i) targetIndex)
    (by
      simpa [sourceAddVIntoULayout, scratchABit] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth) targetIndex)
    (fun j => by
      simpa [sourceAddVIntoULayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, coefficientCarryWorkBit] using
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth
            (sourceCarryWorkPrefixIndex n j)) targetIndex)
    gate hforward

/-- The reverse compact source subtraction `v := v-u` stays within the
core/shared carrier and is disjoint from every public target bit. -/
lemma sourceSubUFromVGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ sourceSubUFromVGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hmem
  have hforward : gate ∈ sourceAddUIntoVGates n counterWidth := by
    simpa [sourceSubUFromVGates] using hmem
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (sourceAddUIntoVLayout n counterWidth)
    (targetValueBit n counterWidth targetIndex)
    (fun i => by
      simpa [sourceAddUIntoVLayout, uValueWord] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i) targetIndex)
    (fun i => by
      simpa [sourceAddUIntoVLayout, vValueWord] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i) targetIndex)
    (by
      simpa [sourceAddUIntoVLayout, scratchABit] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth) targetIndex)
    (fun j => by
      simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit, coefficientCarryWorkBit] using
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth
            (sourceCarryWorkPrefixIndex n j)) targetIndex)
    gate hforward

/-- Compare-controlled `u := u - v` source subtraction.  `scratchB` is the
clean control-work bit; `scratchA` remains exclusively the VBE carry-in. -/
def compareControlledSubVFromUGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (compareBit n counterWidth) (scratchBBit n counterWidth)
    (sourceSubVFromUGates n counterWidth)
    (sourceSubVFromUGates_bitDisjoint_compare n counterWidth)
    (sourceSubVFromUGates_bitDisjoint_scratchB n counterWidth)
    (compareBit_scratchBBit_wire_ne n counterWidth)

/-- Compare-false-controlled `v := v - u` source subtraction. -/
def compareFalseControlledSubUFromVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  compareFalseControlledListWithWorkGates
    (compareBit n counterWidth) (scratchBBit n counterWidth)
    (sourceSubUFromVGates n counterWidth)
    (sourceSubUFromVGates_bitDisjoint_compare n counterWidth)
    (sourceSubUFromVGates_bitDisjoint_scratchB n counterWidth)
    (compareBit_scratchBBit_wire_ne n counterWidth)

/-- Folded compare-controlled `u := u - v` source subtraction. -/
def compareControlledSubVFromUStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (compareControlledSubVFromUGates n counterWidth)

/-- Folded compare-false-controlled `v := v - u` source subtraction. -/
def compareFalseControlledSubUFromVStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (compareFalseControlledSubUFromVGates n counterWidth)

/-- Circuit for compare-controlled `u := u - v` source subtraction. -/
def compareControlledSubVFromUProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compareControlledSubVFromUGates n counterWidth)

/-- Circuit for compare-false-controlled `v := v - u` source subtraction. -/
def compareFalseControlledSubUFromVProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compareFalseControlledSubUFromVGates n counterWidth)

/-- The compare-controlled `u := u - v` circuit realizes its folded step. -/
lemma compareControlledSubVFromU_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (compareControlledSubVFromUProgram n counterWidth) environment
      (compareControlledSubVFromUStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (compareControlledSubVFromUGates n counterWidth)

/-- The compare-false-controlled `v := v - u` circuit realizes its folded
step. -/
lemma compareFalseControlledSubUFromV_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (compareFalseControlledSubUFromVProgram n counterWidth) environment
      (compareFalseControlledSubUFromVStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (compareFalseControlledSubUFromVGates n counterWidth)

/-- A false compare bit disables the `u := u - v` source wrapper. -/
lemma compareControlledSubVFromUStep_eq_self_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false) :
    compareControlledSubVFromUStep n counterWidth x = x := by
  simpa [compareControlledSubVFromUStep, compareControlledSubVFromUGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (compareBit n counterWidth) (scratchBBit n counterWidth)
      (sourceSubVFromUGates n counterWidth)
      (sourceSubVFromUGates_bitDisjoint_compare n counterWidth)
      (sourceSubVFromUGates_bitDisjoint_scratchB n counterWidth)
      (compareBit_scratchBBit_wire_ne n counterWidth) x hcompare

/-- A true compare bit and clean `scratchB` activate `u := u - v`. -/
lemma compareControlledSubVFromUStep_eq_subVFromU_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hwork : (scratchBBit n counterWidth).get x = false) :
    compareControlledSubVFromUStep n counterWidth x =
      sourceSubVFromUStep n counterWidth x := by
  simpa [compareControlledSubVFromUStep, compareControlledSubVFromUGates,
    sourceSubVFromUStep, EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (compareBit n counterWidth) (scratchBBit n counterWidth)
      (sourceSubVFromUGates n counterWidth)
      (sourceSubVFromUGates_bitDisjoint_compare n counterWidth)
      (sourceSubVFromUGates_bitDisjoint_scratchB n counterWidth)
      (compareBit_scratchBBit_wire_ne n counterWidth) x hcompare hwork

/-- A false compare bit and clean `scratchB` activate `v := v - u`. -/
lemma compareFalseControlledSubUFromVStep_eq_subUFromV_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hwork : (scratchBBit n counterWidth).get x = false) :
    compareFalseControlledSubUFromVStep n counterWidth x =
      sourceSubUFromVStep n counterWidth x := by
  simpa [compareFalseControlledSubUFromVStep,
    compareFalseControlledSubUFromVGates, sourceSubUFromVStep] using
    compareFalseControlledListWithWorkStep_eq_stepList_of_control_false
      (compareBit n counterWidth) (scratchBBit n counterWidth)
      (sourceSubUFromVGates n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_compare n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_scratchB n counterWidth)
      (compareBit_scratchBBit_wire_ne n counterWidth) x hcompare hwork

/-- A true compare bit disables the negative-control `v := v - u` wrapper. -/
lemma compareFalseControlledSubUFromVStep_eq_self_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true) :
    compareFalseControlledSubUFromVStep n counterWidth x = x := by
  simpa [compareFalseControlledSubUFromVStep,
    compareFalseControlledSubUFromVGates] using
    compareFalseControlledListWithWorkStep_eq_self_of_control_true
      (compareBit n counterWidth) (scratchBBit n counterWidth)
      (sourceSubUFromVGates n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_compare n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_scratchB n counterWidth)
      (compareBit_scratchBBit_wire_ne n counterWidth) x hcompare

/-- The reverse source path `u := u - v` preserves the comparison dispatch
bit. -/
lemma sourceSubVFromUStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get (sourceSubVFromUStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  simpa only [compareBit_get, RegisterBits.compareBit_get] using
    sourceSubVFromUStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (fun bit => by
        simpa [RegisterBits.uValueBit] using
          RegisterBits.u_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)) x

/-- The reverse source path `v := v - u` preserves the comparison dispatch
bit. -/
lemma sourceSubUFromVStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get (sourceSubUFromVStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  simpa only [compareBit_get, RegisterBits.compareBit_get] using
    sourceSubUFromVStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (fun bit => by
        simpa [RegisterBits.vValueBit] using
          RegisterBits.v_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)) x

/-- The reverse source path `u := u - v` preserves the shared masked-route
control bit. -/
lemma sourceSubVFromUStep_get_control
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (controlBit n counterWidth).get (sourceSubVFromUStep n counterWidth x) =
      (controlBit n counterWidth).get x := by
  exact sourceSubVFromUStep_get_observed_of_u_work_ne n counterWidth
    (controlBit n counterWidth)
    (fun bit => by
      simpa [uValueWord, controlBit, RegisterBits.uValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth bit)
          (sharedControlBit n counterWidth))
    (fun bit => by
      simpa [sourceCarryWorkPrefixBit] using
        (controlBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (sourceCarryWorkPrefixIndex n bit)).symm) x

/-- The reverse source path `v := v - u` preserves the shared masked-route
control bit. -/
lemma sourceSubUFromVStep_get_control
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (controlBit n counterWidth).get (sourceSubUFromVStep n counterWidth x) =
      (controlBit n counterWidth).get x := by
  exact sourceSubUFromVStep_get_observed_of_v_work_ne n counterWidth
    (controlBit n counterWidth)
    (fun bit => by
      simpa [vValueWord, controlBit, RegisterBits.vValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth bit)
          (sharedControlBit n counterWidth))
    (fun bit => by
      simpa [sourceCarryWorkPrefixBit] using
        (controlBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (sourceCarryWorkPrefixIndex n bit)).symm) x

/-- The reverse source path `v := v - u` preserves the shared route bit. -/
lemma sourceSubUFromVStep_get_path
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (pathBit n counterWidth).get (sourceSubUFromVStep n counterWidth x) =
      (pathBit n counterWidth).get x := by
  exact sourceSubUFromVStep_get_observed_of_v_work_ne n counterWidth
    (pathBit n counterWidth)
    (fun bit => by
      simpa [vValueWord, pathBit, RegisterBits.vValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth bit)
          (sharedPathBit n counterWidth))
    (fun bit => by
      simpa [sourceCarryWorkPrefixBit] using
        (pathBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (sourceCarryWorkPrefixIndex n bit)).symm) x

/-- The reverse source path `u := u - v` preserves the shared route bit. -/
lemma sourceSubVFromUStep_get_path
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (pathBit n counterWidth).get (sourceSubVFromUStep n counterWidth x) =
      (pathBit n counterWidth).get x := by
  exact sourceSubVFromUStep_get_observed_of_u_work_ne n counterWidth
    (pathBit n counterWidth)
    (fun bit => by
      simpa [uValueWord, pathBit, RegisterBits.uValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth bit)
          (sharedPathBit n counterWidth))
    (fun bit => by
      simpa [sourceCarryWorkPrefixBit] using
        (pathBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (sourceCarryWorkPrefixIndex n bit)).symm) x

/-- Compare-selected compact source subtraction: compare=true selects
`u := u - v`, while compare=false selects `v := v - u`. -/
def compareSelectedSourceSubtractGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  compareControlledSubVFromUGates n counterWidth ++
    compareFalseControlledSubUFromVGates n counterWidth

/-- Circuit for compare-selected compact source subtraction. -/
def compareSelectedSourceSubtractProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compareSelectedSourceSubtractGates n counterWidth)

/-- Folded compare-selected compact source subtraction. -/
def compareSelectedSourceSubtractStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  fun x => compareFalseControlledSubUFromVStep n counterWidth
    (compareControlledSubVFromUStep n counterWidth x)

/-- The explicit selected-source gate list has the sequential selected-source
semantics. -/
lemma compareSelectedSourceSubtractStep_eq_gateList
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (compareSelectedSourceSubtractGates n counterWidth) x =
      compareSelectedSourceSubtractStep n counterWidth x := by
  rw [compareSelectedSourceSubtractGates,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- The compare-selected compact source-subtraction circuit realizes its
folded step. -/
lemma compareSelectedSourceSubtract_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (compareSelectedSourceSubtractProgram n counterWidth) environment
      (compareSelectedSourceSubtractStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (compareSelectedSourceSubtractGates n counterWidth)
    (compareSelectedSourceSubtractStep_eq_gateList n counterWidth)

/-- Under compare=true and clean `scratchB`, selected subtraction reduces to
the existing compact `u := u - v` schedule. -/
lemma compareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hwork : (scratchBBit n counterWidth).get x = false) :
    compareSelectedSourceSubtractStep n counterWidth x =
      sourceSubVFromUStep n counterWidth x := by
  have hfirst : compareControlledSubVFromUStep n counterWidth x =
      sourceSubVFromUStep n counterWidth x :=
    compareControlledSubVFromUStep_eq_subVFromU_of_compare_true
      n counterWidth x hcompare hwork
  have hcompareFirst :
      (compareBit n counterWidth).get
          (compareControlledSubVFromUStep n counterWidth x) = true := by
    rw [hfirst, sourceSubVFromUStep_get_compare]
    exact hcompare
  rw [compareSelectedSourceSubtractStep]
  rw [compareFalseControlledSubUFromVStep_eq_self_of_compare_true
    n counterWidth (compareControlledSubVFromUStep n counterWidth x)
    hcompareFirst]
  exact hfirst

/-- Under compare=false and clean `scratchB`, selected subtraction reduces to
the existing compact `v := v - u` schedule. -/
lemma compareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hwork : (scratchBBit n counterWidth).get x = false) :
    compareSelectedSourceSubtractStep n counterWidth x =
      sourceSubUFromVStep n counterWidth x := by
  have hfirst : compareControlledSubVFromUStep n counterWidth x = x :=
    compareControlledSubVFromUStep_eq_self_of_compare_false
      n counterWidth x hcompare
  rw [compareSelectedSourceSubtractStep, hfirst]
  exact compareFalseControlledSubUFromVStep_eq_subUFromV_of_compare_false
    n counterWidth x hcompare hwork

/-- Clean compact endpoint for the compare=true selected source branch. -/
lemma compareSelectedSourceSubtractStep_u_cleanEndpoint_of_compare_true
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (hcompare : core.compare = true)
    (hscratchA : core.scratchA = false) (hscratchB : core.scratchB = false) :
    (compareSelectedSourceSubtractStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.u =
        core.u - core.v := by
  rw [compareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
    n counterWidth (coefficientAddCleanInput n counterWidth core target)]
  · exact sourceSubVFromUStep_u_cleanEndpoint n counterWidth core target
      hscratchA
  · simpa only [compareBit_get, coefficientAddCleanInput] using hcompare
  · simpa only [scratchBBit_get, coefficientAddCleanInput] using hscratchB

/-- Clean compact endpoint for the compare=false selected source branch. -/
lemma compareSelectedSourceSubtractStep_v_cleanEndpoint_of_compare_false
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (hcompare : core.compare = false)
    (hscratchA : core.scratchA = false) (hscratchB : core.scratchB = false) :
    (compareSelectedSourceSubtractStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.v =
        core.v - core.u := by
  rw [compareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
    n counterWidth (coefficientAddCleanInput n counterWidth core target)]
  · exact sourceSubUFromVStep_v_cleanEndpoint n counterWidth core target
      hscratchA
  · simpa only [compareBit_get, coefficientAddCleanInput] using hcompare
  · simpa only [scratchBBit_get, coefficientAddCleanInput] using hscratchB

/-- Exact physical length of compare-selected compact source subtraction. -/
lemma compareSelectedSourceSubtractGates_length
    (n counterWidth : Nat) :
    (compareSelectedSourceSubtractGates n counterWidth).length =
      36 * (n - 1) + 4 * n + 2 := by
  simp only [compareSelectedSourceSubtractGates,
    compareControlledSubVFromUGates, compareFalseControlledSubUFromVGates,
    compareFalseControlledListWithWorkGates, List.length_append,
    List.length_cons, List.length_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_length_eq,
    sourceSubVFromUGates_length,
    sourceSubVFromUGates_toffoliMultiplicity_sum,
    sourceSubUFromVGates_length,
    sourceSubUFromVGates_toffoliMultiplicity_sum]
  omega

/-- Compare-selected compact source subtraction contains exactly two X gates. -/
lemma compareSelectedSourceSubtractGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedSourceSubtractGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp only [compareSelectedSourceSubtractGates,
    compareControlledSubVFromUGates, compareFalseControlledSubUFromVGates,
    compareFalseControlledListWithWorkGates, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum]
  rfl

/-- Compare-selected compact source subtraction contains no CNOT leaves. -/
lemma compareSelectedSourceSubtractGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedSourceSubtractGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [compareSelectedSourceSubtractGates,
    compareControlledSubVFromUGates, compareFalseControlledSubUFromVGates,
    compareFalseControlledListWithWorkGates, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    sourceSubVFromUGates_xMultiplicity_sum,
    sourceSubUFromVGates_xMultiplicity_sum]
  rfl

/-- Exact Toffoli coordinate of compare-selected compact source subtraction. -/
lemma compareSelectedSourceSubtractGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedSourceSubtractGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        4 * n + 36 * (n - 1) := by
  simp only [compareSelectedSourceSubtractGates,
    compareControlledSubVFromUGates, compareFalseControlledSubUFromVGates,
    compareFalseControlledListWithWorkGates, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    sourceSubVFromUGates_cnotMultiplicity_sum,
    sourceSubVFromUGates_toffoliMultiplicity_sum,
    sourceSubUFromVGates_cnotMultiplicity_sum,
    sourceSubUFromVGates_toffoliMultiplicity_sum,
    EncodedBit.GateSpec.toffoliMultiplicity_x]
  omega

/-- Reversing the selected-source gate list is a right inverse of its folded
compact step. -/
lemma compareSelectedSourceSubtractStep_reverse_identity
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (compareSelectedSourceSubtractGates n counterWidth).reverse
        (compareSelectedSourceSubtractStep n counterWidth x) = x := by
  rw [← compareSelectedSourceSubtractStep_eq_gateList n counterWidth x]
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (compareSelectedSourceSubtractGates n counterWidth) x

/-! ## Compact compare-selected coefficient addition -/

/-- The compact `r`-into-`s` gate list is disjoint from the comparison bit. -/
lemma coefficientAddRIntoSGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddRIntoSGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (compareBit n counterWidth) gate := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (coefficientAddRIntoSLayout n counterWidth) (compareBit n counterWidth)
    (fun i => by
      simpa [coefficientAddRIntoSLayout, rCoeffValueWord, rCoeffValueBit,
        compareBit, RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire i))).symm)
    (fun i => by
      simpa [coefficientAddRIntoSLayout, sCoeffValueWord, sCoeffValueBit,
        compareBit, RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire i))).symm)
    (by
      simpa [coefficientAddRIntoSLayout, coefficientCarryInBit, compareBit]
        using (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedCoefficientCarryInBit n counterWidth)).symm)
    (fun j => by
      simpa [coefficientAddRIntoSLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit, compareBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedCoefficientCarryWorkBit n counterWidth j)).symm)

/-- The compact `r`-into-`s` gate list is disjoint from clean `scratchA`. -/
lemma coefficientAddRIntoSGates_bitDisjoint_scratchA
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddRIntoSGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (scratchABit n counterWidth) gate := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (coefficientAddRIntoSLayout n counterWidth) (scratchABit n counterWidth)
    (fun i => by
      simpa [coefficientAddRIntoSLayout, rCoeffValueWord, rCoeffValueBit,
        scratchABit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (fun i => by
      simpa [coefficientAddRIntoSLayout, sCoeffValueWord, sCoeffValueBit,
        scratchABit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (by
      simpa [coefficientAddRIntoSLayout, coefficientCarryInBit, scratchABit]
        using (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedCoefficientCarryInBit n counterWidth)).symm)
    (fun j => by
      simpa [coefficientAddRIntoSLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit, scratchABit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedCoefficientCarryWorkBit n counterWidth j)).symm)

/-- The compact `s`-into-`r` gate list is disjoint from the comparison bit. -/
lemma coefficientAddSIntoRGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddSIntoRGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (compareBit n counterWidth) gate := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (coefficientAddSIntoRLayout n counterWidth) (compareBit n counterWidth)
    (fun i => by
      simpa [coefficientAddSIntoRLayout, sCoeffValueWord, sCoeffValueBit,
        compareBit, RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire i))).symm)
    (fun i => by
      simpa [coefficientAddSIntoRLayout, rCoeffValueWord, rCoeffValueBit,
        compareBit, RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire i))).symm)
    (by
      simpa [coefficientAddSIntoRLayout, coefficientCarryInBit, compareBit]
        using (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedCoefficientCarryInBit n counterWidth)).symm)
    (fun j => by
      simpa [coefficientAddSIntoRLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit, compareBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedCoefficientCarryWorkBit n counterWidth j)).symm)

/-- The compact `s`-into-`r` gate list is disjoint from clean `scratchA`. -/
lemma coefficientAddSIntoRGates_bitDisjoint_scratchA
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ coefficientAddSIntoRGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (scratchABit n counterWidth) gate := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (coefficientAddSIntoRLayout n counterWidth) (scratchABit n counterWidth)
    (fun i => by
      simpa [coefficientAddSIntoRLayout, sCoeffValueWord, sCoeffValueBit,
        scratchABit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (fun i => by
      simpa [coefficientAddSIntoRLayout, rCoeffValueWord, rCoeffValueBit,
        scratchABit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)))
    (by
      simpa [coefficientAddSIntoRLayout, coefficientCarryInBit, scratchABit]
        using (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedCoefficientCarryInBit n counterWidth)).symm)
    (fun j => by
      simpa [coefficientAddSIntoRLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit, scratchABit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedCoefficientCarryWorkBit n counterWidth j)).symm)

/-- The compact coefficient adder `s := s+r` is disjoint from every public
target bit. -/
lemma coefficientAddRIntoSGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ coefficientAddRIntoSGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (coefficientAddRIntoSLayout n counterWidth)
    (targetValueBit n counterWidth targetIndex)
    (fun i => by
      simpa [coefficientAddRIntoSLayout, rCoeffValueWord,
        rCoeffValueBit] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth i) targetIndex)
    (fun i => by
      simpa [coefficientAddRIntoSLayout, sCoeffValueWord,
        sCoeffValueBit] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.sCoeffValueBit n counterWidth i) targetIndex)
    (by
      simpa [coefficientAddRIntoSLayout, coefficientCarryInBit] using
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedCoefficientCarryInBit n counterWidth) targetIndex)
    (fun j => by
      simpa [coefficientAddRIntoSLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit] using
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth j) targetIndex)

/-- The compact coefficient adder `r := r+s` is disjoint from every public
target bit. -/
lemma coefficientAddSIntoRGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ coefficientAddSIntoRGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (coefficientAddSIntoRLayout n counterWidth)
    (targetValueBit n counterWidth targetIndex)
    (fun i => by
      simpa [coefficientAddSIntoRLayout, sCoeffValueWord,
        sCoeffValueBit] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.sCoeffValueBit n counterWidth i) targetIndex)
    (fun i => by
      simpa [coefficientAddSIntoRLayout, rCoeffValueWord,
        rCoeffValueBit] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth i) targetIndex)
    (by
      simpa [coefficientAddSIntoRLayout, coefficientCarryInBit] using
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedCoefficientCarryInBit n counterWidth) targetIndex)
    (fun j => by
      simpa [coefficientAddSIntoRLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit] using
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth j) targetIndex)

/-- Compare-controlled coefficient addition `r := r + s`. -/
def compareControlledAddSIntoRGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (compareBit n counterWidth) (scratchABit n counterWidth)
    (coefficientAddSIntoRGates n counterWidth)
    (coefficientAddSIntoRGates_bitDisjoint_compare n counterWidth)
    (coefficientAddSIntoRGates_bitDisjoint_scratchA n counterWidth)
    (compareBit_scratchABit_wire_ne n counterWidth)

/-- Compare-false-controlled coefficient addition `s := s + r`. -/
def compareFalseControlledAddRIntoSGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  compareFalseControlledListWithWorkGates
    (compareBit n counterWidth) (scratchABit n counterWidth)
    (coefficientAddRIntoSGates n counterWidth)
    (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
    (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
    (compareBit_scratchABit_wire_ne n counterWidth)

def compareControlledAddSIntoRStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (compareControlledAddSIntoRGates n counterWidth)

def compareFalseControlledAddRIntoSStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (compareFalseControlledAddRIntoSGates n counterWidth)

def compareControlledAddSIntoRProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compareControlledAddSIntoRGates n counterWidth)

def compareFalseControlledAddRIntoSProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compareFalseControlledAddRIntoSGates n counterWidth)

lemma compareControlledAddSIntoR_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (compareControlledAddSIntoRProgram n counterWidth) environment
      (compareControlledAddSIntoRStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (compareControlledAddSIntoRGates n counterWidth)

lemma compareFalseControlledAddRIntoS_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (compareFalseControlledAddRIntoSProgram n counterWidth) environment
      (compareFalseControlledAddRIntoSStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (compareFalseControlledAddRIntoSGates n counterWidth)

lemma compareControlledAddSIntoRStep_eq_self_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false) :
    compareControlledAddSIntoRStep n counterWidth x = x := by
  simpa [compareControlledAddSIntoRStep, compareControlledAddSIntoRGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (compareBit n counterWidth) (scratchABit n counterWidth)
      (coefficientAddSIntoRGates n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_compare n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_scratchA n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth) x hcompare

lemma compareControlledAddSIntoRStep_eq_addSIntoR_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hwork : (scratchABit n counterWidth).get x = false) :
    compareControlledAddSIntoRStep n counterWidth x =
      coefficientAddSIntoRStep n counterWidth x := by
  simpa [compareControlledAddSIntoRStep, compareControlledAddSIntoRGates,
    coefficientAddSIntoRStep, coefficientAddSIntoRGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (compareBit n counterWidth) (scratchABit n counterWidth)
      (coefficientAddSIntoRGates n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_compare n counterWidth)
      (coefficientAddSIntoRGates_bitDisjoint_scratchA n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth) x hcompare hwork

lemma compareFalseControlledAddRIntoSStep_eq_addRIntoS_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hwork : (scratchABit n counterWidth).get x = false) :
    compareFalseControlledAddRIntoSStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth x := by
  simpa [compareFalseControlledAddRIntoSStep,
    compareFalseControlledAddRIntoSGates, coefficientAddRIntoSStep,
    coefficientAddRIntoSGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using
    compareFalseControlledListWithWorkStep_eq_stepList_of_control_false
      (compareBit n counterWidth) (scratchABit n counterWidth)
      (coefficientAddRIntoSGates n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth) x hcompare hwork

lemma compareFalseControlledAddRIntoSStep_eq_self_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true) :
    compareFalseControlledAddRIntoSStep n counterWidth x = x := by
  simpa [compareFalseControlledAddRIntoSStep,
    compareFalseControlledAddRIntoSGates] using
    compareFalseControlledListWithWorkStep_eq_self_of_control_true
      (compareBit n counterWidth) (scratchABit n counterWidth)
      (coefficientAddRIntoSGates n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_compare n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth) x hcompare

lemma coefficientAddRIntoSStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get (coefficientAddRIntoSStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  exact coefficientAddRIntoSStep_get_observed_of_right_work_ne n counterWidth
    (compareBit n counterWidth)
    (fun bit => by
      simpa [sCoeffValueBit, compareBit, RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (fun bit => by
      simpa [coefficientCarryWorkBit, compareBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedCoefficientCarryWorkBit n counterWidth bit)).symm) x

lemma coefficientAddSIntoRStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get (coefficientAddSIntoRStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  exact coefficientAddSIntoRStep_get_observed_of_right_work_ne n counterWidth
    (compareBit n counterWidth)
    (fun bit => by
      simpa [rCoeffValueBit, compareBit, RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (fun bit => by
      simpa [coefficientCarryWorkBit, compareBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedCoefficientCarryWorkBit n counterWidth bit)).symm) x

/-- The compact `s`-into-`r` addition preserves the shared masked-route
control bit. -/
lemma coefficientAddSIntoRStep_get_control
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (controlBit n counterWidth).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (controlBit n counterWidth).get x := by
  exact coefficientAddSIntoRStep_get_observed_of_right_work_ne n counterWidth
    (controlBit n counterWidth)
    (fun bit => by
      simpa [rCoeffValueBit, controlBit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth bit)
          (sharedControlBit n counterWidth))
    (fun bit => by
      simpa [coefficientCarryWorkBit, controlBit] using
        (controlBit_coefficientCarryWorkBit_wire_ne
          n counterWidth bit).symm) x

/-- The compact `r`-into-`s` addition preserves the shared route bit. -/
lemma coefficientAddRIntoSStep_get_path
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (pathBit n counterWidth).get
        (coefficientAddRIntoSStep n counterWidth x) =
      (pathBit n counterWidth).get x := by
  exact coefficientAddRIntoSStep_get_observed_of_right_work_ne n counterWidth
    (pathBit n counterWidth)
    (fun bit => by
      simpa [sCoeffValueBit, pathBit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.sCoeffValueBit n counterWidth bit)
          (sharedPathBit n counterWidth))
    (fun bit => by
      simpa [coefficientCarryWorkBit, pathBit] using
        (pathBit_coefficientCarryWorkBit_wire_ne n counterWidth bit).symm) x

/-- The compact `s`-into-`r` addition preserves the shared route bit. -/
lemma coefficientAddSIntoRStep_get_path
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (pathBit n counterWidth).get
        (coefficientAddSIntoRStep n counterWidth x) =
      (pathBit n counterWidth).get x := by
  exact coefficientAddSIntoRStep_get_observed_of_right_work_ne n counterWidth
    (pathBit n counterWidth)
    (fun bit => by
      simpa [rCoeffValueBit, pathBit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth bit)
          (sharedPathBit n counterWidth))
    (fun bit => by
      simpa [coefficientCarryWorkBit, pathBit] using
        (pathBit_coefficientCarryWorkBit_wire_ne n counterWidth bit).symm) x

/-- Compare-selected coefficient addition for the compact odd branch. -/
def compareSelectedCoefficientAddGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  compareControlledAddSIntoRGates n counterWidth ++
    compareFalseControlledAddRIntoSGates n counterWidth

def compareSelectedCoefficientAddProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compareSelectedCoefficientAddGates n counterWidth)

def compareSelectedCoefficientAddStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  fun x => compareFalseControlledAddRIntoSStep n counterWidth
    (compareControlledAddSIntoRStep n counterWidth x)

lemma compareSelectedCoefficientAddStep_eq_gateList
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (compareSelectedCoefficientAddGates n counterWidth) x =
      compareSelectedCoefficientAddStep n counterWidth x := by
  rw [compareSelectedCoefficientAddGates,
    EncodedBit.GateSpec.stepList_append]
  rfl

lemma compareSelectedCoefficientAdd_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (compareSelectedCoefficientAddProgram n counterWidth) environment
      (compareSelectedCoefficientAddStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (compareSelectedCoefficientAddGates n counterWidth)
    (compareSelectedCoefficientAddStep_eq_gateList n counterWidth)

lemma compareSelectedCoefficientAddStep_eq_addSIntoR_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hwork : (scratchABit n counterWidth).get x = false) :
    compareSelectedCoefficientAddStep n counterWidth x =
      coefficientAddSIntoRStep n counterWidth x := by
  have hfirst := compareControlledAddSIntoRStep_eq_addSIntoR_of_compare_true
    n counterWidth x hcompare hwork
  have hcompareFirst :
      (compareBit n counterWidth).get
          (compareControlledAddSIntoRStep n counterWidth x) = true := by
    rw [hfirst, coefficientAddSIntoRStep_get_compare]
    exact hcompare
  rw [compareSelectedCoefficientAddStep]
  rw [compareFalseControlledAddRIntoSStep_eq_self_of_compare_true
    n counterWidth (compareControlledAddSIntoRStep n counterWidth x)
    hcompareFirst]
  exact hfirst

lemma compareSelectedCoefficientAddStep_eq_addRIntoS_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hwork : (scratchABit n counterWidth).get x = false) :
    compareSelectedCoefficientAddStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth x := by
  have hfirst := compareControlledAddSIntoRStep_eq_self_of_compare_false
    n counterWidth x hcompare
  rw [compareSelectedCoefficientAddStep, hfirst]
  exact compareFalseControlledAddRIntoSStep_eq_addRIntoS_of_compare_false
    n counterWidth x hcompare hwork

lemma compareSelectedCoefficientAddGates_length (n counterWidth : Nat) :
    (compareSelectedCoefficientAddGates n counterWidth).length = 40 * n + 6 := by
  simp only [compareSelectedCoefficientAddGates,
    compareControlledAddSIntoRGates, compareFalseControlledAddRIntoSGates,
    compareFalseControlledListWithWorkGates, List.length_append,
    List.length_cons, List.length_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_length_eq,
    coefficientAddSIntoRGates_length,
    coefficientAddSIntoRGates_toffoliMultiplicity_sum,
    coefficientAddRIntoSGates_length,
    coefficientAddRIntoSGates_toffoliMultiplicity_sum]
  omega

lemma compareSelectedCoefficientAddGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedCoefficientAddGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp only [compareSelectedCoefficientAddGates,
    compareControlledAddSIntoRGates, compareFalseControlledAddRIntoSGates,
    compareFalseControlledListWithWorkGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum]
  rfl

lemma compareSelectedCoefficientAddGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedCoefficientAddGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [compareSelectedCoefficientAddGates,
    compareControlledAddSIntoRGates, compareFalseControlledAddRIntoSGates,
    compareFalseControlledListWithWorkGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    coefficientAddSIntoRGates_xMultiplicity_sum,
    coefficientAddRIntoSGates_xMultiplicity_sum]
  rfl

lemma compareSelectedCoefficientAddGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedCoefficientAddGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 40 * n + 4 := by
  simp only [compareSelectedCoefficientAddGates,
    compareControlledAddSIntoRGates, compareFalseControlledAddRIntoSGates,
    compareFalseControlledListWithWorkGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    coefficientAddSIntoRGates_cnotMultiplicity_sum,
    coefficientAddSIntoRGates_toffoliMultiplicity_sum,
    coefficientAddRIntoSGates_cnotMultiplicity_sum,
    coefficientAddRIntoSGates_toffoliMultiplicity_sum,
    EncodedBit.GateSpec.toffoliMultiplicity_x]
  omega

lemma compareSelectedCoefficientAddStep_reverse_identity
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (compareSelectedCoefficientAddGates n counterWidth).reverse
        (compareSelectedCoefficientAddStep n counterWidth x) = x := by
  rw [← compareSelectedCoefficientAddStep_eq_gateList n counterWidth x]
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (compareSelectedCoefficientAddGates n counterWidth) x

/-! ## Compact compare-selected odd data path -/

def compareSelectedOddDataPathGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  compareSelectedSourceSubtractGates n counterWidth ++
    compareSelectedCoefficientAddGates n counterWidth

def compareSelectedOddDataPathProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compareSelectedOddDataPathGates n counterWidth)

def compareSelectedOddDataPathStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  fun x => compareSelectedCoefficientAddStep n counterWidth
    (compareSelectedSourceSubtractStep n counterWidth x)

lemma compareSelectedOddDataPathStep_eq_gateList
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (compareSelectedOddDataPathGates n counterWidth) x =
      compareSelectedOddDataPathStep n counterWidth x := by
  rw [compareSelectedOddDataPathGates,
    EncodedBit.GateSpec.stepList_append,
    compareSelectedSourceSubtractStep_eq_gateList,
    compareSelectedCoefficientAddStep_eq_gateList]
  rfl

lemma compareSelectedOddDataPath_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (compareSelectedOddDataPathProgram n counterWidth) environment
      (compareSelectedOddDataPathStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (compareSelectedOddDataPathGates n counterWidth)
    (compareSelectedOddDataPathStep_eq_gateList n counterWidth)

lemma compareSelectedOddDataPathStep_eq_true_branch
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    compareSelectedOddDataPathStep n counterWidth x =
      coefficientAddSIntoRStep n counterWidth
        (sourceSubVFromUStep n counterWidth x) := by
  have hsource := compareSelectedSourceSubtractStep_eq_subVFromU_of_compare_true
    n counterWidth x hcompare hscratchB
  rw [compareSelectedOddDataPathStep, hsource]
  apply compareSelectedCoefficientAddStep_eq_addSIntoR_of_compare_true
  · rw [sourceSubVFromUStep_get_compare]
    exact hcompare
  · simpa only [scratchABit_get] using
      (sourceSubVFromUStep_get_scratchA n counterWidth x).trans hscratchA

lemma compareSelectedOddDataPathStep_eq_false_branch
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    compareSelectedOddDataPathStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth
        (sourceSubUFromVStep n counterWidth x) := by
  have hsource := compareSelectedSourceSubtractStep_eq_subUFromV_of_compare_false
    n counterWidth x hcompare hscratchB
  rw [compareSelectedOddDataPathStep, hsource]
  apply compareSelectedCoefficientAddStep_eq_addRIntoS_of_compare_false
  · rw [sourceSubUFromVStep_get_compare]
    exact hcompare
  · simpa only [scratchABit_get] using
      (sourceSubUFromVStep_get_scratchA n counterWidth x).trans hscratchA

/-- Either selected odd data path returns the sole VBE carry bank to its clean
value.  The source subtraction and coefficient addition reuse the same bank
sequentially; no second carry object is assumed. -/
lemma compareSelectedOddDataPathStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  cases hcompare : (compareBit n counterWidth).get x
  · rw [compareSelectedOddDataPathStep_eq_false_branch
      n counterWidth x hcompare hscratchA hscratchB]
    let subtracted := sourceSubUFromVStep n counterWidth x
    have hbank : subtracted.shared.coefficientAdder = cleanCoeffAdderWork n :=
      sourceSubUFromVStep_coefficientAdder_cleanEndpoint_of_clean
        n counterWidth x hcarry hwork
    apply coefficientAddRIntoSStep_coefficientAdder_cleanEndpoint_of_clean
    · rw [coefficientCarryInBit_get, hbank]
      rfl
    · intro bit
      change (BinaryLabelEncoding.finIdentityBit n bit).get
        subtracted.shared.coefficientAdder.2 = false
      rw [hbank]
      exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit
  · rw [compareSelectedOddDataPathStep_eq_true_branch
      n counterWidth x hcompare hscratchA hscratchB]
    let subtracted := sourceSubVFromUStep n counterWidth x
    have hbank : subtracted.shared.coefficientAdder = cleanCoeffAdderWork n :=
      sourceSubVFromUStep_coefficientAdder_cleanEndpoint_of_clean
        n counterWidth x hcarry hwork
    apply coefficientAddSIntoRStep_coefficientAdder_cleanEndpoint_of_clean
    · rw [coefficientCarryInBit_get, hbank]
      rfl
    · intro bit
      change (BinaryLabelEncoding.finIdentityBit n bit).get
        subtracted.shared.coefficientAdder.2 = false
      rw [hbank]
      exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit

/-- The complete selected odd data path preserves every observation outside
the four arithmetic data words and the sole reusable VBE carry bank. -/
lemma compareSelectedOddDataPathStep_get_observed_of_words_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hu : ∀ bit : Fin n,
      ((uValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hv : ∀ bit : Fin n,
      ((vValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hr : ∀ bit : Fin (n + 1),
      (rCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (hs : ∀ bit : Fin (n + 1),
      (sCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    observed.get (compareSelectedOddDataPathStep n counterWidth x) =
      observed.get x := by
  cases hcompare : (compareBit n counterWidth).get x
  · rw [compareSelectedOddDataPathStep_eq_false_branch
      n counterWidth x hcompare hscratchA hscratchB]
    rw [coefficientAddRIntoSStep_get_observed_of_right_work_ne
      n counterWidth observed hs hwork]
    exact sourceSubUFromVStep_get_observed_of_v_work_ne
      n counterWidth observed hv (by
        intro bit
        simpa [sourceCarryWorkPrefixBit] using
          hwork (sourceCarryWorkPrefixIndex n bit)) x
  · rw [compareSelectedOddDataPathStep_eq_true_branch
      n counterWidth x hcompare hscratchA hscratchB]
    rw [coefficientAddSIntoRStep_get_observed_of_right_work_ne
      n counterWidth observed hr hwork]
    exact sourceSubVFromUStep_get_observed_of_u_work_ne
      n counterWidth observed hu (by
        intro bit
        simpa [sourceCarryWorkPrefixBit] using
          hwork (sourceCarryWorkPrefixIndex n bit)) x

/-- A core readout outside `r` is preserved by the compact `s`-into-`r`
coefficient adder. -/
lemma coefficientAddSIntoRStep_get_coreBit_of_disjoint
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hright : ∀ bit : Fin (n + 1),
      (RegisterBits.rCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (coefficientAddSIntoRStep n counterWidth x).core =
      observed.get x.core := by
  have h := coefficientAddSIntoRStep_get_observed_of_right_work_ne
    n counterWidth (liftCoreBit n counterWidth observed)
    (fun bit => by
      simpa [coefficientAddSIntoRLayout, rCoeffValueWord,
        rCoeffValueBit] using liftCoreBit_wire_ne n counterWidth (hright bit))
    (fun bit => by
      simpa [coefficientCarryWorkBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth observed
          (sharedCoefficientCarryWorkBit n counterWidth bit)).symm) x
  simpa only [liftCoreBit_get] using h

/-- A core readout outside `s` is preserved by the compact `r`-into-`s`
coefficient adder. -/
lemma coefficientAddRIntoSStep_get_coreBit_of_disjoint
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hright : ∀ bit : Fin (n + 1),
      (RegisterBits.sCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (coefficientAddRIntoSStep n counterWidth x).core =
      observed.get x.core := by
  have h := coefficientAddRIntoSStep_get_observed_of_right_work_ne
    n counterWidth (liftCoreBit n counterWidth observed)
    (fun bit => by
      simpa [coefficientAddRIntoSLayout, sCoeffValueWord,
        sCoeffValueBit] using liftCoreBit_wire_ne n counterWidth (hright bit))
    (fun bit => by
      simpa [coefficientCarryWorkBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth observed
          (sharedCoefficientCarryWorkBit n counterWidth bit)).symm) x
  simpa only [liftCoreBit_get] using h

/-- On the compare-true odd branch, every core bit outside the updated `u`
and `r` words is physically preserved. -/
lemma compareSelectedOddDataPathStep_get_coreBit_of_compare_true
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hu : ∀ bit : Fin n,
      (RegisterBits.uValueBit n counterWidth bit).wire ≠ observed.wire)
    (hr : ∀ bit : Fin (n + 1),
      (RegisterBits.rCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    observed.get (compareSelectedOddDataPathStep n counterWidth x).core =
      observed.get x.core := by
  rw [compareSelectedOddDataPathStep_eq_true_branch n counterWidth x
    hcompare hscratchA hscratchB]
  rw [coefficientAddSIntoRStep_get_coreBit_of_disjoint
    n counterWidth observed hr]
  exact sourceSubVFromUStep_get_coreBit_of_disjoint
    n counterWidth observed hu x

/-- On the compare-false odd branch, every core bit outside the updated `v`
and `s` words is physically preserved. -/
lemma compareSelectedOddDataPathStep_get_coreBit_of_compare_false
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hv : ∀ bit : Fin n,
      (RegisterBits.vValueBit n counterWidth bit).wire ≠ observed.wire)
    (hs : ∀ bit : Fin (n + 1),
      (RegisterBits.sCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    observed.get (compareSelectedOddDataPathStep n counterWidth x).core =
      observed.get x.core := by
  rw [compareSelectedOddDataPathStep_eq_false_branch n counterWidth x
    hcompare hscratchA hscratchB]
  rw [coefficientAddRIntoSStep_get_coreBit_of_disjoint
    n counterWidth observed hs]
  exact sourceSubUFromVStep_get_coreBit_of_disjoint
    n counterWidth observed hv x

/-- A core observation disjoint from both possible update pairs is preserved
by the selected odd data path on a clean scratch boundary. -/
lemma compareSelectedOddDataPathStep_get_coreBit_of_disjoint_clean
    (n counterWidth : Nat)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hu : ∀ bit : Fin n,
      (RegisterBits.uValueBit n counterWidth bit).wire ≠ observed.wire)
    (hv : ∀ bit : Fin n,
      (RegisterBits.vValueBit n counterWidth bit).wire ≠ observed.wire)
    (hr : ∀ bit : Fin (n + 1),
      (RegisterBits.rCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (hs : ∀ bit : Fin (n + 1),
      (RegisterBits.sCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    observed.get (compareSelectedOddDataPathStep n counterWidth x).core =
      observed.get x.core := by
  cases hcompare : (compareBit n counterWidth).get x
  · exact compareSelectedOddDataPathStep_get_coreBit_of_compare_false
      n counterWidth observed hv hs x hcompare hscratchA hscratchB
  · exact compareSelectedOddDataPathStep_get_coreBit_of_compare_true
      n counterWidth observed hu hr x hcompare hscratchA hscratchB

/-- The selected odd data path preserves the shared route bit on the clean
scratch boundary used by the round circuit. -/
lemma compareSelectedOddDataPathStep_get_path_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    (pathBit n counterWidth).get
        (compareSelectedOddDataPathStep n counterWidth x) =
      (pathBit n counterWidth).get x := by
  cases hcompare : (compareBit n counterWidth).get x
  · rw [compareSelectedOddDataPathStep_eq_false_branch
      n counterWidth x hcompare hscratchA hscratchB,
      coefficientAddRIntoSStep_get_path,
      sourceSubUFromVStep_get_path]
  · rw [compareSelectedOddDataPathStep_eq_true_branch
      n counterWidth x hcompare hscratchA hscratchB,
      coefficientAddSIntoRStep_get_path,
      sourceSubVFromUStep_get_path]

/-- On any clean reusable-work boundary, the selected `uGreater` odd path
writes `r := r+s` bitwise. -/
lemma compareSelectedOddDataPathStep_get_rCoeff_add_of_compare_true_cleanWork
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (bit : Fin (n + 1))
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.rCoeff.val.testBit
        bit.val =
      (x.core.rCoeff + x.core.sCoeff).val.testBit bit.val := by
  let subtracted := sourceSubVFromUStep n counterWidth x
  have hroute : compareSelectedOddDataPathStep n counterWidth x =
      coefficientAddSIntoRStep n counterWidth subtracted :=
    compareSelectedOddDataPathStep_eq_true_branch n counterWidth x
      hcompare hscratchA hscratchB
  rw [hroute]
  have hbank : subtracted.shared.coefficientAdder = cleanCoeffAdderWork n := by
    dsimp [subtracted]
    exact sourceSubVFromUStep_coefficientAdder_cleanEndpoint_of_clean
      n counterWidth x hcarry hwork
  have hcarrySub :
      (coefficientCarryInBit n counterWidth).get subtracted = false := by
    rw [coefficientCarryInBit_get, hbank]
    rfl
  have hworkSub : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get subtracted = false := by
    intro workBit
    change (BinaryLabelEncoding.finIdentityBit n workBit).get
      subtracted.shared.coefficientAdder.2 = false
    rw [hbank]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n workBit
  have hsCoeff : ∀ coeffBit : Fin (n + 1),
      (sCoeffValueBit n counterWidth coeffBit).get subtracted =
        x.core.sCoeff.val.testBit coeffBit.val := by
    intro coeffBit
    change (RegisterBits.sCoeffValueBit n counterWidth coeffBit).get
      subtracted.core = x.core.sCoeff.val.testBit coeffBit.val
    rw [show x.core.sCoeff.val.testBit coeffBit.val =
        (RegisterBits.sCoeffValueBit n counterWidth coeffBit).get x.core by
      exact (RegisterBits.sCoeffValueBit_get
        n counterWidth coeffBit x.core).symm]
    dsimp [subtracted]
    exact sourceSubVFromUStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.sCoeffValueBit n counterWidth coeffBit)
      (fun sourceBit => by
        simpa [RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
          RegisterBits.u_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire coeffBit)) x
  have hrCoeff : ∀ coeffBit : Fin (n + 1),
      (rCoeffValueBit n counterWidth coeffBit).get subtracted =
        x.core.rCoeff.val.testBit coeffBit.val := by
    intro coeffBit
    change (RegisterBits.rCoeffValueBit n counterWidth coeffBit).get
      subtracted.core = x.core.rCoeff.val.testBit coeffBit.val
    rw [show x.core.rCoeff.val.testBit coeffBit.val =
        (RegisterBits.rCoeffValueBit n counterWidth coeffBit).get x.core by
      exact (RegisterBits.rCoeffValueBit_get
        n counterWidth coeffBit x.core).symm]
    dsimp [subtracted]
    exact sourceSubVFromUStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.rCoeffValueBit n counterWidth coeffBit)
      (fun sourceBit => by
        simpa [RegisterBits.uValueBit, RegisterBits.rCoeffValueBit] using
          RegisterBits.u_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire coeffBit)) x
  have hadd := coefficientAdd_cleanStep_get_right_add_testBit_of_clean
    n counterWidth (coefficientAddSIntoRLayout n counterWidth)
    x.core.sCoeff x.core.rCoeff bit subtracted hsCoeff hrCoeff hcarrySub hworkSub
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    rCoeffValueWord] using hadd

/-- On any clean reusable-work boundary, the selected `vLe` odd path writes
`s := s+r` bitwise. -/
lemma compareSelectedOddDataPathStep_get_sCoeff_add_of_compare_false_cleanWork
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (bit : Fin (n + 1))
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.sCoeff.val.testBit
        bit.val =
      (x.core.sCoeff + x.core.rCoeff).val.testBit bit.val := by
  let subtracted := sourceSubUFromVStep n counterWidth x
  have hroute : compareSelectedOddDataPathStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth subtracted :=
    compareSelectedOddDataPathStep_eq_false_branch n counterWidth x
      hcompare hscratchA hscratchB
  rw [hroute]
  have hbank : subtracted.shared.coefficientAdder = cleanCoeffAdderWork n := by
    dsimp [subtracted]
    exact sourceSubUFromVStep_coefficientAdder_cleanEndpoint_of_clean
      n counterWidth x hcarry hwork
  have hcarrySub :
      (coefficientCarryInBit n counterWidth).get subtracted = false := by
    rw [coefficientCarryInBit_get, hbank]
    rfl
  have hworkSub : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get subtracted = false := by
    intro workBit
    change (BinaryLabelEncoding.finIdentityBit n workBit).get
      subtracted.shared.coefficientAdder.2 = false
    rw [hbank]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n workBit
  have hrCoeff : ∀ coeffBit : Fin (n + 1),
      (rCoeffValueBit n counterWidth coeffBit).get subtracted =
        x.core.rCoeff.val.testBit coeffBit.val := by
    intro coeffBit
    change (RegisterBits.rCoeffValueBit n counterWidth coeffBit).get
      subtracted.core = x.core.rCoeff.val.testBit coeffBit.val
    rw [show x.core.rCoeff.val.testBit coeffBit.val =
        (RegisterBits.rCoeffValueBit n counterWidth coeffBit).get x.core by
      exact (RegisterBits.rCoeffValueBit_get
        n counterWidth coeffBit x.core).symm]
    dsimp [subtracted]
    exact sourceSubUFromVStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.rCoeffValueBit n counterWidth coeffBit)
      (fun sourceBit => by
        simpa [RegisterBits.vValueBit, RegisterBits.rCoeffValueBit] using
          RegisterBits.v_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire coeffBit)) x
  have hsCoeff : ∀ coeffBit : Fin (n + 1),
      (sCoeffValueBit n counterWidth coeffBit).get subtracted =
        x.core.sCoeff.val.testBit coeffBit.val := by
    intro coeffBit
    change (RegisterBits.sCoeffValueBit n counterWidth coeffBit).get
      subtracted.core = x.core.sCoeff.val.testBit coeffBit.val
    rw [show x.core.sCoeff.val.testBit coeffBit.val =
        (RegisterBits.sCoeffValueBit n counterWidth coeffBit).get x.core by
      exact (RegisterBits.sCoeffValueBit_get
        n counterWidth coeffBit x.core).symm]
    dsimp [subtracted]
    exact sourceSubUFromVStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.sCoeffValueBit n counterWidth coeffBit)
      (fun sourceBit => by
        simpa [RegisterBits.vValueBit, RegisterBits.sCoeffValueBit] using
          RegisterBits.v_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire coeffBit)) x
  have hadd := coefficientAdd_cleanStep_get_right_add_testBit_of_clean
    n counterWidth (coefficientAddRIntoSLayout n counterWidth)
    x.core.rCoeff x.core.sCoeff bit subtracted hrCoeff hsCoeff hcarrySub hworkSub
  simpa [coefficientAddRIntoSStep, coefficientAddRIntoSLayout,
    sCoeffValueWord] using hadd

/-- On an arbitrary compact carrier, the selected `vLe` odd arithmetic leaves
`r` unchanged. -/
lemma compareSelectedOddDataPathStep_get_rCoeff_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (bit : Fin (n + 1))
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.rCoeff.val.testBit
        bit.val = x.core.rCoeff.val.testBit bit.val := by
  let subtracted := sourceSubUFromVStep n counterWidth x
  have hroute : compareSelectedOddDataPathStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth subtracted :=
    compareSelectedOddDataPathStep_eq_false_branch n counterWidth x
      hcompare hscratchA hscratchB
  rw [hroute]
  calc
    (coefficientAddRIntoSStep n counterWidth subtracted).core.rCoeff.val.testBit
        bit.val =
        (rCoeffValueBit n counterWidth bit).get
          (coefficientAddRIntoSStep n counterWidth subtracted) := by
      symm
      exact rCoeffValueBit_get n counterWidth bit _
    _ = (rCoeffValueBit n counterWidth bit).get subtracted :=
      coefficientAddRIntoSStep_get_rCoeffValueBit
        n counterWidth bit subtracted
    _ = (RegisterBits.rCoeffValueBit n counterWidth bit).get x.core := by
      dsimp [subtracted]
      exact sourceSubUFromVStep_get_coreBit_of_disjoint n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (fun sourceBit => by
          simpa [RegisterBits.vValueBit, RegisterBits.rCoeffValueBit] using
            RegisterBits.v_rCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire sourceBit)
              (WireAddress.littleEndianWire bit)) x
    _ = x.core.rCoeff.val.testBit bit.val :=
      RegisterBits.rCoeffValueBit_get n counterWidth bit x.core

/-- The selected compare-true odd path writes `u := u-v` as a complete word. -/
lemma compareSelectedOddDataPathStep_core_u_of_compare_true_cleanWork
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hwork : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.u =
      x.core.u - x.core.v := by
  let subtracted := sourceSubVFromUStep n counterWidth x
  have hroute : compareSelectedOddDataPathStep n counterWidth x =
      coefficientAddSIntoRStep n counterWidth subtracted :=
    compareSelectedOddDataPathStep_eq_true_branch n counterWidth x
      hcompare hscratchA hscratchB
  rw [hroute]
  calc
    (coefficientAddSIntoRStep n counterWidth subtracted).core.u =
        subtracted.core.u := by
      apply word_eq_of_testBit_eq
      intro bit
      have h := coefficientAddSIntoRStep_get_coreBit_of_disjoint
        n counterWidth (RegisterBits.uValueBit n counterWidth bit)
        (fun coeffBit => by
          simpa [RegisterBits.uValueBit, RegisterBits.rCoeffValueBit] using
            (RegisterBits.u_rCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)
              (WireAddress.littleEndianWire coeffBit)).symm)
        subtracted
      simpa only [RegisterBits.uValueBit_get] using h
    _ = x.core.u - x.core.v :=
      sourceSubVFromUStep_get_u_sub_of_clean n counterWidth x hscratchA
        (fun workBit => by
          simpa [sourceCarryWorkPrefixBit] using
            hwork (sourceCarryWorkPrefixIndex n workBit))

/-- The selected compare-true odd path preserves the complete `v` word. -/
lemma compareSelectedOddDataPathStep_core_v_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := compareSelectedOddDataPathStep_get_coreBit_of_compare_true
    n counterWidth (RegisterBits.vValueBit n counterWidth bit)
    (fun sourceBit => by
      simpa [RegisterBits.uValueBit, RegisterBits.vValueBit] using
        RegisterBits.u_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire sourceBit)
          (WireAddress.littleEndianWire bit))
    (fun coeffBit => by
      simpa [RegisterBits.vValueBit, RegisterBits.rCoeffValueBit] using
        (RegisterBits.v_rCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire coeffBit)).symm)
    x hcompare hscratchA hscratchB
  simpa only [RegisterBits.vValueBit_get] using h

/-- The selected compare-true odd path writes `r := r+s` as a complete word. -/
lemma compareSelectedOddDataPathStep_core_rCoeff_of_compare_true_cleanWork
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.rCoeff =
      x.core.rCoeff + x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  exact compareSelectedOddDataPathStep_get_rCoeff_add_of_compare_true_cleanWork
    n counterWidth x bit hcompare hscratchA hscratchB hcarry hwork

/-- The selected compare-true odd path preserves the complete `s` word. -/
lemma compareSelectedOddDataPathStep_core_sCoeff_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.sCoeff =
      x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := compareSelectedOddDataPathStep_get_coreBit_of_compare_true
    n counterWidth (RegisterBits.sCoeffValueBit n counterWidth bit)
    (fun sourceBit => by
      simpa [RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
        RegisterBits.u_sCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire sourceBit)
          (WireAddress.littleEndianWire bit))
    (fun coeffBit => by
      simpa [RegisterBits.sCoeffValueBit, RegisterBits.rCoeffValueBit] using
        (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire coeffBit)).symm)
    x hcompare hscratchA hscratchB
  simpa only [RegisterBits.sCoeffValueBit_get] using h

/-- The selected compare-false odd path preserves the complete `u` word. -/
lemma compareSelectedOddDataPathStep_core_u_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := compareSelectedOddDataPathStep_get_coreBit_of_compare_false
    n counterWidth (RegisterBits.uValueBit n counterWidth bit)
    (fun sourceBit => by
      simpa [RegisterBits.uValueBit, RegisterBits.vValueBit] using
        (RegisterBits.u_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire sourceBit)).symm)
    (fun coeffBit => by
      simpa [RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
        (RegisterBits.u_sCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire coeffBit)).symm)
    x hcompare hscratchA hscratchB
  simpa only [RegisterBits.uValueBit_get] using h

/-- The selected compare-false odd path writes `v := v-u` as a complete word. -/
lemma compareSelectedOddDataPathStep_core_v_of_compare_false_cleanWork
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hwork : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.v =
      x.core.v - x.core.u := by
  let subtracted := sourceSubUFromVStep n counterWidth x
  have hroute : compareSelectedOddDataPathStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth subtracted :=
    compareSelectedOddDataPathStep_eq_false_branch n counterWidth x
      hcompare hscratchA hscratchB
  rw [hroute]
  calc
    (coefficientAddRIntoSStep n counterWidth subtracted).core.v =
        subtracted.core.v := by
      apply word_eq_of_testBit_eq
      intro bit
      have h := coefficientAddRIntoSStep_get_coreBit_of_disjoint
        n counterWidth (RegisterBits.vValueBit n counterWidth bit)
        (fun coeffBit => by
          simpa [RegisterBits.vValueBit, RegisterBits.sCoeffValueBit] using
            (RegisterBits.v_sCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)
              (WireAddress.littleEndianWire coeffBit)).symm)
        subtracted
      simpa only [RegisterBits.vValueBit_get] using h
    _ = x.core.v - x.core.u :=
      sourceSubUFromVStep_get_v_sub_of_clean n counterWidth x hscratchA
        (fun workBit => by
          simpa [sourceCarryWorkPrefixBit] using
            hwork (sourceCarryWorkPrefixIndex n workBit))

/-- The selected compare-false odd path preserves the complete `r` word. -/
lemma compareSelectedOddDataPathStep_core_rCoeff_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.rCoeff =
      x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  exact compareSelectedOddDataPathStep_get_rCoeff_of_compare_false
    n counterWidth x bit hcompare hscratchA hscratchB

/-- The selected compare-false odd path writes `s := s+r` as a complete word. -/
lemma compareSelectedOddDataPathStep_core_sCoeff_of_compare_false_cleanWork
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get x = false) :
    (compareSelectedOddDataPathStep n counterWidth x).core.sCoeff =
      x.core.sCoeff + x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  exact compareSelectedOddDataPathStep_get_sCoeff_add_of_compare_false_cleanWork
    n counterWidth x bit hcompare hscratchA hscratchB hcarry hwork

/-- On a clean compact boundary, the selected `uGreater` odd path writes
`r := r+s` bitwise.  The source subtraction restores the sole VBE bank before
the coefficient addition reuses it. -/
lemma compareSelectedOddDataPathStep_get_rCoeff_add_of_compare_true_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (bit : Fin (n + 1))
    (hcompare : core.compare = true)
    (hscratchA : core.scratchA = false)
    (hscratchB : core.scratchB = false) :
    (compareSelectedOddDataPathStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.rCoeff.val.testBit
        bit.val =
      (core.rCoeff + core.sCoeff).val.testBit bit.val := by
  let input := coefficientAddCleanInput n counterWidth core target
  let subtracted := sourceSubVFromUStep n counterWidth input
  have hpath : compareSelectedOddDataPathStep n counterWidth input =
      coefficientAddSIntoRStep n counterWidth subtracted := by
    exact compareSelectedOddDataPathStep_eq_true_branch n counterWidth input
      (by simpa [input, coefficientAddCleanInput] using hcompare)
      (by simpa [input, coefficientAddCleanInput] using hscratchA)
      (by simpa [input, coefficientAddCleanInput] using hscratchB)
  rw [hpath]
  have hbank : subtracted.shared.coefficientAdder = cleanCoeffAdderWork n := by
    dsimp [subtracted, input]
    exact sourceSubVFromUStep_coefficientAdder_cleanEndpoint
      n counterWidth core target
  have hcarry :
      (coefficientCarryInBit n counterWidth).get subtracted = false := by
    rw [coefficientCarryInBit_get, hbank]
    rfl
  have hwork : ∀ workBit : Fin n,
      (coefficientCarryWorkBit n counterWidth workBit).get subtracted = false := by
    intro workBit
    change (BinaryLabelEncoding.finIdentityBit n workBit).get
      subtracted.shared.coefficientAdder.2 = false
    rw [hbank]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n workBit
  have hsCoeff : ∀ coeffBit : Fin (n + 1),
      (sCoeffValueBit n counterWidth coeffBit).get subtracted =
        core.sCoeff.val.testBit coeffBit.val := by
    intro coeffBit
    change (RegisterBits.sCoeffValueBit n counterWidth coeffBit).get
      subtracted.core = core.sCoeff.val.testBit coeffBit.val
    rw [show core.sCoeff.val.testBit coeffBit.val =
        (RegisterBits.sCoeffValueBit n counterWidth coeffBit).get core by
      exact (RegisterBits.sCoeffValueBit_get n counterWidth coeffBit core).symm]
    dsimp [subtracted]
    exact sourceSubVFromUStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.sCoeffValueBit n counterWidth coeffBit)
      (fun sourceBit => by
        simpa [RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
          RegisterBits.u_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire coeffBit)) input
  have hrCoeff : ∀ coeffBit : Fin (n + 1),
      (rCoeffValueBit n counterWidth coeffBit).get subtracted =
        core.rCoeff.val.testBit coeffBit.val := by
    intro coeffBit
    change (RegisterBits.rCoeffValueBit n counterWidth coeffBit).get
      subtracted.core = core.rCoeff.val.testBit coeffBit.val
    rw [show core.rCoeff.val.testBit coeffBit.val =
        (RegisterBits.rCoeffValueBit n counterWidth coeffBit).get core by
      exact (RegisterBits.rCoeffValueBit_get n counterWidth coeffBit core).symm]
    dsimp [subtracted]
    exact sourceSubVFromUStep_get_coreBit_of_disjoint n counterWidth
      (RegisterBits.rCoeffValueBit n counterWidth coeffBit)
      (fun sourceBit => by
        simpa [RegisterBits.uValueBit, RegisterBits.rCoeffValueBit] using
          RegisterBits.u_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire coeffBit)) input
  have hadd := coefficientAdd_cleanStep_get_right_add_testBit_of_clean
    n counterWidth (coefficientAddSIntoRLayout n counterWidth)
    core.sCoeff core.rCoeff bit subtracted hsCoeff hrCoeff hcarry hwork
  simpa [coefficientAddSIntoRStep, coefficientAddSIntoRLayout,
    rCoeffValueWord] using hadd

/-- On a clean compact boundary, the selected `vLe` odd arithmetic leaves
`r` unchanged before the shared shift dispatcher doubles it. -/
lemma compareSelectedOddDataPathStep_get_rCoeff_of_compare_false_clean
    (n counterWidth : Nat) (core : MK.Registers n counterWidth)
    (target : Word n) (bit : Fin (n + 1))
    (hcompare : core.compare = false)
    (hscratchA : core.scratchA = false)
    (hscratchB : core.scratchB = false) :
    (compareSelectedOddDataPathStep n counterWidth
      (coefficientAddCleanInput n counterWidth core target)).core.rCoeff.val.testBit
        bit.val = core.rCoeff.val.testBit bit.val := by
  let input := coefficientAddCleanInput n counterWidth core target
  let subtracted := sourceSubUFromVStep n counterWidth input
  have hpath : compareSelectedOddDataPathStep n counterWidth input =
      coefficientAddRIntoSStep n counterWidth subtracted := by
    exact compareSelectedOddDataPathStep_eq_false_branch n counterWidth input
      (by simpa [input, coefficientAddCleanInput] using hcompare)
      (by simpa [input, coefficientAddCleanInput] using hscratchA)
      (by simpa [input, coefficientAddCleanInput] using hscratchB)
  rw [hpath]
  calc
    (coefficientAddRIntoSStep n counterWidth subtracted).core.rCoeff.val.testBit
        bit.val =
        (rCoeffValueBit n counterWidth bit).get
          (coefficientAddRIntoSStep n counterWidth subtracted) := by
      symm
      exact rCoeffValueBit_get n counterWidth bit _
    _ = (rCoeffValueBit n counterWidth bit).get subtracted :=
      coefficientAddRIntoSStep_get_rCoeffValueBit
        n counterWidth bit subtracted
    _ = (RegisterBits.rCoeffValueBit n counterWidth bit).get core := by
      dsimp [subtracted]
      exact sourceSubUFromVStep_get_coreBit_of_disjoint n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (fun sourceBit => by
          simpa [RegisterBits.vValueBit, RegisterBits.rCoeffValueBit] using
            RegisterBits.v_rCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire sourceBit)
              (WireAddress.littleEndianWire bit)) input
    _ = core.rCoeff.val.testBit bit.val :=
      RegisterBits.rCoeffValueBit_get n counterWidth bit core

lemma compareSelectedOddDataPathGates_length (n counterWidth : Nat) :
    (compareSelectedOddDataPathGates n counterWidth).length =
      36 * (n - 1) + 44 * n + 8 := by
  simp only [compareSelectedOddDataPathGates, List.length_append,
    compareSelectedSourceSubtractGates_length,
    compareSelectedCoefficientAddGates_length]
  omega

lemma compareSelectedOddDataPathGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedOddDataPathGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  simp only [compareSelectedOddDataPathGates, List.map_append, List.sum_append,
    compareSelectedSourceSubtractGates_xMultiplicity_sum,
    compareSelectedCoefficientAddGates_xMultiplicity_sum]

lemma compareSelectedOddDataPathGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedOddDataPathGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [compareSelectedOddDataPathGates, List.map_append, List.sum_append,
    compareSelectedSourceSubtractGates_cnotMultiplicity_sum,
    compareSelectedCoefficientAddGates_cnotMultiplicity_sum]

lemma compareSelectedOddDataPathGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((compareSelectedOddDataPathGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        44 * n + 36 * (n - 1) + 4 := by
  simp only [compareSelectedOddDataPathGates, List.map_append, List.sum_append,
    compareSelectedSourceSubtractGates_toffoliMultiplicity_sum,
    compareSelectedCoefficientAddGates_toffoliMultiplicity_sum]
  omega

lemma compareSelectedOddDataPathStep_reverse_identity
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (compareSelectedOddDataPathGates n counterWidth).reverse
        (compareSelectedOddDataPathStep n counterWidth x) = x := by
  rw [← compareSelectedOddDataPathStep_eq_gateList n counterWidth x]
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (compareSelectedOddDataPathGates n counterWidth) x

/-! ## Active-odd masked data path -/

/-- The reverse `v := v-u` gate list is disjoint from the shared control bit
used to retain the masked `vLe` predicate. -/
lemma sourceSubUFromVGates_bitDisjoint_control
    (n counterWidth : Nat) :
    forall gate, gate ∈ sourceSubUFromVGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (controlBit n counterWidth) gate := by
  intro gate hmem
  have hforward : gate ∈ sourceAddUIntoVGates n counterWidth := by
    simpa [sourceSubUFromVGates] using hmem
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (sourceAddUIntoVLayout n counterWidth) (controlBit n counterWidth)
    (fun i => by
      simpa [sourceAddUIntoVLayout, uValueWord, controlBit,
        RegisterBits.uValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (sharedControlBit n counterWidth))
    (fun i => by
      simpa [sourceAddUIntoVLayout, vValueWord, controlBit,
        RegisterBits.vValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (sharedControlBit n counterWidth))
    (by
      simpa [sourceAddUIntoVLayout, scratchABit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedControlBit n counterWidth))
    (fun j => by
      simpa [sourceAddUIntoVLayout, sourceCarryWorkPrefixWord,
        sourceCarryWorkPrefixBit] using
        (controlBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (sourceCarryWorkPrefixIndex n j)).symm)
    gate hforward

/-- The compact `r`-into-`s` addition is disjoint from the shared control bit
used to retain the masked `vLe` predicate. -/
lemma coefficientAddRIntoSGates_bitDisjoint_control
    (n counterWidth : Nat) :
    forall gate, gate ∈ coefficientAddRIntoSGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (controlBit n counterWidth) gate := by
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
    (coefficientAddRIntoSLayout n counterWidth) (controlBit n counterWidth)
    (fun i => by
      simpa [coefficientAddRIntoSLayout, rCoeffValueWord, rCoeffValueBit,
        controlBit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth i)
          (sharedControlBit n counterWidth))
    (fun i => by
      simpa [coefficientAddRIntoSLayout, sCoeffValueWord, sCoeffValueBit,
        controlBit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.sCoeffValueBit n counterWidth i)
          (sharedControlBit n counterWidth))
    (by
      simpa [coefficientAddRIntoSLayout] using
        (controlBit_coefficientCarryInBit_wire_ne n counterWidth).symm)
    (fun j => by
      simpa [coefficientAddRIntoSLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit] using
        (controlBit_coefficientCarryWorkBit_wire_ne n counterWidth j).symm)

/-- Positive-control `v := v-u` under the retained masked `vLe` bit. -/
def controlControlledSubUFromVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (controlBit n counterWidth) (scratchBBit n counterWidth)
    (sourceSubUFromVGates n counterWidth)
    (sourceSubUFromVGates_bitDisjoint_control n counterWidth)
    (sourceSubUFromVGates_bitDisjoint_scratchB n counterWidth)
    (by
      simpa [controlBit, scratchBBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (sharedControlBit n counterWidth)).symm)

def controlControlledSubUFromVStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (controlControlledSubUFromVGates n counterWidth)

lemma controlControlledSubUFromVStep_eq_self_of_control_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    controlControlledSubUFromVStep n counterWidth x = x := by
  simpa [controlControlledSubUFromVStep, controlControlledSubUFromVGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (controlBit n counterWidth) (scratchBBit n counterWidth)
      (sourceSubUFromVGates n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_control n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_scratchB n counterWidth)
      (by
        simpa [controlBit, scratchBBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchBBit n counterWidth)
            (sharedControlBit n counterWidth)).symm)
      x hcontrol

lemma controlControlledSubUFromVStep_eq_sub_of_control_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = true)
    (hwork : (scratchBBit n counterWidth).get x = false) :
    controlControlledSubUFromVStep n counterWidth x =
      sourceSubUFromVStep n counterWidth x := by
  simpa [controlControlledSubUFromVStep, controlControlledSubUFromVGates,
    sourceSubUFromVStep,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (controlBit n counterWidth) (scratchBBit n counterWidth)
      (sourceSubUFromVGates n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_control n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_scratchB n counterWidth)
      (by
        simpa [controlBit, scratchBBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchBBit n counterWidth)
            (sharedControlBit n counterWidth)).symm)
      x hcontrol hwork

/-- Positive-control `s := s+r` under the retained masked `vLe` bit. -/
def controlControlledAddRIntoSGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (controlBit n counterWidth) (scratchABit n counterWidth)
    (coefficientAddRIntoSGates n counterWidth)
    (coefficientAddRIntoSGates_bitDisjoint_control n counterWidth)
    (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
    (by
      simpa [controlBit, scratchABit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedControlBit n counterWidth)).symm)

def controlControlledAddRIntoSStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (controlControlledAddRIntoSGates n counterWidth)

lemma controlControlledAddRIntoSStep_eq_self_of_control_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    controlControlledAddRIntoSStep n counterWidth x = x := by
  simpa [controlControlledAddRIntoSStep, controlControlledAddRIntoSGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (controlBit n counterWidth) (scratchABit n counterWidth)
      (coefficientAddRIntoSGates n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_control n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
      (by
        simpa [controlBit, scratchABit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchABit n counterWidth)
            (sharedControlBit n counterWidth)).symm)
      x hcontrol

lemma controlControlledAddRIntoSStep_eq_add_of_control_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = true)
    (hwork : (scratchABit n counterWidth).get x = false) :
    controlControlledAddRIntoSStep n counterWidth x =
      coefficientAddRIntoSStep n counterWidth x := by
  simpa [controlControlledAddRIntoSStep, controlControlledAddRIntoSGates,
    coefficientAddRIntoSStep, coefficientAddRIntoSGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (controlBit n counterWidth) (scratchABit n counterWidth)
      (coefficientAddRIntoSGates n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_control n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_scratchA n counterWidth)
      (by
        simpa [controlBit, scratchABit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchABit n counterWidth)
            (sharedControlBit n counterWidth)).symm)
      x hcontrol hwork

/-- Compute or erase `path ∧ ¬compare` in the clean shared control bit. -/
def activeOddVLeControlGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  [ EncodedBit.GateSpec.x (compareBit n counterWidth)
  , EncodedBit.GateSpec.toffoli
      (pathBit n counterWidth) (compareBit n counterWidth)
      (controlBit n counterWidth)
      (by
        simpa [pathBit, compareBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth)
            (sharedPathBit n counterWidth)).symm)
      (pathBit_controlBit_wire_ne n counterWidth)
      (by
        simpa [compareBit, controlBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth)
            (sharedControlBit n counterWidth))
  , EncodedBit.GateSpec.x (compareBit n counterWidth) ]

/-- Compare-controlled source subtraction is disjoint from every public
target bit. -/
lemma compareControlledSubVFromUGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ compareControlledSubVFromUGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  unfold compareControlledSubVFromUGates
  apply EncodedBit.GateSpec.controlledListWithWorkGates_bitDisjoint
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) targetIndex
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) targetIndex
  · exact sourceSubVFromUGates_bitDisjoint_target n counterWidth targetIndex

/-- Shared-control source subtraction is disjoint from every public target
bit. -/
lemma controlControlledSubUFromVGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ controlControlledSubUFromVGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  unfold controlControlledSubUFromVGates
  apply EncodedBit.GateSpec.controlledListWithWorkGates_bitDisjoint
  · exact liftSharedBit_targetValueBit_wire_ne n counterWidth
      (sharedControlBit n counterWidth) targetIndex
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) targetIndex
  · exact sourceSubUFromVGates_bitDisjoint_target n counterWidth targetIndex

/-- Compare-controlled coefficient addition is disjoint from every public
target bit. -/
lemma compareControlledAddSIntoRGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ compareControlledAddSIntoRGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  unfold compareControlledAddSIntoRGates
  apply EncodedBit.GateSpec.controlledListWithWorkGates_bitDisjoint
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) targetIndex
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) targetIndex
  · exact coefficientAddSIntoRGates_bitDisjoint_target n counterWidth
      targetIndex

/-- Shared-control coefficient addition is disjoint from every public target
bit. -/
lemma controlControlledAddRIntoSGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ controlControlledAddRIntoSGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  unfold controlControlledAddRIntoSGates
  apply EncodedBit.GateSpec.controlledListWithWorkGates_bitDisjoint
  · exact liftSharedBit_targetValueBit_wire_ne n counterWidth
      (sharedControlBit n counterWidth) targetIndex
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) targetIndex
  · exact coefficientAddRIntoSGates_bitDisjoint_target n counterWidth
      targetIndex

/-- The temporary masked-vLe control computation is disjoint from every
public target bit. -/
lemma activeOddVLeControlGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ activeOddVLeControlGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  simp only [activeOddVLeControlGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) targetIndex
  · exact ⟨
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedPathBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedControlBit n counterWidth) targetIndex⟩
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) targetIndex

def activeOddVLeControlStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (activeOddVLeControlGates n counterWidth)

lemma activeOddVLeControlStep_get_control
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (controlBit n counterWidth).get
        (activeOddVLeControlStep n counterWidth x) =
      ((controlBit n counterWidth).get x ^^
        ((pathBit n counterWidth).get x &&
          !(compareBit n counterWidth).get x)) := by
  unfold activeOddVLeControlStep activeOddVLeControlGates
  change (controlBit n counterWidth).get
      ((compareBit n counterWidth).flip
        (EncodedBit.toffoliStep (pathBit n counterWidth)
          (compareBit n counterWidth) (controlBit n counterWidth)
          ((compareBit n counterWidth).flip x))) = _
  rw [EncodedBit.get_flip_of_wire_ne
      (compareBit n counterWidth) (controlBit n counterWidth)
      (by
        simpa [compareBit, controlBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth)
            (sharedControlBit n counterWidth)),
    EncodedBit.toffoliStep_get_target,
    EncodedBit.get_flip_of_wire_ne
      (compareBit n counterWidth) (pathBit n counterWidth)
      (by
        simpa [compareBit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth)
            (sharedPathBit n counterWidth)),
    EncodedBit.get_flip_self]
  cases (compareBit n counterWidth).get x <;> rfl

lemma activeOddVLeControlStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (activeOddVLeControlStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  unfold activeOddVLeControlStep activeOddVLeControlGates
  change (compareBit n counterWidth).get
      ((compareBit n counterWidth).flip
        (EncodedBit.toffoliStep (pathBit n counterWidth)
          (compareBit n counterWidth) (controlBit n counterWidth)
          ((compareBit n counterWidth).flip x))) = _
  rw [EncodedBit.get_flip_self,
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (by
        simpa [compareBit, controlBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth)
            (sharedControlBit n counterWidth)).symm),
    EncodedBit.get_flip_self]
  cases (compareBit n counterWidth).get x <;> rfl

lemma activeOddVLeControlStep_eq_self_of_predicate_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hpredicate :
      ((pathBit n counterWidth).get x &&
        !(compareBit n counterWidth).get x) = false) :
    activeOddVLeControlStep n counterWidth x = x := by
  unfold activeOddVLeControlStep activeOddVLeControlGates
  change (compareBit n counterWidth).flip
      (EncodedBit.toffoliStep (pathBit n counterWidth)
        (compareBit n counterWidth) (controlBit n counterWidth)
        ((compareBit n counterWidth).flip x)) = x
  unfold EncodedBit.toffoliStep
  have hcondition : ¬
      ((pathBit n counterWidth).get ((compareBit n counterWidth).flip x) &&
          (compareBit n counterWidth).get
            ((compareBit n counterWidth).flip x)) := by
    rw [EncodedBit.get_flip_of_wire_ne
        (compareBit n counterWidth) (pathBit n counterWidth)
        (by
          simpa [compareBit, pathBit] using
            liftCoreBit_liftSharedBit_wire_ne n counterWidth
              (RegisterBits.compareBit n counterWidth)
              (sharedPathBit n counterWidth)),
      EncodedBit.get_flip_self]
    have hpredicate' : (x.shared.path && !x.core.compare) = false := by
      simpa only [pathBit_get, compareBit_get] using hpredicate
    cases hp : x.shared.path <;> cases hc : x.core.compare <;>
      simp [hp, hc] at hpredicate' ⊢
  rw [if_neg hcondition]
  exact EncodedBit.flip_flip (compareBit n counterWidth) x

lemma activeOddVLeControlStep_eq_controlFlip_of_predicate_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hpredicate :
      ((pathBit n counterWidth).get x &&
        !(compareBit n counterWidth).get x) = true) :
    activeOddVLeControlStep n counterWidth x =
      (controlBit n counterWidth).flip x := by
  unfold activeOddVLeControlStep activeOddVLeControlGates
  change (compareBit n counterWidth).flip
      (EncodedBit.toffoliStep (pathBit n counterWidth)
        (compareBit n counterWidth) (controlBit n counterWidth)
        ((compareBit n counterWidth).flip x)) = _
  unfold EncodedBit.toffoliStep
  have hcondition :
      (pathBit n counterWidth).get ((compareBit n counterWidth).flip x) &&
          (compareBit n counterWidth).get
            ((compareBit n counterWidth).flip x) := by
    rw [EncodedBit.get_flip_of_wire_ne
        (compareBit n counterWidth) (pathBit n counterWidth)
        (by
          simpa [compareBit, pathBit] using
            liftCoreBit_liftSharedBit_wire_ne n counterWidth
              (RegisterBits.compareBit n counterWidth)
              (sharedPathBit n counterWidth)),
      EncodedBit.get_flip_self]
    have hpredicate' : (x.shared.path && !x.core.compare) = true := by
      simpa only [pathBit_get, compareBit_get] using hpredicate
    cases hp : x.shared.path <;> cases hc : x.core.compare <;>
      simp [hp, hc] at hpredicate' ⊢
  rw [if_pos hcondition]
  rw [EncodedBit.flip_comm (compareBit n counterWidth)
    (controlBit n counterWidth)]
  rw [EncodedBit.flip_flip]

/-- Native odd data path selected by the masked pair `(path, compare)`.
`compare=true` selects `uGreater`; `path ∧ ¬compare` is retained only long
enough to select `vLe`, then erased from `control`. -/
def activeOddSelectedDataPathGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  compareControlledSubVFromUGates n counterWidth ++
    activeOddVLeControlGates n counterWidth ++
      controlControlledSubUFromVGates n counterWidth ++
        compareControlledAddSIntoRGates n counterWidth ++
          controlControlledAddRIntoSGates n counterWidth ++
            activeOddVLeControlGates n counterWidth

/-- The complete active-odd arithmetic path stays within core/shared work and
is disjoint from every public target bit. -/
lemma activeOddSelectedDataPathGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ activeOddSelectedDataPathGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  rw [activeOddSelectedDataPathGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hcontrolLast
  · rcases List.mem_append.mp hgate with hgate | haddR
    · rcases List.mem_append.mp hgate with hgate | haddS
      · rcases List.mem_append.mp hgate with hgate | hsubU
        · rcases List.mem_append.mp hgate with hsubV | hcontrolFirst
          · exact compareControlledSubVFromUGates_bitDisjoint_target n
              counterWidth targetIndex gate hsubV
          · exact activeOddVLeControlGates_bitDisjoint_target n counterWidth
              targetIndex gate hcontrolFirst
        · exact controlControlledSubUFromVGates_bitDisjoint_target n
            counterWidth targetIndex gate hsubU
      · exact compareControlledAddSIntoRGates_bitDisjoint_target n
          counterWidth targetIndex gate haddS
    · exact controlControlledAddRIntoSGates_bitDisjoint_target n counterWidth
        targetIndex gate haddR
  · exact activeOddVLeControlGates_bitDisjoint_target n counterWidth
      targetIndex gate hcontrolLast

def activeOddSelectedDataPathStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (activeOddSelectedDataPathGates n counterWidth)

def activeOddSelectedDataPathProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeOddSelectedDataPathGates n counterWidth)

lemma activeOddSelectedDataPath_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (activeOddSelectedDataPathProgram n counterWidth) environment
      (activeOddSelectedDataPathStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (activeOddSelectedDataPathGates n counterWidth)

lemma activeOddSelectedDataPathStep_eq_stages
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    activeOddSelectedDataPathStep n counterWidth x =
      activeOddVLeControlStep n counterWidth
        (controlControlledAddRIntoSStep n counterWidth
          (compareControlledAddSIntoRStep n counterWidth
            (controlControlledSubUFromVStep n counterWidth
              (activeOddVLeControlStep n counterWidth
                (compareControlledSubVFromUStep n counterWidth x))))) := by
  unfold activeOddSelectedDataPathStep activeOddSelectedDataPathGates
  repeat rw [EncodedBit.GateSpec.stepList_append]
  rfl

/-- If no masked odd route is selected, the complete odd data path is the
identity.  This is the contract used by both even branches and inactive
padding rounds. -/
lemma activeOddSelectedDataPathStep_eq_self_of_path_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    activeOddSelectedDataPathStep n counterWidth x = x := by
  rw [activeOddSelectedDataPathStep_eq_stages]
  rw [compareControlledSubVFromUStep_eq_self_of_compare_false
    n counterWidth x hcompare]
  have hpfalse :
      ((pathBit n counterWidth).get x &&
        !(compareBit n counterWidth).get x) = false := by
    rw [hpath]
    rfl
  rw [activeOddVLeControlStep_eq_self_of_predicate_false
    n counterWidth x hpfalse]
  rw [controlControlledSubUFromVStep_eq_self_of_control_false
    n counterWidth x hcontrol]
  rw [compareControlledAddSIntoRStep_eq_self_of_compare_false
    n counterWidth x hcompare]
  rw [controlControlledAddRIntoSStep_eq_self_of_control_false
    n counterWidth x hcontrol]
  exact activeOddVLeControlStep_eq_self_of_predicate_false
    n counterWidth x hpfalse

/-- On a clean `compare=true` boundary, the masked active-odd data path is
exactly the already-certified compare-selected `uGreater` path. -/
lemma activeOddSelectedDataPathStep_eq_compareSelected_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    activeOddSelectedDataPathStep n counterWidth x =
      compareSelectedOddDataPathStep n counterWidth x := by
  rw [activeOddSelectedDataPathStep_eq_stages]
  rw [compareControlledSubVFromUStep_eq_subVFromU_of_compare_true
    n counterWidth x hcompare hscratchB]
  let subtracted := sourceSubVFromUStep n counterWidth x
  have hcompareSub :
      (compareBit n counterWidth).get subtracted = true := by
    dsimp [subtracted]
    exact (sourceSubVFromUStep_get_compare n counterWidth x).trans hcompare
  have hcontrolSub :
      (controlBit n counterWidth).get subtracted = false := by
    dsimp [subtracted]
    exact (sourceSubVFromUStep_get_control n counterWidth x).trans hcontrol
  have hscratchASub :
      (scratchABit n counterWidth).get subtracted = false := by
    simpa only [subtracted, scratchABit_get] using
      (sourceSubVFromUStep_get_scratchA n counterWidth x).trans hscratchA
  have hpredicateSub :
      ((pathBit n counterWidth).get subtracted &&
        !(compareBit n counterWidth).get subtracted) = false := by
    rw [hcompareSub]
    simp
  rw [activeOddVLeControlStep_eq_self_of_predicate_false
    n counterWidth subtracted hpredicateSub]
  rw [controlControlledSubUFromVStep_eq_self_of_control_false
    n counterWidth subtracted hcontrolSub]
  rw [compareControlledAddSIntoRStep_eq_addSIntoR_of_compare_true
    n counterWidth subtracted hcompareSub hscratchASub]
  let added := coefficientAddSIntoRStep n counterWidth subtracted
  have hcompareAdded :
      (compareBit n counterWidth).get added = true := by
    dsimp [added]
    exact (coefficientAddSIntoRStep_get_compare
      n counterWidth subtracted).trans hcompareSub
  have hcontrolAdded :
      (controlBit n counterWidth).get added = false := by
    dsimp [added]
    exact (coefficientAddSIntoRStep_get_control
      n counterWidth subtracted).trans hcontrolSub
  have hpredicateAdded :
      ((pathBit n counterWidth).get added &&
        !(compareBit n counterWidth).get added) = false := by
    rw [hcompareAdded]
    simp
  rw [controlControlledAddRIntoSStep_eq_self_of_control_false
    n counterWidth added hcontrolAdded]
  rw [activeOddVLeControlStep_eq_self_of_predicate_false
    n counterWidth added hpredicateAdded]
  exact (compareSelectedOddDataPathStep_eq_true_branch
    n counterWidth x hcompare hscratchA hscratchB).symm

/-- On a clean `compare=false` odd boundary, the temporary shared control bit
selects `vLe`, commutes through its arithmetic, and is then erased.  The
result is exactly the already-certified compare-selected `vLe` path. -/
lemma activeOddSelectedDataPathStep_eq_compareSelected_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hpath : (pathBit n counterWidth).get x = true)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    activeOddSelectedDataPathStep n counterWidth x =
      compareSelectedOddDataPathStep n counterWidth x := by
  let control := controlBit n counterWidth
  have hpredicate :
      ((pathBit n counterWidth).get x &&
        !(compareBit n counterWidth).get x) = true := by
    rw [hpath, hcompare]
    rfl
  have hcontrolFlip : control.get (control.flip x) = true := by
    rw [EncodedBit.get_flip_self, hcontrol]
    rfl
  have hscratchBFlip :
      (scratchBBit n counterWidth).get (control.flip x) = false := by
    rw [EncodedBit.get_flip_of_wire_ne control (scratchBBit n counterWidth)
      (by
        dsimp [control]
        simpa [controlBit, scratchBBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchBBit n counterWidth)
            (sharedControlBit n counterWidth)).symm)]
    exact hscratchB
  have hsourceComm :
      sourceSubUFromVStep n counterWidth (control.flip x) =
        control.flip (sourceSubUFromVStep n counterWidth x) := by
    dsimp [control]
    exact EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
      (sourceSubUFromVGates n counterWidth) (controlBit n counterWidth)
      (sourceSubUFromVGates_bitDisjoint_control n counterWidth) x
  let subtracted := sourceSubUFromVStep n counterWidth (control.flip x)
  have hcompareSub :
      (compareBit n counterWidth).get subtracted = false := by
    dsimp [subtracted]
    rw [sourceSubUFromVStep_get_compare,
      EncodedBit.get_flip_of_wire_ne control (compareBit n counterWidth)
        (by
          dsimp [control]
          simpa [controlBit, compareBit] using
            (liftCoreBit_liftSharedBit_wire_ne n counterWidth
              (RegisterBits.compareBit n counterWidth)
              (sharedControlBit n counterWidth)).symm)]
    exact hcompare
  have hcontrolSub : control.get subtracted = true := by
    dsimp [subtracted]
    rw [hsourceComm, EncodedBit.get_flip_self,
      sourceSubUFromVStep_get_control, hcontrol]
    rfl
  have hscratchASub :
      (scratchABit n counterWidth).get subtracted = false := by
    dsimp [subtracted]
    rw [scratchABit_get, sourceSubUFromVStep_get_scratchA]
    rw [← scratchABit_get]
    rw [EncodedBit.get_flip_of_wire_ne control (scratchABit n counterWidth)
      (by
        dsimp [control]
        simpa [controlBit, scratchABit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchABit n counterWidth)
            (sharedControlBit n counterWidth)).symm)]
    exact hscratchA
  have hcoefficientComm (y : Registers n counterWidth) :
      coefficientAddRIntoSStep n counterWidth (control.flip y) =
        control.flip (coefficientAddRIntoSStep n counterWidth y) := by
    dsimp [control, coefficientAddRIntoSStep]
    exact EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
      (coefficientAddRIntoSGates n counterWidth) (controlBit n counterWidth)
      (coefficientAddRIntoSGates_bitDisjoint_control n counterWidth) y
  rw [activeOddSelectedDataPathStep_eq_stages]
  rw [compareControlledSubVFromUStep_eq_self_of_compare_false
    n counterWidth x hcompare]
  rw [activeOddVLeControlStep_eq_controlFlip_of_predicate_true
    n counterWidth x hpredicate]
  rw [controlControlledSubUFromVStep_eq_sub_of_control_true
    n counterWidth (control.flip x) hcontrolFlip hscratchBFlip]
  rw [compareControlledAddSIntoRStep_eq_self_of_compare_false
    n counterWidth subtracted hcompareSub]
  rw [controlControlledAddRIntoSStep_eq_add_of_control_true
    n counterWidth subtracted hcontrolSub hscratchASub]
  change activeOddVLeControlStep n counterWidth
      (coefficientAddRIntoSStep n counterWidth
        (sourceSubUFromVStep n counterWidth (control.flip x))) = _
  rw [hsourceComm, hcoefficientComm]
  let added := coefficientAddRIntoSStep n counterWidth
    (sourceSubUFromVStep n counterWidth x)
  have hcompareAdded :
      (compareBit n counterWidth).get (control.flip added) = false := by
    rw [EncodedBit.get_flip_of_wire_ne control (compareBit n counterWidth)
      (by
        dsimp [control]
        simpa [controlBit, compareBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth)
            (sharedControlBit n counterWidth)).symm)]
    dsimp [added]
    rw [coefficientAddRIntoSStep_get_compare,
      sourceSubUFromVStep_get_compare]
    exact hcompare
  have hpathAdded :
      (pathBit n counterWidth).get (control.flip added) = true := by
    rw [EncodedBit.get_flip_of_wire_ne control (pathBit n counterWidth)
      (by
        dsimp [control]
        exact (pathBit_controlBit_wire_ne n counterWidth).symm)]
    dsimp [added]
    rw [coefficientAddRIntoSStep_get_path,
      sourceSubUFromVStep_get_path]
    exact hpath
  have hpredicateAdded :
      ((pathBit n counterWidth).get (control.flip added) &&
        !(compareBit n counterWidth).get (control.flip added)) = true := by
    rw [hpathAdded, hcompareAdded]
    rfl
  rw [activeOddVLeControlStep_eq_controlFlip_of_predicate_true
    n counterWidth (control.flip added) hpredicateAdded]
  rw [EncodedBit.flip_flip]
  exact (compareSelectedOddDataPathStep_eq_false_branch
    n counterWidth x hcompare hscratchA hscratchB).symm

/-- On a clean selected odd boundary, the masked native data path is exactly
the established compare-selected odd data path, independently of the
comparison result. -/
lemma activeOddSelectedDataPathStep_eq_compareSelected
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hpath : (pathBit n counterWidth).get x = true)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    activeOddSelectedDataPathStep n counterWidth x =
      compareSelectedOddDataPathStep n counterWidth x := by
  cases hcompare : (compareBit n counterWidth).get x
  · exact activeOddSelectedDataPathStep_eq_compareSelected_of_compare_false
      n counterWidth x hcompare hpath hcontrol hscratchA hscratchB
  · exact activeOddSelectedDataPathStep_eq_compareSelected_of_compare_true
      n counterWidth x hcompare hcontrol hscratchA hscratchB

@[simp] lemma activeOddVLeControlGates_length
    (n counterWidth : Nat) :
    (activeOddVLeControlGates n counterWidth).length = 3 := by
  rfl

@[simp] lemma activeOddVLeControlGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((activeOddVLeControlGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  rfl

@[simp] lemma activeOddVLeControlGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((activeOddVLeControlGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  rfl

@[simp] lemma activeOddVLeControlGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((activeOddVLeControlGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 1 := by
  rfl

lemma activeOddSelectedDataPathGates_length (n counterWidth : Nat) :
    (activeOddSelectedDataPathGates n counterWidth).length =
      36 * (n - 1) + 44 * n + 10 := by
  simp only [activeOddSelectedDataPathGates, List.length_append,
    activeOddVLeControlGates_length,
    compareControlledSubVFromUGates, controlControlledSubUFromVGates,
    compareControlledAddSIntoRGates, controlControlledAddRIntoSGates,
    EncodedBit.GateSpec.controlledListWithWorkGates_length_eq,
    sourceSubVFromUGates_length, sourceSubVFromUGates_toffoliMultiplicity_sum,
    sourceSubUFromVGates_length, sourceSubUFromVGates_toffoliMultiplicity_sum,
    coefficientAddSIntoRGates_length,
    coefficientAddSIntoRGates_toffoliMultiplicity_sum,
    coefficientAddRIntoSGates_length,
    coefficientAddRIntoSGates_toffoliMultiplicity_sum]
  omega

lemma activeOddSelectedDataPathGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((activeOddSelectedDataPathGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  simp only [activeOddSelectedDataPathGates, List.map_append, List.sum_append,
    activeOddVLeControlGates_xMultiplicity_sum,
    compareControlledSubVFromUGates, controlControlledSubUFromVGates,
    compareControlledAddSIntoRGates, controlControlledAddRIntoSGates,
    EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum]

lemma activeOddSelectedDataPathGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((activeOddSelectedDataPathGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [activeOddSelectedDataPathGates, List.map_append, List.sum_append,
    activeOddVLeControlGates_cnotMultiplicity_sum,
    compareControlledSubVFromUGates, controlControlledSubUFromVGates,
    compareControlledAddSIntoRGates, controlControlledAddRIntoSGates,
    EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    sourceSubVFromUGates_xMultiplicity_sum,
    sourceSubUFromVGates_xMultiplicity_sum,
    coefficientAddSIntoRGates_xMultiplicity_sum,
    coefficientAddRIntoSGates_xMultiplicity_sum]

lemma activeOddSelectedDataPathGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((activeOddSelectedDataPathGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        44 * n + 36 * (n - 1) + 6 := by
  simp only [activeOddSelectedDataPathGates, List.map_append, List.sum_append,
    activeOddVLeControlGates_toffoliMultiplicity_sum,
    compareControlledSubVFromUGates, controlControlledSubUFromVGates,
    compareControlledAddSIntoRGates, controlControlledAddRIntoSGates,
    EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    sourceSubVFromUGates_cnotMultiplicity_sum,
    sourceSubVFromUGates_toffoliMultiplicity_sum,
    sourceSubUFromVGates_cnotMultiplicity_sum,
    sourceSubUFromVGates_toffoliMultiplicity_sum,
    coefficientAddSIntoRGates_cnotMultiplicity_sum,
    coefficientAddSIntoRGates_toffoliMultiplicity_sum,
    coefficientAddRIntoSGates_cnotMultiplicity_sum,
    coefficientAddRIntoSGates_toffoliMultiplicity_sum]
  omega

end Compact

end
end MK
end MAU.Inversion
end QuantumAlg

end
