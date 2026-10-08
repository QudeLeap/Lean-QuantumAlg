/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Round

/-!
# Round readout

This focused leaf is part of the exact fixed-round binary-GCD inversion
realization.  It is exported only through the canonical `MAU.Inversion.MK`
aggregate.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-- Active-only semantic round selector lifted to the full fixed-round
workspace.  Callers must carry the active-source assumption when relating this
selector to `RoundState.round`: this is not the total fixed-round step.  The
`v = 0` case enters terminating counter mode, while the `v ≠ 0` case enters
the nonzero active selected round.  Inactive padding mode and the
data-dependent Same-Circuit wrapper remain separate obligations. -/
def fullRoundWorkKaliskiActiveOnlyRoundStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    if x.1.1.1.v.val = 0 then
      fullRoundWorkTerminatingStep tail counterWidth x
    else
      fullRoundWorkKaliskiActiveNonzeroRoundStep
        tail counterWidth comparisonIndex historyIndex x

/-- In the `v = 0` branch, the active-only selector dispatches to the
terminating counter-mode wrapper. -/
theorem fullRoundWorkKaliskiActiveOnlyRoundStep_eq_terminating_of_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hvZero : x.1.1.1.v.val = 0) :
    fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      fullRoundWorkTerminatingStep tail counterWidth x := by
  simp [fullRoundWorkKaliskiActiveOnlyRoundStep, hvZero]

/-- In the `v ≠ 0` branch, the active-only selector dispatches to the nonzero
active selected-round wrapper. -/
theorem fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hvNonzero : x.1.1.1.v.val ≠ 0) :
    fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      fullRoundWorkKaliskiActiveNonzeroRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  simp [fullRoundWorkKaliskiActiveOnlyRoundStep, hvNonzero]

/-- On clean work in the concrete `v = 0` case, the active-only selector has
the same clean endpoint as the terminating counter-mode wrapper.
-/
theorem fullRoundWorkKaliskiActiveOnlyRoundStep_cleanEndpoint_of_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_terminating_of_v_zero]
  · exact
      fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero
        tail counterWidth x hcompare hactive hvZero
  · exact hvZero

/-- On clean work in the concrete `v = 0` case, the active-only selector
matches the source terminating round on the source-state projection.
-/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_fromRegisters_eq_source_round_of_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_terminating_of_v_zero]
  · exact
      fullRoundWorkTerminatingStep_fromRegisters_eq_source_round_of_v_zero
        tail counterWidth kaliskiSteps paddingSteps x hcompare hactive hvZero
  · exact hvZero

/-- On clean work in the concrete `v ≠ 0` case, the active-only selector's
source-state projection reduces to the existing nonzero active selected-round
projection.  This is a routing fact, not the branch-split source-round theorem
for the nonzero case. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_projection_eq_activeNonzero_of_v_nonzero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hvNonzero : x.v.val ≠ 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps paddingSteps =
      RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps paddingSteps := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero]
  exact hvNonzero

/-- Selector over the active/inactive semantic Kaliski round routes in the full
fixed-round workspace.  This packages the already separated active-only and
inactive-padding semantic routes; it is not a Same-Circuit witness. -/
def fullRoundWorkKaliskiRoundStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    if x.1.1.1.active then
      fullRoundWorkKaliskiActiveOnlyRoundStep
        tail counterWidth comparisonIndex historyIndex x
    else
      fullRoundWorkInactivePaddingStep tail counterWidth x

/-- In active mode, the total semantic selector dispatches to the active-only
round selector. -/
theorem fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : x.1.1.1.active = true) :
    fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      fullRoundWorkKaliskiActiveOnlyRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  simp [fullRoundWorkKaliskiRoundStep, hactive]

/-- In inactive mode, the total semantic selector dispatches to the inactive
padding route. -/
theorem fullRoundWorkKaliskiRoundStep_eq_inactivePadding_of_inactive
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : x.1.1.1.active = false) :
    fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      fullRoundWorkInactivePaddingStep tail counterWidth x := by
  simp [fullRoundWorkKaliskiRoundStep, hactive]

/-- On clean work in inactive mode, the total semantic selector has the same
clean endpoint as inactive padding mode. -/
theorem fullRoundWorkKaliskiRoundStep_cleanEndpoint_of_inactive
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_inactivePadding_of_inactive]
  · exact fullRoundWorkInactivePaddingStep_cleanEndpoint
      tail counterWidth x
  · exact hactive

/-- On clean work in inactive mode, the total semantic selector matches the
source inactive round on the source-state projection. -/
theorem
    fullRoundWorkKaliskiRoundStep_fromRegisters_eq_source_round_of_inactive
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_inactivePadding_of_inactive]
  · exact
      fullRoundWorkInactivePaddingStep_fromRegisters_eq_source_round_of_inactive
        tail counterWidth kaliskiSteps paddingSteps x hactive
  · exact hactive

/-- On clean work in active terminating mode, the total semantic selector has
the same clean endpoint as the active-only terminating branch. -/
theorem fullRoundWorkKaliskiRoundStep_cleanEndpoint_of_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_cleanEndpoint_of_v_zero
        tail counterWidth comparisonIndex historyIndex x
        hcompare hactive hvZero
  · exact hactive

/-- The clean-restoring semantic total selector is not itself reversible on
the full clean `v = 0` slice: active termination and inactive padding collapse
the two possible input active flags to the same clean output.  A gate-level
total-round witness therefore needs either a narrower domain statement or
path information outside this clean-restoring step. -/
theorem fullRoundWorkKaliskiRoundStep_not_injective_clean_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hvZero : x.v.val = 0) :
    ¬ Function.Injective
      (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex) := by
  let xActive : Registers tail.succ counterWidth := { x with active := true }
  let xInactive : Registers tail.succ counterWidth :=
    { x with active := false }
  let activeInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (((xActive, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  let inactiveInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (((xInactive, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  have hsameOutput :
      fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex activeInput =
        fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex inactiveInput := by
    rw [fullRoundWorkKaliskiRoundStep_cleanEndpoint_of_v_zero
      tail counterWidth comparisonIndex historyIndex xActive]
    · rw [fullRoundWorkKaliskiRoundStep_cleanEndpoint_of_inactive
        tail counterWidth comparisonIndex historyIndex xInactive]
      simp [xInactive]
    · simpa [xActive] using hcompare
    · simp [xActive]
    · simpa [xActive] using hvZero
  have hinputNe : activeInput ≠ inactiveInput := by
    intro h
    have hactiveEq := congrArg
      (fun y : RegistersWithFullRoundWork tail.succ counterWidth =>
        y.1.1.1.active) h
    simp [activeInput, inactiveInput, xActive, xInactive] at hactiveEq
  intro hinj
  exact hinputNe (hinj hsameOutput)

/-- Consequently, no base-gate program can realize the clean-restoring semantic
total selector as a total step over the standard full-round workspace whenever
the clean `v = 0` slice is inhabited. -/
theorem fullRoundWorkKaliskiRoundStep_not_realizable_clean_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hvZero : x.v.val = 0) :
    ¬ ∃ program :
        UnitaryCircuit AlgorithmGate.model .empty
          (QubitLayout.canonical
            (registersWithFullRoundWorkEncoding
              tail.succ counterWidth).width).toQuantum,
      UnitaryCircuit.Realizes
        (registersWithFullRoundWorkEncoding tail.succ counterWidth)
        program
        (fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex) := by
  intro hrealizes
  rcases hrealizes with ⟨program, hprogram⟩
  exact
    fullRoundWorkKaliskiRoundStep_not_injective_clean_v_zero
      tail counterWidth comparisonIndex historyIndex x hcompare hvZero
      (UnitaryCircuit.Realizes.injective hprogram)

/-- On clean work in active terminating mode, the total semantic selector
matches the source terminating round on the source-state projection. -/
theorem
    fullRoundWorkKaliskiRoundStep_fromRegisters_eq_source_round_of_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_fromRegisters_eq_source_round_of_v_zero
        tail counterWidth kaliskiSteps paddingSteps comparisonIndex
        historyIndex x hcompare hactive hvZero
  · exact hactive


theorem activeBit_get_eq_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get x = x.active := by
  rfl

/-- In active nonzero mode, the total fixed-round semantic selector reduces
to the nonzero active semantic wrapper. -/
theorem fullRoundWorkKaliskiRoundStep_eq_activeNonzero_of_active_v_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : x.1.1.1.active = true)
    (hvNonzero : x.1.1.1.v.val ≠ 0) :
    fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      fullRoundWorkKaliskiActiveNonzeroRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
        tail counterWidth comparisonIndex historyIndex x hvNonzero
  · exact hactive

/-- In the active nonzero low-`u` false case, the active-guarded latch/body
route agrees with the total fixed-round semantic selector. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_kaliskiRound_of_uLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : x.1.1.1.active = true)
    (hvNonzero : x.1.1.1.v.val ≠ 0)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkKaliskiRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_false
      tail counterWidth comparisonIndex historyIndex workIndex
      x hcontrol hwork huLow]
  rw [← fullRoundWorkKaliskiRoundStep_eq_activeNonzero_of_active_v_nonzero
    tail counterWidth comparisonIndex historyIndex x hactive hvNonzero]

/-- In the active nonzero low-`u` true and low-`v` false case, the
active-guarded latch/body route agrees with the total fixed-round semantic
selector. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_kaliskiRound_of_uLow_true_vLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : x.1.1.1.active = true)
    (hvNonzero : x.1.1.1.v.val ≠ 0)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkKaliskiRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_true_vLow_false
      tail counterWidth comparisonIndex historyIndex workIndex
      x hcontrol hwork huLow hvLow]
  rw [← fullRoundWorkKaliskiRoundStep_eq_activeNonzero_of_active_v_nonzero
    tail counterWidth comparisonIndex historyIndex x hactive hvNonzero]

/-- In the active clean odd-odd `v < u` case, active-guarded latch/body agrees
with the total fixed-round semantic selector up to the remaining counter
carry-in latch flip. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_kaliskiRound_clean_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hvNonzero : x.v.val ≠ 0)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkKaliskiRoundStep
          tail counterWidth comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)) := by
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hlt hcontrolWork hactive]
  have hactiveRound :
      ((((x, cleanComparisonWork tail.succ), work), counterWork).1.1.1.active) =
        true := by
    simpa [coeffAdderActiveBit, liftComparisonStateBitToCoeffAdderWork,
      liftedActiveBit, liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit, RegisterBits.activeBit_get] using
      hactive
  have hround :=
    fullRoundWorkKaliskiRoundStep_eq_activeNonzero_of_active_v_nonzero
      tail counterWidth comparisonIndex historyIndex
      (((x, cleanComparisonWork tail.succ), work), counterWork)
      hactiveRound hvNonzero
  rw [hround]

/-- In the active clean odd-odd non-`v < u` case, active-guarded latch/body
agrees with the total fixed-round semantic selector up to the remaining
counter carry-in latch flip. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_kaliskiRound_clean_not_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hvNonzero : x.v.val ≠ 0)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkKaliskiRoundStep
          tail counterWidth comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)) := by
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hnlt hcontrolWork hactive]
  have hactiveRound :
      ((((x, cleanComparisonWork tail.succ), work), counterWork).1.1.1.active) =
        true := by
    simpa [coeffAdderActiveBit, liftComparisonStateBitToCoeffAdderWork,
      liftedActiveBit, liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit, RegisterBits.activeBit_get] using
      hactive
  have hround :=
    fullRoundWorkKaliskiRoundStep_eq_activeNonzero_of_active_v_nonzero
      tail counterWidth comparisonIndex historyIndex
      (((x, cleanComparisonWork tail.succ), work), counterWork)
      hactiveRound hvNonzero
  rw [hround]

/-- Flipping the full-round counter carry-in latch only changes the
counter-increment work component, leaving the register/comparison/coefficient
state untouched. -/
theorem fullRoundWorkCounterCarryInBit_flip_coeffState
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    ((fullRoundWorkCounterCarryInBit tail counterWidth).flip x).1 = x.1 := by
  simp [fullRoundWorkCounterCarryInBit,
    liftCounterIncrementWorkBitToFullRoundWork,
    BinaryLabelEncoding.prodRightBit]

/-- In the active clean odd-odd `v < u` case, the active-guarded latch/body
route and total fixed-round semantic selector agree on the full
register/comparison/coefficient state; the remaining carry-in latch flip lives
only in counter work. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hvNonzero : x.v.val ≠ 0)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      (fullRoundWorkKaliskiRoundStep
        tail counterWidth comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1 := by
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hlt hcontrolWork hactive]
  rw [fullRoundWorkCounterCarryInBit_flip_coeffState]

/-- In the active clean odd-odd non-`v < u` case, the active-guarded latch/body
route and total fixed-round semantic selector agree on the full
register/comparison/coefficient state; the remaining carry-in latch flip lives
only in counter work. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_not_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hvNonzero : x.v.val ≠ 0)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      (fullRoundWorkKaliskiRoundStep
        tail counterWidth comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1 := by
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hnlt hcontrolWork hactive]
  rw [fullRoundWorkCounterCarryInBit_flip_coeffState]

/-- In the active nonzero odd-odd `v < u` case, the folded concrete active-only
route agrees with the total semantic round on the register/comparison/
coefficient state.  The only remaining difference is the private counter
carry-in latch. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hscratchA : x.scratchA = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1 =
      (fullRoundWorkKaliskiRoundStep
        tail counterWidth comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1 := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero]
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (coeffAdderCarryInWorkBit tail.succ).get
          (cleanCoeffAdderWork tail.succ) = false
    rfl
  exact
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x
      (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth)
      (fullRoundWorkCounterCarryInBit_get_clean tail counterWidth x)
      (fullRoundWorkCounterCarryWorkBit_get_clean
        tail counterWidth workIndex x)
      hscratchA hcompare hfinal huOdd hvOdd hvNonzero hlt hcontrolWork
      hactiveCoeff

/-- In the active nonzero odd-odd non-`v < u` case, the folded concrete
active-only route agrees with the total semantic round on the register/
comparison/coefficient state.  The only remaining difference is the private
counter carry-in latch. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_not_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hscratchA : x.scratchA = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1 =
      (fullRoundWorkKaliskiRoundStep
        tail counterWidth comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1 := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero]
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (coeffAdderCarryInWorkBit tail.succ).get
          (cleanCoeffAdderWork tail.succ) = false
    rfl
  exact
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x
      (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth)
      (fullRoundWorkCounterCarryInBit_get_clean tail counterWidth x)
      (fullRoundWorkCounterCarryWorkBit_get_clean
        tail counterWidth workIndex x)
      hscratchA hcompare hfinal huOdd hvOdd hvNonzero hnlt hcontrolWork
      hactiveCoeff

/-- In the active nonzero clean case, the folded concrete active-only route
preserves every history slot except the selected target slot. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_historyBit_of_ne_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (target observed : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0)
    (hscratchA : x.scratchA = false)
    (hne : target ≠ observed) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex target workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1 =
      (RegisterBits.historyBit tail.succ counterWidth observed).get x := by
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex target workIndex x hcompare
      hvNonzero]
  let input : RegistersWithFullRoundWork tail.succ counterWidth :=
    (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  have hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get input = false :=
    fullRoundWorkCounterCarryInBit_get_clean tail counterWidth x
  have hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
          input = false :=
    fullRoundWorkCounterCarryWorkBit_get_clean
      tail counterWidth workIndex x
  have hactiveFull :
      (fullRoundWorkActiveBit tail counterWidth).get input = true := by
    change (coeffAdderActiveBit tail.succ counterWidth).get
        ((x, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ) = true
    change x.active = true
    exact hactive
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (coeffAdderCarryInWorkBit tail.succ).get
          (cleanCoeffAdderWork tail.succ) = false
    rfl
  by_cases huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get input.1 =
        false
  · rw [
      fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_uLow_false
        tail counterWidth comparisonIndex target workIndex input
        hcontrol hcounterWork huLow]
    exact
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
        tail counterWidth comparisonIndex target observed hne input
  · have huLowTrue :
        (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get input.1 =
          true := by
      cases h :
          (coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get input.1
      · exact False.elim (huLow h)
      · rfl
    by_cases hvLow :
        (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get input.1 =
          false
    · rw [
        fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_uLow_true_vLow_false
          tail counterWidth comparisonIndex target workIndex input
          hcontrol hcounterWork huLowTrue hvLow]
      exact
        fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
          tail counterWidth comparisonIndex target observed hne input
    · have hvLowTrue :
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get input.1 =
            true := by
        cases h :
            (coeffAdderVBit tail.succ counterWidth
              (WireAddress.littleEndianWire (0 : Fin tail.succ))).get input.1
        · exact False.elim (hvLow h)
        · rfl
      rw [
        fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_compareCarried_of_active_lsb_true
          tail counterWidth comparisonIndex target workIndex input
          hactiveFull hcontrol hcounterWork huLowTrue hvLowTrue]
      rw [fullRoundWorkCounterCarryInBit_flip_coeffState]
      exact
        fullRoundWorkCompareCarriedHistoryBitOfNeClean
          tail counterWidth comparisonIndex target observed hne x
          (cleanCoeffAdderWork tail.succ)
          (cleanCounterIncrementWork counterWidth)
          hscratchA hcontrolWork

/-- The concrete selected branch-code/history/aux-shift dispatch's `uEven`
history readout agrees with the source-level `RoundState.historyBit` once the
concrete low-`u` selector bit chooses the even branch. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_uEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
  have hbranch :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).historyBit =
        false := by
    rw [Branch.fromCoeffWorkSignals_historyBit_eq_branch_bits_disjoint]
    simp [huLow]
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        false := by
    apply RoundState.historyBit_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hmain, hhistory, hactive, hbranch, hsource]
  simp

/-- The concrete selected branch-code/history/aux-shift dispatch's `vEven`
history readout agrees with the source-level `RoundState.historyBit` once the
concrete low readouts choose the even-`v` branch. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_vEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
  have hbranch :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).historyBit =
        true := by
    rw [Branch.fromCoeffWorkSignals_historyBit_eq_branch_bits_disjoint]
    simp [huLow, hvLow]
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        true := by
    apply RoundState.historyBit_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hmain, hhistory, hactive, hbranch, hsource]
  simp

/-- The concrete selected branch-code/history/aux-shift dispatch's `uEven`
`u` readout agrees with the source-level fixed round. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u_uEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        true := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow]
  have hwrittenU : written.1.1.u = x.1.1.u := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_u]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_u
      tail counterWidth tempIndex x
  have hlsbWritten : written.1.1.u.val.testBit (0 : Nat) = false := by
    rw [hwrittenU]
    exact huEven
  have hword :=
    coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hdispatch]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.u.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).u
  rw [hword, hwrittenU, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The concrete selected branch-code/history/aux-shift dispatch's `uEven`
`s` readout agrees with the source-level fixed round under the explicit
no-overflow coefficient-doubling guard. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff_uEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        true := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow]
  have hwrittenS : written.1.1.sCoeff = x.1.1.sCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_sCoeff
      tail counterWidth tempIndex x
  have hmsbWritten :
      written.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenS]
    exact hmsb
  have hword :=
    coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
      tail.succ counterWidth written hmsbWritten
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  have hdoubleVal :
      (wordDouble (tail.succ + 1) x.1.1.sCoeff).val =
        2 * x.1.1.sCoeff.val :=
    wordDouble_val_of_no_overflow (tail.succ + 1) x.1.1.sCoeff hdouble
  rw [hdispatch]
  change
      (coeffWorkUDiv2ThenSMul2Step
        tail.succ counterWidth written).1.1.sCoeff.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).sCoeff
  rw [hword, hwrittenS, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The concrete selected branch-code/history/aux-shift dispatch's `vEven`
`v` readout agrees with the source-level fixed round. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v_vEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        false := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow, hvLow]
  have hwrittenV : written.1.1.v = x.1.1.v := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_v]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_v
      tail counterWidth tempIndex x
  have hlsbWritten : written.1.1.v.val.testBit (0 : Nat) = false := by
    rw [hwrittenV]
    exact hvEven
  have hword :=
    coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hdispatch]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.v.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).v
  rw [hword, hwrittenV, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The concrete selected branch-code/history/aux-shift dispatch's `vEven`
`r` readout agrees with the source-level fixed round under the explicit
no-overflow coefficient-doubling guard. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff_vEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        false := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow, hvLow]
  have hwrittenR : written.1.1.rCoeff = x.1.1.rCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_rCoeff
      tail counterWidth tempIndex x
  have hmsbWritten :
      written.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenR]
    exact hmsb
  have hword :=
    coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
      tail.succ counterWidth written hmsbWritten
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  have hdoubleVal :
      (wordDouble (tail.succ + 1) x.1.1.rCoeff).val =
        2 * x.1.1.rCoeff.val :=
    wordDouble_val_of_no_overflow (tail.succ + 1) x.1.1.rCoeff hdouble
  rw [hdispatch]
  change
      (coeffWorkVDiv2ThenRMul2Step
        tail.succ counterWidth written).1.1.rCoeff.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).rCoeff
  rw [hword, hwrittenR, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the active clean odd-odd `v < u` case, the carried selector-selected
odd wrapper's selected history write agrees with the source-level
`RoundState.historyBit`. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkSelectedOddCarriedDispatch_get_history_uGreater_clean
      tail counterWidth bit historyIndex x work hscratchA hscratchB hcompare
      hfinal huOdd hvOdd hlt hcontrolWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        true := by
    apply RoundState.historyBit_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · simpa [RoundState.fromRegisters] using hlt
  rw [hmain, hhistory, hsource, hactive]
  simp

/-- In the active clean odd-odd non-`v < u` case, the carried selector-selected
odd wrapper's selected history write agrees with the source-level
`RoundState.historyBit`. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkSelectedOddCarriedDispatch_get_history_vLe_clean
      tail counterWidth bit historyIndex x work hscratchA hscratchB hcompare
      hfinal huOdd hvOdd hnlt hcontrolWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        false := by
    apply RoundState.historyBit_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · simpa [RoundState.fromRegisters] using hnlt
  rw [hmain, hhistory, hsource]

/-- In the active clean odd-odd `v < u` case, the concrete compare-carried odd
route's selected history write agrees with the source-level
`RoundState.historyBit`. -/
theorem
    coeffWorkCompareCarriedDispatch_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkCompareCarriedDispatch_get_history_uGreater_clean
      tail counterWidth bit historyIndex x work hscratchA hscratchB hcompare
      hfinal hlt hcontrolWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        true := by
    apply RoundState.historyBit_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · simpa [RoundState.fromRegisters] using hlt
  rw [hmain, hhistory, hsource, hactive]
  simp

/-- In the active clean odd-odd non-`v < u` case, the concrete compare-carried
odd route's selected history readout agrees with the source-level
`RoundState.historyBit`. -/
theorem
    coeffWorkCompareCarriedDispatch_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkCompareCarriedDispatch_get_history_vLe_clean
      tail counterWidth bit historyIndex x work hscratchA hscratchB hcompare
      hfinal hnlt hcontrolWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        false := by
    apply RoundState.historyBit_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · simpa [RoundState.fromRegisters] using hnlt
  rw [hmain, hhistory, hsource]

/-- In the active clean odd-odd `v < u` case, the concrete compare-carried odd
route's `u` readout agrees with the source-level fixed round. -/
theorem coeffWorkCompareCarriedDispatch_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkCompareCarriedDispatch_get_u_uGreater_wordHalf_sub_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactiveCoeff hsourceWork hlsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have hsubVal : (x.u - x.v).val = x.u.val - x.v.val := by
    exact Fin.sub_val_of_le (le_of_lt hlt)
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters, hsubVal]

/-- In the active clean odd-odd `v < u` case, the concrete compare-carried odd
route's `r` readout agrees with the source-level fixed round under the
explicit no-overflow coefficient-add guard. -/
theorem
    coeffWorkCompareCarriedDispatch_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkCompareCarriedDispatch_get_rCoeff_uGreater_add_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactiveCoeff hcoeffWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have haddVal :
      (x.rCoeff + x.sCoeff).val = x.rCoeff.val + x.sCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  rw [hword, hround, haddVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the active clean odd-odd `v < u` case, the concrete compare-carried odd
route's `s` readout agrees with the source-level fixed round under the
explicit no-overflow coefficient-doubling guard. -/
theorem
    coeffWorkCompareCarriedDispatch_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkCompareCarriedDispatch_get_sCoeff_uGreater_wordDouble_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactiveCoeff hmsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have hdoubleVal :
      (wordDouble (tail.succ + 1) x.sCoeff).val = 2 * x.sCoeff.val :=
    wordDouble_val_of_no_overflow (tail.succ + 1) x.sCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the active clean odd-odd non-`v < u` case, the concrete compare-carried
odd route's `v` readout agrees with the source-level fixed round. -/
theorem coeffWorkCompareCarriedDispatch_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkCompareCarriedDispatch_get_v_vLe_wordHalf_sub_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactiveCoeff hsourceWork hlsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have hsubVal : (x.v - x.u).val = x.v.val - x.u.val := by
    exact Fin.sub_val_of_le (Nat.le_of_not_gt hnlt)
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters, hsubVal]

/-- In the active clean odd-odd non-`v < u` case, the concrete compare-carried
odd route's `s` readout agrees with the source-level fixed round under the
explicit no-overflow coefficient-add guard. -/
theorem coeffWorkCompareCarriedDispatch_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkCompareCarriedDispatch_get_sCoeff_vLe_add_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactiveCoeff hcoeffWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have haddVal :
      (x.sCoeff + x.rCoeff).val = x.sCoeff.val + x.rCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  rw [hword, hround, haddVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters, Nat.add_comm]

/-- In the active clean odd-odd non-`v < u` case, the concrete compare-carried
odd route's `r` readout agrees with the source-level fixed round under the
explicit no-overflow coefficient-doubling guard. -/
theorem coeffWorkCompareCarriedDispatch_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkCompareCarriedDispatch_get_rCoeff_vLe_wordDouble_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactiveCoeff hmsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have hdoubleVal :
      (wordDouble (tail.succ + 1) x.rCoeff).val = 2 * x.rCoeff.val :=
    wordDouble_val_of_no_overflow (tail.succ + 1) x.rCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The lifted concrete compare-carried odd route's `uGreater` history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkCompareCarriedDispatch_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_history_uGreater_eq_sourceHistoryBit_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hscratchB hcompare hfinal hactive hhistory huOdd hvOdd hlt
        hcontrolWork

/-- The lifted concrete compare-carried odd route's `vLe` history readout
agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkCompareCarriedDispatch_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_history_vLe_eq_sourceHistoryBit_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hscratchB hcompare hfinal hactive hhistory huOdd hvOdd hnlt
        hcontrolWork

/-- The lifted concrete compare-carried odd route's `uGreater` `u` readout
agrees with the source-level fixed round. -/
theorem fullRoundWorkCompareCarriedDispatch_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_u_uGreater_eq_sourceRound_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hcompare hfinal hactive huOdd hvOdd hlt hcontrolWork
        hsourceWork hlsb

/-- The lifted concrete compare-carried odd route's `uGreater` `r` readout
agrees with the source-level fixed round. -/
theorem
    fullRoundWorkCompareCarriedDispatch_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_rCoeff_uGreater_eq_sourceRound_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hcompare hfinal hactive huOdd hvOdd hlt hcontrolWork
        hcoeffWork hadd

/-- The lifted concrete compare-carried odd route's `uGreater` `s` readout
agrees with the source-level fixed round. -/
theorem
    fullRoundWorkCompareCarriedDispatch_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_sCoeff_uGreater_eq_sourceRound_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hcompare hfinal hactive huOdd hvOdd hlt hcontrolWork hmsb
        hdouble

/-- The lifted concrete compare-carried odd route's `vLe` `v` readout agrees
with the source-level fixed round. -/
theorem fullRoundWorkCompareCarriedDispatch_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_v_vLe_eq_sourceRound_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hcompare hfinal hactive huOdd hvOdd hnlt hcontrolWork
        hsourceWork hlsb

/-- The lifted concrete compare-carried odd route's `vLe` `s` readout agrees
with the source-level fixed round. -/
theorem fullRoundWorkCompareCarriedDispatch_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_sCoeff_vLe_eq_sourceRound_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hcompare hfinal hactive huOdd hvOdd hnlt hcontrolWork
        hcoeffWork hadd

/-- The lifted concrete compare-carried odd route's `vLe` `r` readout agrees
with the source-level fixed round. -/
theorem fullRoundWorkCompareCarriedDispatch_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareCarriedDispatch_get_rCoeff_vLe_eq_sourceRound_clean
        tail counterWidth bit historyIndex kaliskiSteps paddingSteps x work
        hscratchA hcompare hfinal hactive huOdd hvOdd hnlt hcontrolWork hmsb
        hdouble

/-- The nonzero-active selected wrapper's `uEven` history readout agrees with
the source-level `RoundState.historyBit`. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_uEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive hhistory huLow hvNonzero huEven

/-- The nonzero-active selected wrapper's `vEven` history readout agrees with
the source-level `RoundState.historyBit`. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_vEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive hhistory huLow hvLow hvNonzero
      huOdd hvEven

/-- The nonzero-active selected wrapper's `uGreater` carried odd history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_history_uGreater_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hscratchB hcompare hfinal hactive hhistory huOdd
      hvOdd hlt hcontrolWork

/-- The nonzero-active selected wrapper's `vLe` carried odd history readout
agrees with the source-level `RoundState.historyBit`. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_history_vLe_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hscratchB hcompare hfinal hactive hhistory huOdd
      hvOdd hnlt hcontrolWork

/-- In the active clean odd-odd `v < u` case, the carried selector-selected
odd wrapper's `u` readout agrees with the source-level fixed round. -/
theorem coeffWorkSelectedOddCarriedDispatch_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkSelectedOddCarriedDispatch_get_u_uGreater_wordHalf_sub_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactiveCoeff hsourceWork hlsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have hsubVal : (x.u - x.v).val = x.u.val - x.v.val := by
    exact Fin.sub_val_of_le (le_of_lt hlt)
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters, hsubVal]

/-- In the active clean odd-odd `v < u` case, the carried selector-selected
odd wrapper's `r` readout agrees with the source-level fixed round under the
explicit no-overflow coefficient-add guard. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkSelectedOddCarriedDispatch_get_rCoeff_uGreater_add_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactiveCoeff hcoeffWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have haddVal :
      (x.rCoeff + x.sCoeff).val = x.rCoeff.val + x.sCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  rw [hword, hround, haddVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the active clean odd-odd `v < u` case, the carried selector-selected
odd wrapper's `s` readout agrees with the source-level fixed round under the
explicit no-overflow coefficient-doubling guard. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkSelectedOddCarriedDispatch_get_sCoeff_uGreater_wordDouble_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactiveCoeff hmsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have hdoubleVal :
      (wordDouble (tail.succ + 1) x.sCoeff).val = 2 * x.sCoeff.val :=
    wordDouble_val_of_no_overflow (tail.succ + 1) x.sCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the active clean odd-odd non-`v < u` case, the carried
selector-selected odd wrapper's `v` readout agrees with the source-level fixed
round. -/
theorem coeffWorkSelectedOddCarriedDispatch_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkSelectedOddCarriedDispatch_get_v_vLe_wordHalf_sub_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactiveCoeff hsourceWork hlsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have hsubVal : (x.v - x.u).val = x.v.val - x.u.val := by
    exact Fin.sub_val_of_le (Nat.le_of_not_gt hnlt)
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters, hsubVal]

/-- In the active clean odd-odd non-`v < u` case, the carried
selector-selected odd wrapper's `s` readout agrees with the source-level fixed
round under the explicit no-overflow coefficient-add guard. -/
theorem coeffWorkSelectedOddCarriedDispatch_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkSelectedOddCarriedDispatch_get_sCoeff_vLe_add_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactiveCoeff hcoeffWork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have haddVal :
      (x.sCoeff + x.rCoeff).val = x.sCoeff.val + x.rCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  rw [hword, hround, haddVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters, Nat.add_comm]

/-- In the active clean odd-odd non-`v < u` case, the carried
selector-selected odd wrapper's `r` readout agrees with the source-level fixed
round under the explicit no-overflow coefficient-doubling guard. -/
theorem coeffWorkSelectedOddCarriedDispatch_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hword :=
    coeffWorkSelectedOddCarriedDispatch_get_rCoeff_vLe_wordDouble_clean
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactiveCoeff hmsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have hdoubleVal :
      (wordDouble (tail.succ + 1) x.rCoeff).val = 2 * x.rCoeff.val :=
    wordDouble_val_of_no_overflow (tail.succ + 1) x.rCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The nonzero-active selected wrapper's `uEven` `u` readout agrees with the
source-level fixed round. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u_uEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- The nonzero-active selected wrapper's `uEven` `s` readout agrees with the
source-level fixed round under the explicit no-overflow coefficient-doubling
guard. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff_uEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven hmsb
      hdouble

/-- The nonzero-active selected wrapper's `vEven` `v` readout agrees with the
source-level fixed round. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v_vEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd
      hvEven

/-- The nonzero-active selected wrapper's `vEven` `r` readout agrees with the
source-level fixed round under the explicit no-overflow coefficient-doubling
guard. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff_vEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd
      hvEven hmsb hdouble

/-- The nonzero-active selected wrapper's odd `uGreater` `u` readout agrees
with the source-level fixed round. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hlt hcontrolWork
      hsourceWork hlsb

/-- The nonzero-active selected wrapper's odd `uGreater` `r` readout agrees
with the source-level fixed round under the explicit no-overflow coefficient-add
guard. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_rCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hlt hcontrolWork
      hcoeffWork hadd

/-- The nonzero-active selected wrapper's odd `uGreater` `s` readout agrees
with the source-level fixed round under the explicit no-overflow coefficient-
doubling guard. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_sCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hlt hcontrolWork
      hmsb hdouble

/-- The nonzero-active selected wrapper's odd `vLe` `v` readout agrees with the
source-level fixed round. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_v_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hnlt hcontrolWork
      hsourceWork hlsb

/-- The nonzero-active selected wrapper's odd `vLe` `s` readout agrees with the
source-level fixed round under the explicit no-overflow coefficient-add guard.
-/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_sCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hnlt hcontrolWork
      hcoeffWork hadd

/-- The nonzero-active selected wrapper's odd `vLe` `r` readout agrees with the
source-level fixed round under the explicit no-overflow coefficient-doubling
guard. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_rCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hnlt hcontrolWork
      hmsb hdouble

/-- The lifted nonzero-active selected wrapper's `uEven` history readout agrees
with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive hhistory huLow hvNonzero huEven

/-- The lifted nonzero-active selected wrapper's `vEven` history readout agrees
with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive hhistory huLow hvLow hvNonzero
      huOdd hvEven

/-- The lifted nonzero-active selected wrapper's odd `uGreater` history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hscratchB hcompare hfinal hactive hhistory huLow
      hvLow huOdd hvOdd hlt hcontrolWork

/-- The lifted nonzero-active selected wrapper's odd `vLe` history readout
agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hscratchB hcompare hfinal hactive hhistory huLow
      hvLow huOdd hvOdd hnlt hcontrolWork

/-- The lifted nonzero-active selected wrapper's `uEven` `u` readout agrees
with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- The lifted nonzero-active selected wrapper's `uEven` `s` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven hmsb
      hdouble

/-- The lifted nonzero-active selected wrapper's `vEven` `v` readout agrees
with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd
      hvEven

/-- The lifted nonzero-active selected wrapper's `vEven` `r` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd
      hvEven hmsb hdouble

/-- The lifted nonzero-active selected wrapper's odd `uGreater` `u` readout
agrees with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hlt
      hcontrolWork hsourceWork hlsb

/-- The lifted nonzero-active selected wrapper's odd `uGreater` `r` readout
agrees with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hlt
      hcontrolWork hcoeffWork hadd

/-- The lifted nonzero-active selected wrapper's odd `uGreater` `s` readout
agrees with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hlt
      hcontrolWork hmsb hdouble

/-- The lifted nonzero-active selected wrapper's odd `vLe` `v` readout agrees
with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hnlt
      hcontrolWork hsourceWork hlsb

/-- The lifted nonzero-active selected wrapper's odd `vLe` `s` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hnlt
      hcontrolWork hcoeffWork hadd

/-- The lifted nonzero-active selected wrapper's odd `vLe` `r` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hnlt
      hcontrolWork hmsb hdouble

/-- On clean active nonzero inputs, the lifted nonzero-active selected wrapper
keeps the source active flag set. -/
theorem fullRoundWorkKaliskiActiveNonzeroRoundStep_get_active_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.active =
      true := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  by_cases huOdd : x.u.val.testBit (0 : Nat) = true
  · have huLow :
        (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
            ((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ) = true := by
      rw [coeffAdderUBit_get_littleEndian_zero]
      exact huOdd
    by_cases hvOdd : x.v.val.testBit (0 : Nat) = true
    · have hvLow :
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
              ((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ) = true := by
        rw [coeffAdderVBit_get_littleEndian_zero]
        exact hvOdd
      by_cases hlt : x.v.val < x.u.val
      · rw [fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_lt
          tail counterWidth comparisonIndex historyIndex x
          (cleanCoeffAdderWork tail.succ)
          (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
          huOdd hvOdd hlt hcontrolWork hactiveCoeff]
        change
            (coeffAdderActiveBit tail.succ counterWidth).get
              (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
                tail counterWidth comparisonIndex historyIndex
                ((x, cleanComparisonWork tail.succ),
                  cleanCoeffAdderWork tail.succ)) =
            true
        exact
          coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_active_clean_lt
            tail counterWidth comparisonIndex historyIndex x
            (cleanCoeffAdderWork tail.succ) hscratchA hcompare hfinal hlt
            hcontrolWork hactiveCoeff
      · rw [fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_not_lt
          tail counterWidth comparisonIndex historyIndex x
          (cleanCoeffAdderWork tail.succ)
          (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
          huOdd hvOdd hlt hcontrolWork hactiveCoeff]
        change
            (coeffAdderActiveBit tail.succ counterWidth).get
              (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
                tail counterWidth comparisonIndex historyIndex
                ((x, cleanComparisonWork tail.succ),
                  cleanCoeffAdderWork tail.succ)) =
            true
        exact
          coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_active_clean_not_lt
            tail counterWidth comparisonIndex historyIndex x
            (cleanCoeffAdderWork tail.succ) hscratchA hcompare hfinal hlt
            hcontrolWork hactiveCoeff
    · have hvEven : x.v.val.testBit (0 : Nat) = false := by
        cases hv : x.v.val.testBit (0 : Nat) <;> simp_all
      have hvLow :
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
              ((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ) = false := by
        rw [coeffAdderVBit_get_littleEndian_zero]
        exact hvEven
      rw [
        fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
          tail counterWidth comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)
          huLow hvLow]
      change
          (coeffAdderActiveBit tail.succ counterWidth).get
            (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
              tail counterWidth comparisonIndex historyIndex
              ((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ)) =
          true
      rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active]
      exact hactiveCoeff
  · have huEven : x.u.val.testBit (0 : Nat) = false := by
      cases hu : x.u.val.testBit (0 : Nat) <;> simp_all
    have huLow :
        (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
            ((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ) = false := by
      rw [coeffAdderUBit_get_littleEndian_zero]
      exact huEven
    rw [
      fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
        tail counterWidth comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)
        huLow]
    change
        (coeffAdderActiveBit tail.succ counterWidth).get
          (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
            tail counterWidth comparisonIndex historyIndex
            ((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ)) =
        true
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active]
    exact hactiveCoeff

/-- On clean active nonzero inputs, the concrete active-only route keeps the
source active flag set. -/
theorem fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_active_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep tail counterWidth
        comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.active =
      true := by
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have hroundActive :
      (((x, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth).1.1.1.active = true := by
    exact hactive
  by_cases huOdd : x.u.val.testBit (0 : Nat) = true
  · have huLow :
        (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
            ((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ) = true := by
      rw [coeffAdderUBit_get_littleEndian_zero]
      exact huOdd
    by_cases hvOdd : x.v.val.testBit (0 : Nat) = true
    · have hvLow :
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
              ((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ) = true := by
        rw [coeffAdderVBit_get_littleEndian_zero]
        exact hvOdd
      by_cases hlt : x.v.val < x.u.val
      · rw [
          fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_lt
            tail counterWidth comparisonIndex historyIndex workIndex x
            hcompare hfinal hscratchA hactiveBit huOdd hvOdd hlt]
        rw [
          fullRoundWorkKaliskiRoundStep_eq_activeNonzero_of_active_v_nonzero
            tail counterWidth comparisonIndex historyIndex
            (((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ),
              cleanCounterIncrementWork counterWidth)
            hroundActive hvNonzero]
        exact
          fullRoundWorkKaliskiActiveNonzeroRoundStep_get_active_clean
            tail counterWidth comparisonIndex historyIndex x hscratchA
            hcompare hfinal hactiveBit
      · rw [
          fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_not_lt
            tail counterWidth comparisonIndex historyIndex workIndex x
            hcompare hfinal hscratchA hactiveBit huOdd hvOdd hlt]
        rw [
          fullRoundWorkKaliskiRoundStep_eq_activeNonzero_of_active_v_nonzero
            tail counterWidth comparisonIndex historyIndex
            (((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ),
              cleanCounterIncrementWork counterWidth)
            hroundActive hvNonzero]
        exact
          fullRoundWorkKaliskiActiveNonzeroRoundStep_get_active_clean
            tail counterWidth comparisonIndex historyIndex x hscratchA
            hcompare hfinal hactiveBit
    · have hvEven : x.v.val.testBit (0 : Nat) = false := by
        cases hv : x.v.val.testBit (0 : Nat) <;> simp_all
      have hvLow :
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
              ((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ) = false := by
        rw [coeffAdderVBit_get_littleEndian_zero]
        exact hvEven
      rw [
        fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
          tail counterWidth comparisonIndex historyIndex workIndex x hcompare
          hvNonzero]
      rw [
        fullRoundWorkActiveOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_true_vLow_false
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)
          (fullRoundWorkCounterCarryInBit_get_clean tail counterWidth x)
          (fullRoundWorkCounterCarryWorkBit_get_clean
            tail counterWidth workIndex x)
          huLow hvLow]
      exact
        fullRoundWorkKaliskiActiveNonzeroRoundStep_get_active_clean
          tail counterWidth comparisonIndex historyIndex x hscratchA hcompare
          hfinal hactiveBit
  · have huEven : x.u.val.testBit (0 : Nat) = false := by
      cases hu : x.u.val.testBit (0 : Nat) <;> simp_all
    have huLow :
        (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
            ((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ) = false := by
      rw [coeffAdderUBit_get_littleEndian_zero]
      exact huEven
    rw [
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
        tail counterWidth comparisonIndex historyIndex workIndex x hcompare
        hvNonzero huLow]
    exact
      fullRoundWorkKaliskiActiveNonzeroRoundStep_get_active_clean
        tail counterWidth comparisonIndex historyIndex x hscratchA hcompare
        hfinal hactiveBit

/-- In the nonzero `uEven` branch, the active-only selector's history readout
agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
          comparisonIndex historyIndex (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive hhistory huLow
      hvNonzero huEven

/-- In the nonzero `vEven` branch, the active-only selector's history readout
agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
          comparisonIndex historyIndex (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive hhistory huLow hvLow
      hvNonzero huOdd hvEven

/-- In the nonzero odd `uGreater` branch, the active-only selector's history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hscratchB hcompare hfinal hactive
      hhistory huLow hvLow huOdd hvOdd hlt hcontrolWork

/-- In the nonzero odd `vLe` branch, the active-only selector's history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hscratchB hcompare hfinal hactive
      hhistory huLow hvLow huOdd hvOdd hnlt hcontrolWork

/-- In the nonzero `uEven` branch, the active-only selector's `u` readout
agrees with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- In the nonzero `uEven` branch, the active-only selector's `s` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvNonzero
      huEven hmsb hdouble

/-- In the nonzero `vEven` branch, the active-only selector's `v` readout
agrees with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvLow hvNonzero
      huOdd hvEven

/-- In the nonzero `vEven` branch, the active-only selector's `r` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvLow hvNonzero
      huOdd hvEven hmsb hdouble

/-- In the nonzero odd `uGreater` branch, the active-only selector's `u`
readout agrees with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hlt hcontrolWork hsourceWork hlsb

/-- In the nonzero odd `uGreater` branch, the active-only selector's `r`
readout agrees with the source-level fixed round under the explicit
no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hlt hcontrolWork hcoeffWork hadd

/-- In the nonzero odd `uGreater` branch, the active-only selector's `s`
readout agrees with the source-level fixed round under the explicit
no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hlt hcontrolWork hmsb hdouble

/-- In the nonzero odd `vLe` branch, the active-only selector's `v` readout
agrees with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hnlt hcontrolWork hsourceWork hlsb

/-- In the nonzero odd `vLe` branch, the active-only selector's `s` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hnlt hcontrolWork hcoeffWork hadd

/-- In the nonzero odd `vLe` branch, the active-only selector's `r` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hnlt hcontrolWork hmsb hdouble

/-- In the nonzero `uEven` branch, the active/inactive semantic selector's
history readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive
        hhistory huLow hvNonzero huEven
  · exact hactive

/-- In the nonzero `vEven` branch, the active/inactive semantic selector's
history readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive
        hhistory huLow hvLow hvNonzero huOdd hvEven
  · exact hactive

/-- In the nonzero odd `uGreater` branch, the active/inactive semantic
selector's history readout agrees with the source-level
`RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hscratchB hcompare
        hfinal hactive hhistory huLow hvLow huOdd hvOdd hlt hcontrolWork
  · exact hactive

/-- In the nonzero odd `vLe` branch, the active/inactive semantic selector's
history readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiRoundStep tail counterWidth
          comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hscratchB hcompare
        hfinal hactive hhistory huLow hvLow huOdd hvOdd hnlt
        hcontrolWork
  · exact hactive

/-- In the nonzero `uEven` branch, the active/inactive semantic selector's
`u` readout agrees with the source-level fixed round. -/
theorem fullRoundWorkKaliskiRoundStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_uEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvNonzero huEven
  · exact hactive

/-- In the nonzero `uEven` branch, the active/inactive semantic selector's
`s` readout agrees with the source-level fixed round under the explicit
no-overflow guard. -/
theorem fullRoundWorkKaliskiRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvNonzero huEven hmsb hdouble
  · exact hactive

/-- In the nonzero `vEven` branch, the active/inactive semantic selector's
`v` readout agrees with the source-level fixed round. -/
theorem fullRoundWorkKaliskiRoundStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvLow hvNonzero huOdd hvEven
  · exact hactive

/-- In the nonzero `vEven` branch, the active/inactive semantic selector's
`r` readout agrees with the source-level fixed round under the explicit
no-overflow guard. -/
theorem fullRoundWorkKaliskiRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvLow hvNonzero huOdd hvEven hmsb hdouble
  · exact hactive

/-- In the nonzero odd `uGreater` branch, the active/inactive semantic
selector's `u` readout agrees with the source-level fixed round. -/
theorem fullRoundWorkKaliskiRoundStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hlt hcontrolWork hsourceWork hlsb
  · exact hactive

/-- In the nonzero odd `uGreater` branch, the active/inactive semantic
selector's `r` readout agrees with the source-level fixed round under the
explicit no-overflow guard. -/
theorem fullRoundWorkKaliskiRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hlt hcontrolWork hcoeffWork hadd
  · exact hactive

/-- In the nonzero odd `uGreater` branch, the active/inactive semantic
selector's `s` readout agrees with the source-level fixed round under the
explicit no-overflow guard. -/
theorem fullRoundWorkKaliskiRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hlt hcontrolWork hmsb hdouble
  · exact hactive

/-- In the nonzero odd `vLe` branch, the active/inactive semantic selector's
`v` readout agrees with the source-level fixed round. -/
theorem fullRoundWorkKaliskiRoundStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hnlt hcontrolWork hsourceWork hlsb
  · exact hactive

/-- In the nonzero odd `vLe` branch, the active/inactive semantic selector's
`s` readout agrees with the source-level fixed round under the explicit
no-overflow guard. -/
theorem fullRoundWorkKaliskiRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hnlt hcontrolWork hcoeffWork hadd
  · exact hactive

/-- In the nonzero odd `vLe` branch, the active/inactive semantic selector's
`r` readout agrees with the source-level fixed round under the explicit
no-overflow guard. -/
theorem fullRoundWorkKaliskiRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hnlt hcontrolWork hmsb hdouble
  · exact hactive

/-- In the active clean odd-odd `v < u` case, the active-guarded latch/body
route's selected history readout agrees with the source-level
`RoundState.historyBit`. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hscratchB hcompare hfinal hactive hhistory
      huLow hvLow huOdd hvOdd hlt hcontrolWork

/-- In the active clean odd-odd non-`v < u` case, the active-guarded
latch/body route's selected history readout agrees with the source-level
`RoundState.historyBit`. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hnlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hscratchB hcompare hfinal hactive hhistory
      huLow hvLow huOdd hvOdd hnlt hcontrolWork

/-- In the active clean odd-odd `v < u` case, the active-guarded latch/body
route's `u` readout agrees with the source-level fixed round. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow huOdd
      hvOdd hlt hcontrolWork hsourceWork hlsb

/-- In the active clean odd-odd `v < u` case, the active-guarded latch/body
route's `r` readout agrees with the source-level fixed round under the
explicit no-overflow guard. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow huOdd
      hvOdd hlt hcontrolWork hcoeffWork hadd

/-- In the active clean odd-odd `v < u` case, the active-guarded latch/body
route's `s` readout agrees with the source-level fixed round under the
explicit no-overflow guard. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow huOdd
      hvOdd hlt hcontrolWork hmsb hdouble

/-- In the active clean odd-odd non-`v < u` case, the active-guarded
latch/body route's `v` readout agrees with the source-level fixed round. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hnlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_v_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow huOdd
      hvOdd hnlt hcontrolWork hsourceWork hlsb

/-- In the active clean odd-odd non-`v < u` case, the active-guarded
latch/body route's `s` readout agrees with the source-level fixed round under
the explicit no-overflow guard. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hnlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow huOdd
      hvOdd hnlt hcontrolWork hcoeffWork hadd

/-- In the active clean odd-odd non-`v < u` case, the active-guarded
latch/body route's `r` readout agrees with the source-level fixed round under
the explicit no-overflow guard. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x work
      counterWork hcontrol hcounterWork hscratchA hcompare hfinal huOdd hvOdd
      hvNonzero hnlt hcontrolWork hactiveCoeff]
  exact
    fullRoundWorkKaliskiRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow huOdd
      hvOdd hnlt hcontrolWork hmsb hdouble

/-- In the concrete active-only nonzero `uEven` branch, the selected history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_uEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hhistoryCoeff :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false
    exact hhistory
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff hhistoryCoeff huLow hvNonzero
      huEven

/-- In the concrete active-only nonzero `vEven` branch, the selected history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_vEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hhistoryCoeff :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false
    exact hhistory
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow hvLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff hhistoryCoeff huLow hvLow
      hvNonzero huOdd hvEven

/-- In the concrete active-only nonzero `uEven` branch, the `u` readout agrees
with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvNonzero huEven

/-- In the concrete active-only nonzero `uEven` branch, the `s` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvNonzero huEven hmsb
      hdouble

/-- On clean active `uEven` inputs, the path/control route's updated source
readouts match the source active Kaliski round. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uEven
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).u =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).u ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).sCoeff =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).sCoeff := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have huRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hvNonzero
      huEven
  have hsRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hvNonzero
      huEven hmsb hdouble
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using huRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hsRead

/-- In the concrete active-only nonzero `vEven` branch, the `v` readout agrees
with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow hvLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvLow hvNonzero huOdd
      hvEven

/-- In the concrete active-only nonzero `vEven` branch, the `r` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow hvLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvLow hvNonzero huOdd
      hvEven hmsb hdouble

/-- On clean active `vEven` inputs, the path/control route's updated source
readouts match the source active Kaliski round. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vEven
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).v =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).v ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).rCoeff =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).rCoeff := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have hvRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit huOdd
      hvEven hvNonzero
  have hrRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit huOdd
      hvEven hvNonzero hmsb hdouble
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hvRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hrRead

/-- In the concrete active-only odd `uGreater` branch, the selected history
readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (coeffAdderCarryInWorkBit tail.succ).get
          (cleanCoeffAdderWork tail.succ) = false
    rfl
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hscratchB hcompare
      hfinal hactive hhistory huLow hvLow huOdd hvOdd hlt hcontrolWork

/-- In the concrete active-only odd `vLe` branch, the selected history readout
agrees with the source-level `RoundState.historyBit`. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_vLe_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps) := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (coeffAdderCarryInWorkBit tail.succ).get
          (cleanCoeffAdderWork tail.succ) = false
    rfl
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hnlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hscratchB hcompare
      hfinal hactive hhistory huLow hvLow huOdd hvOdd hnlt hcontrolWork

/-- In the concrete active-only odd `uGreater` branch, the `u` readout agrees
with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  have hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    intro k
    exact coeffAdderComparisonCarryPrefixWord_get_clean
      tail.succ counterWidth k x
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hlt hcontrolWork hsourceWork hlsb

/-- In the concrete active-only odd `uGreater` branch, the `r` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  have hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    intro k
    exact liftedCoeffAdderCarryWorkBit_get_clean
      tail.succ counterWidth k (x, cleanComparisonWork tail.succ)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hlt hcontrolWork hcoeffWork hadd

/-- In the concrete active-only odd `uGreater` branch, the `s` readout agrees
with the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hlt hcontrolWork hmsb hdouble

/-- In the concrete active-only odd `vLe` branch, the `v` readout agrees with
the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  have hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    intro k
    exact coeffAdderComparisonCarryPrefixWord_get_clean
      tail.succ counterWidth k x
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hnlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_v_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hnlt hcontrolWork hsourceWork hlsb

/-- In the concrete active-only odd `vLe` branch, the `s` readout agrees with
the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  have hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    intro k
    exact liftedCoeffAdderCarryWorkBit_get_clean
      tail.succ counterWidth k (x, cleanComparisonWork tail.succ)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hnlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hnlt hcontrolWork hcoeffWork hadd

/-- In the concrete active-only odd `vLe` branch, the `r` readout agrees with
the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hnlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hnlt hcontrolWork hmsb hdouble

/-- On clean active odd `uGreater` inputs, the path/control route's updated
source readouts match the source active Kaliski round. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uGreater
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).u =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).u ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).rCoeff =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).rCoeff ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).sCoeff =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).sCoeff := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have huRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hlt
      hlsb
  have hrRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hlt
      hadd
  have hsRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hlt
      hmsb hdouble
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using huRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hrRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hsRead

/-- On clean active odd `vLe` inputs, the path/control route's updated source
readouts match the source active Kaliski round. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vLe
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).v =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).v ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).sCoeff =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).sCoeff ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).rCoeff =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).rCoeff := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have hvRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hnlt
      hlsb
  have hsRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hnlt
      hadd
  have hrRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hnlt
      hmsb hdouble
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hvRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hsRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hrRead

/-- On clean active nonzero inputs, the path/control route's RoundState readout
preserves the nonzero active-round metadata. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_nonzero_metadata
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0) :
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).active =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).active ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).kaliskiSteps =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).kaliskiSteps ∧
    (RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps).paddingSteps =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)).paddingSteps := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).v ≠ 0 := by
    simpa [RoundState.fromRegisters] using hvNonzero
  have hactiveRead :
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1.active =
        true :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_active_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hscratchA
      hcompare hfinal hactive hvNonzero
  have hroundActive :=
    RoundState.round_active_nonzero_active
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps)
      hsourceActive hsourceV
  have hroundKaliskiSteps :=
    RoundState.round_active_nonzero_kaliskiSteps
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps)
      hsourceActive hsourceV
  have hroundPaddingSteps :=
    RoundState.round_active_nonzero_paddingSteps
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps)
      hsourceActive hsourceV
  constructor
  · rw [hroundActive]
    simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hactiveRead
  constructor
  · rw [hroundKaliskiSteps]
    simp [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters]
  · rw [hroundPaddingSteps]
    simp [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters]

/-- On clean active `uEven` inputs, the path/control route's selected history
readout matches the source branch-history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_uEven
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have hread :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_uEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hhistory
      hvNonzero huEven
  rw [fullRoundPathControlWorkRoundStateReadoutRegisters_get_historyBit]
  simpa [coeffAdderHistoryBit, liftedHistoryBit,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using hread

/-- On clean active `vEven` inputs, the path/control route's selected history
readout matches the source branch-history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_vEven
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have hread :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_vEven_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hhistory
      huOdd hvEven hvNonzero
  rw [fullRoundPathControlWorkRoundStateReadoutRegisters_get_historyBit]
  simpa [coeffAdderHistoryBit, liftedHistoryBit,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using hread

/-- On clean active odd `uGreater` inputs, the path/control route's selected
history readout matches the source branch-history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_uGreater
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have hread :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_uGreater_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hfinal hactiveBit
      hhistory huOdd hvOdd hlt
  rw [fullRoundPathControlWorkRoundStateReadoutRegisters_get_historyBit]
  simpa [coeffAdderHistoryBit, liftedHistoryBit,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using hread

/-- On clean active odd `vLe` inputs, the path/control route's selected
history readout matches the source branch-history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_vLe
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have hread :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_vLe_eq_sourceHistoryBit_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hfinal hactiveBit
      hhistory huOdd hvOdd hnlt
  rw [fullRoundPathControlWorkRoundStateReadoutRegisters_get_historyBit]
  simpa [coeffAdderHistoryBit, liftedHistoryBit,
    liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using hread

/-- In the explicit active-round family, the `uEven` branch's selected
history readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hhistory : (coeffAdderHistoryBit n counterWidth historyIndex).get x =
      false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkKaliskiActiveBranchRoundStep_get_history_uEven_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex x hcompare
      hscratchB
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        false := by
    apply RoundState.historyBit_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hmain, hhistory, hsource]

/-- In the explicit active-round family, the `vEven` branch's selected
history readout agrees with the source-level `RoundState.historyBit`. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hhistory : (coeffAdderHistoryBit n counterWidth historyIndex).get x =
      false)
    (huIndex : (coeffAdderUBit n counterWidth uIndex).get x = true)
    (hvIndex : (coeffAdderVBit n counterWidth vIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkKaliskiActiveBranchRoundStep_get_history_vEven_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex x hcompare
      hscratchB
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        true := by
    apply RoundState.historyBit_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hmain, hhistory, hactive, huIndex, hvIndex, hsource]
  simp

/-- In the explicit active-round family, the `uEven` branch's `u` readout
agrees with the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huIndex : (coeffAdderUBit tail.succ counterWidth uIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.uEven x).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_u_uEven_wordHalf_of_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex x hcompare
      hscratchA hactive huIndex huEven
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the explicit active-round family, the `uEven` branch's `s` readout
agrees with the source-level fixed round under the explicit no-overflow
coefficient-doubling guard. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (huIndex : (coeffAdderUBit n counterWidth uIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (n + 1)) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uEven x).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uEven_wordDouble_of_msb_false
      n counterWidth uIndex vIndex comparisonIndex historyIndex x hcompare
      hscratchA hactive huIndex hmsb
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  have hdoubleVal :
      (wordDouble (n + 1) x.1.1.sCoeff).val = 2 * x.1.1.sCoeff.val :=
    wordDouble_val_of_no_overflow (n + 1) x.1.1.sCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the explicit active-round family, the `uEven` branch preserves the
untouched `v` readout, matching the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_v_uEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (huIndex : (coeffAdderUBit n counterWidth uIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uEven x).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  have hword :=
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v
      n counterWidth uIndex historyIndex x hcompare hscratchA hactive huIndex
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hround]
  simpa [coeffWorkKaliskiActiveBranchRoundStep, RoundState.applyBranch,
    RoundState.fromRegisters] using congrArg (fun word => word.val) hword

/-- In the explicit active-round family, the `uEven` branch preserves the
untouched `r` readout, matching the source-level fixed round. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (huIndex : (coeffAdderUBit n counterWidth uIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uEven x).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  have hword :=
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff
      n counterWidth uIndex historyIndex x hcompare hscratchA hactive huIndex
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hround]
  simpa [coeffWorkKaliskiActiveBranchRoundStep, RoundState.applyBranch,
    RoundState.fromRegisters] using congrArg (fun word => word.val) hword

/-- In the explicit active-round family, the `vEven` branch's `v` readout
agrees with the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.vEven x).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_v_vEven_wordHalf_of_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex x hcompare
      hscratchA hactive hvEven
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the explicit active-round family, the `vEven` branch's `r` readout
agrees with the source-level fixed round under the explicit no-overflow
coefficient-doubling guard. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (n + 1)) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vEven x).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vEven_wordDouble_of_msb_false
      n counterWidth uIndex vIndex comparisonIndex historyIndex x hcompare
      hscratchA hactive hmsb
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  have hdoubleVal :
      (wordDouble (n + 1) x.1.1.rCoeff).val = 2 * x.1.1.rCoeff.val :=
    wordDouble_val_of_no_overflow (n + 1) x.1.1.rCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the explicit active-round family, the `vEven` branch preserves the
untouched `u` readout, matching the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_u_vEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vEven x).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  have hword :=
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u
      n counterWidth uIndex vIndex historyIndex x hcompare hscratchA hactive
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hround]
  simpa [coeffWorkKaliskiActiveBranchRoundStep, RoundState.applyBranch,
    RoundState.fromRegisters] using congrArg (fun word => word.val) hword

/-- In the explicit active-round family, the `vEven` branch preserves the
untouched `s` readout, matching the source-level fixed round. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vEven x).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  have hword :=
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff
      n counterWidth uIndex vIndex historyIndex x hcompare hscratchA hactive
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hround]
  simpa [coeffWorkKaliskiActiveBranchRoundStep, RoundState.applyBranch,
    RoundState.fromRegisters] using congrArg (fun word => word.val) hword

/-- The selected active wrapper's `uEven` history readout agrees with the
source-level `RoundState.historyBit` once the concrete low-`u` selector bit
chooses the fixed `uEven` branch. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex kaliskiSteps paddingSteps x hcompare
      hscratchB hactive hhistory hvNonzero huEven

/-- The selected active wrapper's `vEven` history readout agrees with the
source-level `RoundState.historyBit` once the concrete low readouts choose the
fixed `vEven` branch. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hhistory :
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex kaliskiSteps paddingSteps x hcompare
      hscratchB hactive hhistory huLow hvLow hvNonzero huOdd hvEven

/-- The selected active wrapper's `uEven` `u` readout agrees with the
source-level fixed round once the concrete low-`u` selector bit chooses the
fixed `uEven` branch. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_u_uEven_eq_sourceRound_clean
      tail counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex kaliskiSteps paddingSteps x hcompare
      hscratchA hactive huLow hvNonzero huEven

/-- The selected active wrapper's `uEven` `s` readout agrees with the
source-level fixed round under the explicit no-overflow coefficient-doubling
guard. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex kaliskiSteps paddingSteps x hcompare
      hscratchA hactive huLow hvNonzero huEven hmsb hdouble

/-- The selected active wrapper's `vEven` `v` readout agrees with the
source-level fixed round once the concrete low readouts choose the fixed
`vEven` branch. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_v_vEven_eq_sourceRound_clean
      tail counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex kaliskiSteps paddingSteps x hcompare
      hscratchA hactive hvNonzero huOdd hvEven

/-- The selected active wrapper's `vEven` `r` readout agrees with the
source-level fixed round under the explicit no-overflow coefficient-doubling
guard. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb :
      x.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (tail.succ + 1)) :
    (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex kaliskiSteps paddingSteps x hcompare
      hscratchA hactive hvNonzero huOdd hvEven hmsb hdouble

/-- In the explicit active-round family, the corrected `uGreater` branch's
selected history write agrees with the source-level `RoundState.historyBit`.
-/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : comparisonIndex.val + 1 = n)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit n counterWidth historyIndex).get x = false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uGreater
          ((x, cleanComparisonWork n), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkKaliskiActiveBranchRoundStep_get_history_uGreater_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchA hcompare hscratchB hfinal
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        true := by
    apply RoundState.historyBit_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  rw [hmain, hhistory, hsource, hactive]
  simp [hlt]

/-- In the explicit active-round family, the corrected `vLe` branch's
selected history readout agrees with the source-level `RoundState.historyBit`.
-/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit n counterWidth historyIndex).get x = false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vLe
          ((x, cleanComparisonWork n), work)) =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps) := by
  have hmain :=
    coeffWorkKaliskiActiveBranchRoundStep_get_history_vLe_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchB
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hsource :
      RoundState.historyBit
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        false := by
    apply RoundState.historyBit_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  rw [hmain, hhistory, hsource]

/-- In the explicit active-round family, the corrected `uGreater` branch's
`u` readout agrees with the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.uGreater
        ((x, cleanComparisonWork tail.succ), work)).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have hgreater : decide (x.v.val < x.u.val) = true := by
    simp [hlt]
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_u_uGreater_wordHalf_sub_of_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchA hcompare hactive hfinal hgreater hsourceWork hlsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have hsubVal : (x.u - x.v).val = x.u.val - x.v.val := by
    exact Fin.sub_val_of_le (le_of_lt hlt)
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters, hsubVal]

/-- In the explicit active-round family, the corrected `uGreater` branch's
`r` readout agrees with the source-level fixed round under the explicit
no-overflow coefficient-add guard. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hfinal : comparisonIndex.val + 1 = n)
    (hcarry :
      (liftedCoeffAdderCarryInBit n counterWidth).get
        ((x, cleanComparisonWork n), work) = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (n + 1)) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uGreater
        ((x, cleanComparisonWork n), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hgreater : decide (x.v.val < x.u.val) = true := by
    simp [hlt]
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_uGreater_add_of_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchA hcompare hactive hfinal hgreater hcarry hwork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have haddVal :
      (x.rCoeff + x.sCoeff).val = x.rCoeff.val + x.sCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  rw [hword, hround, haddVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the explicit active-round family, the corrected `uGreater` branch's
`s` readout agrees with the source-level fixed round under the explicit
no-overflow coefficient-doubling guard. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hfinal : comparisonIndex.val + 1 = n)
    (hmsb : x.sCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (n + 1)) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uGreater
        ((x, cleanComparisonWork n), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hgreater : decide (x.v.val < x.u.val) = true := by
    simp [hlt]
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uGreater_wordDouble_of_msb_false
      n counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchA hcompare hactive hfinal hgreater hmsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  have hdoubleVal :
      (wordDouble (n + 1) x.sCoeff).val = 2 * x.sCoeff.val :=
    wordDouble_val_of_no_overflow (n + 1) x.sCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the explicit active-round family, the corrected `uGreater` branch
preserves the untouched `v` readout, matching the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_v_uGreater_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hfinal : comparisonIndex.val + 1 = n) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uGreater
        ((x, cleanComparisonWork n), work)).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have hgreater : decide (x.v.val < x.u.val) = true := by
    simp [hlt]
  have hword :=
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_v
      n counterWidth comparisonIndex historyIndex x work hscratchA hcompare
      hactive hfinal hgreater
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  rw [hround]
  simpa [coeffWorkKaliskiActiveBranchRoundStep, RoundState.applyBranch,
    RoundState.fromRegisters] using congrArg (fun word => word.val) hword

/-- In the explicit active-round family, the corrected `vLe` branch's `v`
readout agrees with the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.vLe
        ((x, cleanComparisonWork tail.succ), work)).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_v_vLe_wordHalf_sub_of_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchA hactive hsourceWork hlsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have hsubVal : (x.v - x.u).val = x.v.val - x.u.val := by
    exact Fin.sub_val_of_le (Nat.le_of_not_gt hnlt)
  rw [hword, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters, hsubVal]

/-- In the explicit active-round family, the corrected `vLe` branch's `s`
readout agrees with the source-level fixed round under the explicit
no-overflow coefficient-add guard. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcarry :
      (liftedCoeffAdderCarryInBit n counterWidth).get
        ((x, cleanComparisonWork n), work) = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (n + 1)) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vLe
        ((x, cleanComparisonWork n), work)).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_vLe_add_of_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchA hactive hcarry hwork
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have haddVal :
      (x.sCoeff + x.rCoeff).val = x.sCoeff.val + x.rCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  rw [hword, hround, haddVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters, Nat.add_comm]

/-- In the explicit active-round family, the corrected `vLe` branch's `r`
readout agrees with the source-level fixed round under the explicit
no-overflow coefficient-doubling guard. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hmsb : x.rCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (n + 1)) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vLe
        ((x, cleanComparisonWork n), work)).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have hword :=
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vLe_wordDouble_of_msb_false
      n counterWidth uIndex vIndex comparisonIndex historyIndex x work
      hscratchA hactive hmsb
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  have hdoubleVal :
      (wordDouble (n + 1) x.rCoeff).val = 2 * x.rCoeff.val :=
    wordDouble_val_of_no_overflow (n + 1) x.rCoeff hdouble
  rw [hword, hround, hdoubleVal]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- In the explicit active-round family, the corrected `vLe` branch preserves
the untouched `u` readout, matching the source-level fixed round. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_u_vLe_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vLe
        ((x, cleanComparisonWork n), work)).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have hword :=
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_u
      n counterWidth comparisonIndex historyIndex x work hscratchA hactive
  have hactiveField : x.active = true :=
    activeBit_get_eq_active n counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters n counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  rw [hround]
  simpa [coeffWorkKaliskiActiveBranchRoundStep, RoundState.applyBranch,
    RoundState.fromRegisters] using congrArg (fun word => word.val) hword

/-- The lifted explicit active-round family preserves the `uEven` source
history bridge while carrying padding-counter work unchanged. -/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hhistory : (coeffAdderHistoryBit n counterWidth historyIndex).get x =
      false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex
          vIndex comparisonIndex historyIndex Branch.uEven
          (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_history_uEven_eq_sourceHistoryBit_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x hcompare hscratchB hactive hhistory hvNonzero huEven

/-- The lifted explicit active-round family preserves the `vEven` source
history bridge while carrying padding-counter work unchanged. -/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hhistory : (coeffAdderHistoryBit n counterWidth historyIndex).get x =
      false)
    (huIndex : (coeffAdderUBit n counterWidth uIndex).get x = true)
    (hvIndex : (coeffAdderVBit n counterWidth vIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex
          vIndex comparisonIndex historyIndex Branch.vEven
          (x, counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_history_vEven_eq_sourceHistoryBit_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x hcompare hscratchB hactive hhistory huIndex hvIndex
      hvNonzero huOdd hvEven

/-- The lifted explicit active-round family's `uEven` `u` readout agrees with
the source-level fixed round. -/
theorem fullRoundWorkKaliskiActiveBranchRoundStep_get_u_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huIndex : (coeffAdderUBit tail.succ counterWidth uIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.uEven
        (x, counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_u_uEven_eq_sourceRound_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex
      kaliskiSteps paddingSteps x hcompare hscratchA hactive huIndex
      hvNonzero huEven

/-- The lifted explicit active-round family's `uEven` `s` readout agrees with
the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (huIndex : (coeffAdderUBit n counterWidth uIndex).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.1.1.sCoeff.val < 2 ^ (n + 1)) :
    (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uEven
        (x, counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uEven_eq_sourceRound_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x hcompare hscratchA hactive huIndex hvNonzero huEven hmsb
      hdouble

/-- The lifted explicit active-round family's `vEven` `v` readout agrees with
the source-level fixed round. -/
theorem fullRoundWorkKaliskiActiveBranchRoundStep_get_v_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.vEven
        (x, counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_v_vEven_eq_sourceRound_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex
      kaliskiSteps paddingSteps x hcompare hscratchA hactive hvNonzero huOdd
      hvEven

/-- The lifted explicit active-round family's `vEven` `r` readout agrees with
the source-level fixed round under the explicit no-overflow guard. -/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.1.1.rCoeff.val < 2 ^ (n + 1)) :
    (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vEven
        (x, counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vEven_eq_sourceRound_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x hcompare hscratchA hactive hvNonzero huOdd hvEven hmsb
      hdouble

/-- The lifted explicit active-round family preserves the corrected
`uGreater` source-history bridge. -/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : comparisonIndex.val + 1 = n)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit n counterWidth historyIndex).get x = false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex
          vIndex comparisonIndex historyIndex Branch.uGreater
          (((x, cleanComparisonWork n), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_history_uGreater_eq_sourceHistoryBit_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x work hscratchA hcompare hscratchB hfinal hactive
      hhistory huOdd hvOdd hlt

/-- The lifted explicit active-round family preserves the corrected `vLe`
source-history bridge. -/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hhistory :
      (RegisterBits.historyBit n counterWidth historyIndex).get x = false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex
          vIndex comparisonIndex historyIndex Branch.vLe
          (((x, cleanComparisonWork n), work), counterWork)).1 =
      RoundState.historyBit
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps) := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_history_vLe_eq_sourceHistoryBit_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x work hscratchB hactive hhistory huOdd hvOdd hnlt

/-- The lifted explicit active-round family's corrected `uGreater` `u` readout
agrees with the source-level fixed round. -/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_u_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.uGreater
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex
      kaliskiSteps paddingSteps x work hscratchA hcompare hactive huOdd hvOdd
      hlt hfinal hsourceWork hlsb

/-- The lifted explicit active-round family's corrected `uGreater` `r` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hfinal : comparisonIndex.val + 1 = n)
    (hcarry :
      (liftedCoeffAdderCarryInBit n counterWidth).get
        ((x, cleanComparisonWork n), work) = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (n + 1)) :
    (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uGreater
        (((x, cleanComparisonWork n), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_uGreater_eq_sourceRound_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x work hscratchA hcompare hactive huOdd hvOdd hlt hfinal
      hcarry hwork hadd

/-- The lifted explicit active-round family's corrected `uGreater` `s` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hfinal : comparisonIndex.val + 1 = n)
    (hmsb : x.sCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (n + 1)) :
    (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uGreater
        (((x, cleanComparisonWork n), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uGreater_eq_sourceRound_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x work hscratchA hcompare hactive huOdd hvOdd hlt hfinal
      hmsb hdouble

/-- The lifted explicit active-round family's corrected `vLe` `v` readout
agrees with the source-level fixed round. -/
theorem fullRoundWorkKaliskiActiveBranchRoundStep_get_v_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.vLe
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_v_vLe_eq_sourceRound_clean
      tail counterWidth uIndex vIndex comparisonIndex historyIndex
      kaliskiSteps paddingSteps x work hscratchA hactive huOdd hvOdd hnlt
      hsourceWork hlsb

/-- The lifted explicit active-round family's corrected `vLe` `s` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcarry :
      (liftedCoeffAdderCarryInBit n counterWidth).get
        ((x, cleanComparisonWork n), work) = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (n + 1)) :
    (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vLe
        (((x, cleanComparisonWork n), work), counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_vLe_eq_sourceRound_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x work hscratchA hactive huOdd hvOdd hnlt hcarry hwork
      hadd

/-- The lifted explicit active-round family's corrected `vLe` `r` readout
agrees with the source-level fixed round under the explicit no-overflow guard.
-/
theorem
    fullRoundWorkKaliskiActiveBranchRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hmsb : x.rCoeff.val.testBit (Fin.last n).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (n + 1)) :
    (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vLe
        (((x, cleanComparisonWork n), work), counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkKaliskiActiveBranchRoundStep] using
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vLe_eq_sourceRound_clean
      n counterWidth uIndex vIndex comparisonIndex historyIndex kaliskiSteps
      paddingSteps x work hscratchA hactive huOdd hvOdd hnlt hmsb hdouble

end
end MK
end MAU.Inversion
end QuantumAlg

end
