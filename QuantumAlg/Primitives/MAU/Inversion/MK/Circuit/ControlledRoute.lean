/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Fold
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.RouteWorkspace
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.ActiveSlices
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Semantics
import all QuantumAlg.Primitives.MAU.Inversion.MK.Termination
import all QuantumAlg.Primitives.MAU.Inversion.MK.Round
import all QuantumAlg.Primitives.MAU.Inversion.MK.Selector
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Termination

/-!
# Controlled fixed-round route semantics
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open MK
open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD
/-! ## Whole active-only route controlled by the original-active path -/

/-- Clean-work control decomposition of the complete active-only route.  The
payload contains both the terminating detector/counter prefix and the
nonterminating dispatch, so every payload gate is controlled by the latched
original-active path. -/
def controlledActiveOnlyGates (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (workingPathBit tail counterWidth)
    (workingControlBit tail counterWidth)
    (liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex)
    (liftedActiveOnlyGates_bitDisjoint_path tail counterWidth comparisonIndex
      historyIndex workIndex)
    (liftedActiveOnlyGates_bitDisjoint_controlWork tail counterWidth
      comparisonIndex historyIndex workIndex)
    (workingPathBit_workingControlBit_wire_ne tail counterWidth)

/-- Actual clean-work controlled program for the complete active-only route,
including both the terminating detector and the nonterminating dispatch. -/
def controlledActiveOnlyProgram (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (controlledActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex)

/-- Exact structured action of the whole controlled active-only route. -/
def controlledActiveOnlyStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (controlledActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex)

lemma controlledActiveOnly_realizes
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (encoding tail.succ counterWidth)
      (controlledActiveOnlyProgram tail counterWidth comparisonIndex
        historyIndex workIndex) environment
      (controlledActiveOnlyStep tail counterWidth comparisonIndex
        historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (controlledActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex)

/-- Structured action of the raw controlled program on the clean-control
slice.  This is a semantic description of the fixed program, not a
data-dependent gate selector. -/
def controlledActiveOnlyStructuredStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  fun x =>
    if (workingPathBit tail counterWidth).get x then
      liftedActiveOnlyStep tail counterWidth comparisonIndex historyIndex
        workIndex x
    else x

/-- With clean control work, the exact controlled step reduces to the lifted
active-only route when the path is true and to identity when it is false. -/
lemma controlledActiveOnlyStep_eq_semantic_of_clean
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hwork : (workingControlBit tail counterWidth).get x = false) :
    controlledActiveOnlyStep tail counterWidth comparisonIndex historyIndex
        workIndex x =
      controlledActiveOnlyStructuredStep tail counterWidth comparisonIndex
        historyIndex workIndex x := by
  cases hpath : (workingPathBit tail counterWidth).get x with
  | false =>
      have hcontrolled :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
          (workingPathBit tail counterWidth)
          (workingControlBit tail counterWidth)
          (liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
            workIndex)
          (liftedActiveOnlyGates_bitDisjoint_path tail counterWidth
            comparisonIndex historyIndex workIndex)
          (liftedActiveOnlyGates_bitDisjoint_controlWork tail counterWidth
            comparisonIndex historyIndex workIndex)
          (workingPathBit_workingControlBit_wire_ne tail counterWidth)
          x hpath
      simpa [controlledActiveOnlyStep, controlledActiveOnlyGates,
        controlledActiveOnlyStructuredStep,
        EncodedBit.GateSpec.controlledListWithWorkStep, hpath] using
        hcontrolled
  | true =>
      have hcontrolled :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
          (workingPathBit tail counterWidth)
          (workingControlBit tail counterWidth)
          (liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
            workIndex)
          (liftedActiveOnlyGates_bitDisjoint_path tail counterWidth
            comparisonIndex historyIndex workIndex)
          (liftedActiveOnlyGates_bitDisjoint_controlWork tail counterWidth
            comparisonIndex historyIndex workIndex)
          (workingPathBit_workingControlBit_wire_ne tail counterWidth)
          x hpath hwork
      calc
        controlledActiveOnlyStep tail counterWidth comparisonIndex historyIndex
            workIndex x =
            EncodedBit.GateSpec.stepList
              (liftedActiveOnlyGates tail counterWidth comparisonIndex
                historyIndex workIndex) x := by
          simpa [controlledActiveOnlyStep, controlledActiveOnlyGates,
            EncodedBit.GateSpec.controlledListWithWorkStep] using hcontrolled
        _ = liftedActiveOnlyStep tail counterWidth comparisonIndex historyIndex
              workIndex x :=
          liftedActiveOnlyGates_stepList_eq tail counterWidth comparisonIndex
            historyIndex workIndex x
        _ = controlledActiveOnlyStructuredStep tail counterWidth
              comparisonIndex historyIndex workIndex x := by
          simp [controlledActiveOnlyStructuredStep, hpath]

/-- Normalize the latch/padding/controlled-route prefix on a clean active
round boundary.  The active-only concrete route receives exactly the standard
clean full-round workspace, while the latched path remains true. -/
lemma controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hclean : PhysicalWorkspaceClean tail counterWidth x)
    (hactive : (dataRegisters tail counterWidth x).active = true) :
    controlledActiveOnlyStructuredStep tail counterWidth comparisonIndex
        roundIndex workIndex
        (inactivePaddingStep tail counterWidth
          (originalActiveLatchStep tail counterWidth x)) =
      (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex
          ((((dataRegisters tail counterWidth x),
              cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth), true), false), x.2) := by
  unfold inactivePaddingStep originalActiveLatchStep
  rw [hclean.workspace]
  rw [fullRoundPathControlWorkOriginalActiveLatchStep_cleanActiveEndpoint
    tail counterWidth (dataRegisters tail counterWidth x) hactive]
  change controlledActiveOnlyStructuredStep tail counterWidth comparisonIndex
      roundIndex workIndex
      (fullRoundPathControlWorkActiveFalseInactivePaddingStep tail counterWidth
        (((((dataRegisters tail counterWidth x,
              cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), true), false), x.2) = _
  rw [fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanActiveEndpoint
    tail counterWidth (dataRegisters tail counterWidth x) true false hactive]
  change (if true then _ else _) = _
  rfl

/-- Normalize the same prefix on a clean inactive round boundary.  Padding
increments the source counter, all reusable work stays clean, and the false
path makes the controlled active-only route an exact no-op. -/
lemma controlledActiveOnlyStructuredStep_after_latch_padding_inactive_eq
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hclean : PhysicalWorkspaceClean tail counterWidth x)
    (hactive : (dataRegisters tail counterWidth x).active = false) :
    controlledActiveOnlyStructuredStep tail counterWidth comparisonIndex
        roundIndex workIndex
        (inactivePaddingStep tail counterWidth
          (originalActiveLatchStep tail counterWidth x)) =
      (((((({ dataRegisters tail counterWidth x with
              counter := wordIncrement counterWidth
                (dataRegisters tail counterWidth x).counter },
            cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), false), false), x.2) := by
  unfold inactivePaddingStep originalActiveLatchStep
  rw [hclean.workspace]
  have hactiveBit :
      (fullRoundPathControlWorkActiveBit tail counterWidth).get
          (withCleanFullRoundPathControlWork tail.succ counterWidth
            (dataRegisters tail counterWidth x)) = false := by
    rw [fullRoundPathControlWorkActiveBit_get_withClean, hactive]
  rw [fullRoundPathControlWorkOriginalActiveLatchStep_eq_self_of_active_false
    tail counterWidth _ hactiveBit]
  change controlledActiveOnlyStructuredStep tail counterWidth comparisonIndex
      roundIndex workIndex
      (fullRoundPathControlWorkActiveFalseInactivePaddingStep tail counterWidth
        (withCleanFullRoundPathControlWork tail.succ counterWidth
          (dataRegisters tail counterWidth x)), x.2) = _
  rw [fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanInactiveEndpoint
    tail counterWidth (dataRegisters tail counterWidth x) hactive]
  change (if false then _ else _) = _
  rfl

/-- The exact latch/padding/controlled-route prefix, stopping immediately
before physical branch-residue cleanup. -/
def routedStepBeforeCleanup (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  fun x =>
    controlledActiveOnlyStructuredStep tail counterWidth comparisonIndex
      roundIndex workIndex
      (inactivePaddingStep tail counterWidth
        (originalActiveLatchStep tail counterWidth x))

/-- The latch/padding/controlled-route prefix does not consume any persistent
route-history slot. -/
lemma routedStepBeforeCleanup_get_route
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex observed : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth observed).get
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x) =
      (routeHistoryBit tail counterWidth observed).get x := by
  unfold routedStepBeforeCleanup controlledActiveOnlyStructuredStep
    inactivePaddingStep originalActiveLatchStep liftedActiveOnlyStep
  split <;> rfl

/-- On a clean round boundary the working path records exactly the original
active flag, independently of the branch taken by the controlled route. -/
lemma routedStepBeforeCleanup_get_path_eq_originalActive
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hclean : PhysicalWorkspaceClean tail counterWidth x) :
    (workingPathBit tail counterWidth).get
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x) =
      (dataRegisters tail counterWidth x).active := by
  cases hactive : (dataRegisters tail counterWidth x).active
  · rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_inactive_eq
        tail counterWidth comparisonIndex roundIndex workIndex x hclean
        hactive]
    rfl
  · rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x hclean
        hactive]
    rfl

/-- The selected even-branch dispatcher restores every comparison-work bit,
including the one temporarily borrowed for branch-code staging. -/
private lemma selectedDispatch_comparisonWork_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (d : Registers tail.succ counterWidth)
    (hscratchA : d.scratchA = false)
    (hscratchB : d.scratchB = false) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex roundIndex
        ((d, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ)).1.2 =
      cleanComparisonWork tail.succ := by
  let input : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let output :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex input
  have hscratchAInput :
      (coeffAdderScratchABit tail.succ counterWidth).get input = false := by
    change d.scratchA = false
    exact hscratchA
  have hscratchBInput :
      (coeffAdderScratchBBit tail.succ counterWidth).get input = false := by
    change d.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get input = false := by
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ comparisonIndex
  change output.1.2 = cleanComparisonWork tail.succ
  apply (comparisonWorkEquiv tail.succ).injective
  change output.1.2.carry = (cleanComparisonWork tail.succ).carry
  apply word_eq_of_testBit_eq
  intro observed
  have hbit :
      (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get
          output = false := by
    by_cases hselected : comparisonIndex = observed
    · subst observed
      exact
        coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_comparisonCarry_clean
          tail counterWidth comparisonIndex roundIndex input
          hscratchAInput hscratchBInput htemp
    · rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_comparisonCarry_of_ne
        tail counterWidth comparisonIndex roundIndex observed hselected input]
      exact comparisonCarryValueBit_clean tail.succ observed
  simpa [cleanComparisonWork, coeffAdderComparisonCarryBit,
    liftedComparisonCarryBit, liftComparisonStateBitToCoeffAdderWork,
    liftComparisonWorkBit, comparisonCarryValueBit, comparisonCarryBit,
    comparisonWorkEquiv, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    WireAddress.bitIndex_littleEndianWire,
    BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit] using hbit

/-- The selected even-branch dispatcher also restores the dedicated
coefficient-adder carry-in and complete carry-work word. -/
private lemma selectedDispatch_coefficientWork_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (d : Registers tail.succ counterWidth) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex roundIndex
        ((d, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ)).2 =
      cleanCoeffAdderWork tail.succ := by
  let input : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let output :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex input
  change output.2 = cleanCoeffAdderWork tail.succ
  apply Prod.ext
  · have hcarry :=
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryIn
        tail counterWidth comparisonIndex roundIndex input
    change output.2.1 = input.2.1 at hcarry
    simpa [input, cleanCoeffAdderWork] using hcarry
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    change
      ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit
        workBit).get output = false
    calc
      ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit
          workBit).get output =
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit
          workBit).get input := by
            exact
              coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryWorkBit
                tail counterWidth comparisonIndex roundIndex workBit input
      _ = false :=
        liftedCoeffAdderCarryWorkBit_get_clean tail.succ counterWidth
          workBit (d, cleanComparisonWork tail.succ)

/-- The carried odd dispatcher restores the complete comparison workspace. -/
private lemma oddCarriedDispatch_comparisonWork_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (d : Registers tail.succ counterWidth)
    (hscratchA : d.scratchA = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth comparisonIndex roundIndex
        ((d, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ)).1.2 =
      cleanComparisonWork tail.succ := by
  let input : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth comparisonIndex input
  let output :=
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
      tail counterWidth comparisonIndex roundIndex input
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get input = false := by
    dsimp [input]
    exact liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (d, cleanComparisonWork tail.succ)
  have hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
            input = false := by
    intro k
    dsimp [input]
    exact coeffAdderComparisonCarryPrefixWord_get_clean
      tail.succ counterWidth k d
  change output.1.2 = cleanComparisonWork tail.succ
  apply (comparisonWorkEquiv tail.succ).injective
  change output.1.2.carry = (cleanComparisonWork tail.succ).carry
  apply word_eq_of_testBit_eq
  intro observed
  have hselectedBit :
      (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get
          selected = false := by
    by_cases hselected : comparisonIndex = observed
    · subst observed
      exact
        coeffWorkCompareSelectorSelectedOddDataPathStep_get_comparisonCarry_final_clean
          tail.succ counterWidth comparisonIndex d
          (cleanCoeffAdderWork tail.succ) hscratchA hfinal hcontrolWork
    · have hvalNe : comparisonIndex.val ≠ observed.val := by
        intro hval
        apply hselected
        exact Fin.ext hval
      have hobservedLt : observed.val < tail.succ - 1 := by
        have hobserved := observed.isLt
        omega
      let workBit : Fin (tail.succ - 1) :=
        ⟨observed.val, hobservedLt⟩
      have hprefix :=
        coeffWorkCompareSelectorSelectedOddDataPathStep_get_comparisonCarryPrefix_clean
          tail.succ counterWidth comparisonIndex workBit d
          (cleanCoeffAdderWork tail.succ) hscratchA hcontrolWork hsourceWork
      have hidx :
          coeffAdderComparisonCarryPrefixIndex tail.succ workBit = observed := by
        apply Fin.ext
        rfl
      change
        (coeffAdderComparisonCarryBit tail.succ counterWidth
          (coeffAdderComparisonCarryPrefixIndex tail.succ workBit)).get
            selected = false at hprefix
      simpa only [hidx] using hprefix
  have hpreserved :
      (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get
          output =
        (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get
          selected := by
    dsimp only [output]
    rw [coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep,
      coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_comparisonCarry]
    rfl
  have hbit :
      (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get
          output = false := hpreserved.trans hselectedBit
  simpa [cleanComparisonWork, coeffAdderComparisonCarryBit,
    liftedComparisonCarryBit, liftComparisonStateBitToCoeffAdderWork,
    liftComparisonWorkBit, comparisonCarryValueBit, comparisonCarryBit,
    comparisonWorkEquiv, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    WireAddress.bitIndex_littleEndianWire,
    BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit] using hbit

/-- The carried odd dispatcher restores the complete coefficient-adder work. -/
private lemma oddCarriedDispatch_coefficientWork_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (d : Registers tail.succ counterWidth)
    (hscratchA : d.scratchA = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth comparisonIndex roundIndex
        ((d, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ)).2 =
      cleanCoeffAdderWork tail.succ := by
  let input : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth comparisonIndex input
  let output :=
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
      tail counterWidth comparisonIndex roundIndex input
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get input = false := by
    dsimp [input]
    exact liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (d, cleanComparisonWork tail.succ)
  have hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
            input = false := by
    intro k
    dsimp [input]
    exact liftedCoeffAdderCarryWorkBit_get_clean tail.succ counterWidth k
      (d, cleanComparisonWork tail.succ)
  have hselectedCarry :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get selected =
        false := by
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_coeffCarryIn_clean
        tail.succ counterWidth comparisonIndex d
        (cleanCoeffAdderWork tail.succ) hscratchA hcontrolWork
  have hpreservedCarry :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get output =
        (liftedCoeffAdderCarryInBit tail.succ counterWidth).get selected := by
    dsimp only [output]
    rw [coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep,
      coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryIn,
      coeffWorkActiveBranchCodeToScratchStep_get_carryIn]
    rfl
  have hselectedWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
            selected = false := by
    intro k
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_carryWork_clean
        tail.succ counterWidth comparisonIndex k d
        (cleanCoeffAdderWork tail.succ) hscratchA hcontrolWork hcoeffWork
  have hpreservedWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
            output =
          ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
            selected := by
    intro k
    dsimp only [output]
    rw [coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep,
      coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryWorkBit,
      coeffWorkActiveBranchCodeToScratchStep_get_carryWorkBit]
    rfl
  change output.2 = cleanCoeffAdderWork tail.succ
  apply Prod.ext
  · have hcarry := hpreservedCarry.trans hselectedCarry
    change output.2.1 = false at hcarry
    simpa [cleanCoeffAdderWork] using hcarry
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    change
      ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
          output = false
    exact (hpreservedWork workBit).trans (hselectedWork workBit)

/-- Inactive padding leaves no branch residue: the path-controlled active
route is skipped and the counter incrementer restores its physical work. -/
lemma routedStepBeforeCleanup_inactive_residueCertificate
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = false) :
    BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  have hhistoryValue :
      (dataRegisters tail counterWidth x).history.val.testBit
          (WireAddress.bitIndex roundIndex).val = false := by
    simpa [RegisterBits.historyBit_get] using hinput.historyFresh
  rw [routedStepBeforeCleanup,
    controlledActiveOnlyStructuredStep_after_latch_padding_inactive_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive]
  apply branchResidueCertificate_of_all_false
  · simpa only [activeBit_get_dataRegisters, dataRegisters,
      RegisterBits.activeBit_get] using hactive
  · simp [counterCarryInBit_get_counterWork, cleanCounterIncrementWork,
      counterIncrementCarryInBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.boolBit]
  · simpa only [compareBit_get_dataRegisters, dataRegisters,
      RegisterBits.compareBit_get] using hinput.compare
  · simpa only [scratchABit_get_dataRegisters, dataRegisters,
      RegisterBits.scratchABit_get] using hinput.scratchA
  · simpa only [scratchBBit_get_dataRegisters, dataRegisters,
      RegisterBits.scratchBBit_get] using hinput.scratchB
  · rw [historyBit_get_dataRegisters, RegisterBits.historyBit_get]
    simpa [dataRegisters] using hhistoryValue

/-- An active terminating round clears active and restores all full-round
work, so it likewise reaches the all-zero branch-residue certificate. -/
lemma routedStepBeforeCleanup_active_terminated_residueCertificate
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvZero : (dataRegisters tail counterWidth x).v.val = 0) :
    BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  have hhistoryValue :
      (dataRegisters tail counterWidth x).history.val.testBit
          (WireAddress.bitIndex roundIndex).val = false := by
    simpa [RegisterBits.historyBit_get] using hinput.historyFresh
  rw [routedStepBeforeCleanup,
    controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive]
  rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
    tail counterWidth comparisonIndex roundIndex workIndex
    (dataRegisters tail counterWidth x) hinput.compare hactive hvZero
    hinput.scratchA hinput.scratchB]
  apply branchResidueCertificate_of_all_false
  · rfl
  · simp [counterCarryInBit_get_counterWork, cleanCounterIncrementWork,
      counterIncrementCarryInBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.boolBit]
  · simpa only [compareBit_get_dataRegisters, dataRegisters,
      RegisterBits.compareBit_get] using hinput.compare
  · simpa only [scratchABit_get_dataRegisters, dataRegisters,
      RegisterBits.scratchABit_get] using hinput.scratchA
  · simpa only [scratchBBit_get_dataRegisters, dataRegisters,
      RegisterBits.scratchBBit_get] using hinput.scratchB
  · rw [historyBit_get_dataRegisters, RegisterBits.historyBit_get]
    simpa [dataRegisters] using hhistoryValue

/-- The active nonterminating `uEven` route reaches the exact six-bit residue
pattern required by the physical cleanup suffix. -/
lemma routedStepBeforeCleanup_active_uEven_residueCertificate
    (tail counterWidth modulus kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huEven :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = false)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout :
      RoundState.BezoutInvariant modulus
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x) kaliskiSteps paddingSteps)) :
    BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  let selected :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routed =
        (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex fullInput,
          true), false), x.2) := by
    dsimp [routed]
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = false := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hconcrete :
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex fullInput =
        (selected, cleanCounterIncrementWork counterWidth) := by
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hvNonzero huLow]
    simpa [selected, coeffInput] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow)
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get coeffInput = false := by
    change d.scratchA = false
    exact hinput.scratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get coeffInput = false := by
    change d.scratchB = false
    exact hinput.scratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get coeffInput = false := by
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ comparisonIndex
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get coeffInput = true := by
    change d.active = true
    exact hactive
  have hhistoryCoeff :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
          coeffInput = false := by
    change
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get d = false
    exact hinput.historyFresh
  have hbranch :
      Branch.fromCoeffWorkSignals tail.succ counterWidth coeffInput =
        Branch.uEven := by
    simp [Branch.fromCoeffWorkSignals, Branch.fromCircuitSignals,
      coeffInput, d, huEven]
  have hactiveOut : (activeBit tail counterWidth).get routed = true := by
    rw [hroute, hconcrete]
    change (coeffAdderActiveBit tail.succ counterWidth).get selected = true
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active]
    exact hactiveCoeff
  have hcounterOut :
      (counterCarryInBit tail counterWidth).get routed = false := by
    rw [hroute, hconcrete]
    simp [counterCarryInBit_get_counterWork, cleanCounterIncrementWork,
      counterIncrementCarryInBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.boolBit]
  have hcompareOut : (compareBit tail counterWidth).get routed = false := by
    rw [hroute, hconcrete]
    change (coeffAdderCompareBit tail.succ counterWidth).get selected = false
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare]
    change d.compare = false
    exact hinput.compare
  have hscratchAOut : (scratchABit tail counterWidth).get routed = true := by
    rw [hroute, hconcrete]
    change (coeffAdderScratchABit tail.succ counterWidth).get selected = true
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
      tail counterWidth comparisonIndex roundIndex coeffInput hscratchACoeff
      hscratchBCoeff htemp]
    rw [hactiveCoeff, hbranch]
    rfl
  have hscratchBOut : (scratchBBit tail counterWidth).get routed = false := by
    rw [hroute, hconcrete]
    change (coeffAdderScratchBBit tail.succ counterWidth).get selected = false
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
      tail counterWidth comparisonIndex roundIndex coeffInput hscratchACoeff
      hscratchBCoeff htemp]
    rw [hactiveCoeff, hbranch]
    rfl
  have hhistoryOut :
      (historyBit tail counterWidth roundIndex).get routed = false := by
    rw [hroute, hconcrete]
    change
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get selected =
        false
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      tail counterWidth comparisonIndex roundIndex coeffInput hscratchACoeff
      hscratchBCoeff htemp]
    rw [hhistoryCoeff, hactiveCoeff, hbranch]
    rfl
  let st :=
    RoundState.fromRegisters tail.succ counterWidth d kaliskiSteps paddingSteps
  have hstActive : st.active = true := by
    simpa [st, RoundState.fromRegisters, d] using hactive
  have hstV : st.v ≠ 0 := by
    simpa [st, RoundState.fromRegisters, d] using hvNonzero
  have hselect : RoundState.selectBranch st = Branch.uEven := by
    apply RoundState.selectBranch_uEven_of_even
    dsimp [st, RoundState.fromRegisters, d]
    exact Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false d.u.val huEven
  have hroundParity : (RoundState.round st).rCoeff.testBit 0 = true := by
    calc
      (RoundState.round st).rCoeff.testBit 0 =
          (RoundState.applyBranch
            (RoundState.selectBranch st) st).rCoeff.testBit 0 := by
        rw [RoundState.round_active_nonzero_eq_applyBranch_selectBranch
          st hstActive hstV]
      _ = (RoundState.selectBranch st).auxBit :=
        sourceApplyBranch_rCoeff_testBit_zero_eq_auxBit modulus st
          hmodulusOdd hbezout
      _ = true := by
        rw [hselect]
        rfl
  have hrExact :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex roundIndex workIndex kaliskiSteps
      paddingSteps d hinput.scratchA hinput.scratchB hinput.compare
      (by simpa [RegisterBits.activeBit_get] using hactive) hvNonzero huEven
  have hrLowOut : (rCoeffLowBit tail counterWidth).get routed = true := by
    have hfullInput :
        fullInput =
          (((d, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) := by
      rfl
    have hst :
        st = RoundState.fromRegisters tail.succ counterWidth d
          kaliskiSteps paddingSteps := by
      rfl
    calc
      (rCoeffLowBit tail counterWidth).get routed =
          (rCoeffLowBit tail counterWidth).get
            (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
                tail counterWidth comparisonIndex roundIndex workIndex
                fullInput, true), false), x.2) :=
        congrArg (fun y => (rCoeffLowBit tail counterWidth).get y) hroute
      _ =
          (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex
            fullInput).1.1.1.rCoeff.val.testBit 0 :=
        rCoeffLowBit_get_fullRoundWork tail counterWidth _ true false x.2
      _ =
          (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex
            (((d, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ),
              cleanCounterIncrementWork counterWidth)).1.1.1.rCoeff.val.testBit
            0 :=
        congrArg
          (fun input =>
            (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
              tail counterWidth comparisonIndex roundIndex workIndex
              input).1.1.1.rCoeff.val.testBit 0)
          hfullInput
      _ =
          (RoundState.round
            (RoundState.fromRegisters tail.succ counterWidth d
              kaliskiSteps paddingSteps)).rCoeff.testBit 0 :=
        congrArg (fun z : Nat => z.testBit 0) hrExact
      _ = (RoundState.round st).rCoeff.testBit 0 := by
        rw [hst]
      _ = true := hroundParity
  exact branchResidueCertificate_uEven tail counterWidth roundIndex routed
    hactiveOut hcounterOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- The active nonterminating `vEven` route reaches the complementary even
residue pattern.  Its low `r` bit is read from the physical cyclic shift and
therefore depends only on the explicit source-MSB arithmetic certificate. -/
lemma routedStepBeforeCleanup_active_vEven_residueCertificate
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvEven :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  let selected :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routed =
        (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex fullInput,
          true), false), x.2) := by
    dsimp [routed]
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = false := by
    dsimp [coeffInput, d]
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hconcrete :
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex fullInput =
        (selected, cleanCounterIncrementWork counterWidth) := by
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
        tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
        hvNonzero huLow hvLow]
    simpa [selected, coeffInput] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow hvLow)
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get coeffInput = false := by
    change d.scratchA = false
    exact hinput.scratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get coeffInput = false := by
    change d.scratchB = false
    exact hinput.scratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get coeffInput = false := by
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ comparisonIndex
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get coeffInput = true := by
    change d.active = true
    exact hactive
  have hhistoryCoeff :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
          coeffInput = false := by
    change
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get d = false
    exact hinput.historyFresh
  have hbranch :
      Branch.fromCoeffWorkSignals tail.succ counterWidth coeffInput =
        Branch.vEven := by
    simp [Branch.fromCoeffWorkSignals, Branch.fromCircuitSignals,
      coeffInput, d, huOdd, hvEven]
  have hactiveOut : (activeBit tail counterWidth).get routed = true := by
    rw [hroute, hconcrete]
    change (coeffAdderActiveBit tail.succ counterWidth).get selected = true
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active]
    exact hactiveCoeff
  have hcounterOut :
      (counterCarryInBit tail counterWidth).get routed = false := by
    rw [hroute, hconcrete]
    simp [counterCarryInBit_get_counterWork, cleanCounterIncrementWork,
      counterIncrementCarryInBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.boolBit]
  have hcompareOut : (compareBit tail counterWidth).get routed = false := by
    rw [hroute, hconcrete]
    change (coeffAdderCompareBit tail.succ counterWidth).get selected = false
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare]
    change d.compare = false
    exact hinput.compare
  have hscratchAOut : (scratchABit tail counterWidth).get routed = false := by
    rw [hroute, hconcrete]
    change (coeffAdderScratchABit tail.succ counterWidth).get selected = false
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
      tail counterWidth comparisonIndex roundIndex coeffInput hscratchACoeff
      hscratchBCoeff htemp]
    rw [hactiveCoeff, hbranch]
    rfl
  have hscratchBOut : (scratchBBit tail counterWidth).get routed = true := by
    rw [hroute, hconcrete]
    change (coeffAdderScratchBBit tail.succ counterWidth).get selected = true
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
      tail counterWidth comparisonIndex roundIndex coeffInput hscratchACoeff
      hscratchBCoeff htemp]
    rw [hactiveCoeff, hbranch]
    rfl
  have hhistoryOut :
      (historyBit tail counterWidth roundIndex).get routed = true := by
    rw [hroute, hconcrete]
    change
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get selected =
        true
    rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      tail counterWidth comparisonIndex roundIndex coeffInput hscratchACoeff
      hscratchBCoeff htemp]
    rw [hhistoryCoeff, hactiveCoeff, hbranch]
    rfl
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep
      tail counterWidth comparisonIndex coeffInput
  let written :=
    coeffWorkActiveScratchBToHistoryStep
      tail.succ counterWidth roundIndex staged
  have hselectedVShift :
      selected =
        coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth
          written := by
    dsimp [selected, written, staged]
    exact
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
        tail counterWidth comparisonIndex roundIndex coeffInput
        hscratchACoeff hscratchBCoeff htemp hactiveCoeff (by rw [hbranch]; rfl)
  have hrSelected : selected.1.1.rCoeff.val.testBit 0 = false := by
    calc
      selected.1.1.rCoeff.val.testBit 0 =
          (coeffWorkVDiv2ThenRMul2Step
            tail.succ counterWidth written).1.1.rCoeff.val.testBit 0 :=
        congrArg (fun output => output.1.1.rCoeff.val.testBit 0)
          hselectedVShift
      _ = written.1.1.rCoeff.val.testBit (Fin.last tail.succ).val :=
        coeffWorkVDiv2ThenRMul2Step_get_rCoeff_testBit_zero
          tail.succ counterWidth written
      _ = staged.1.1.rCoeff.val.testBit (Fin.last tail.succ).val :=
        congrArg (fun word => word.val.testBit (Fin.last tail.succ).val)
          (coeffWorkActiveScratchBToHistoryStep_get_rCoeff
            tail.succ counterWidth roundIndex staged)
      _ = coeffInput.1.1.rCoeff.val.testBit (Fin.last tail.succ).val :=
        congrArg (fun word => word.val.testBit (Fin.last tail.succ).val)
          (coeffWorkSelectedBranchCodeToScratchStep_get_rCoeff
            tail counterWidth comparisonIndex coeffInput)
      _ = false := arith.vEven_msb hactive hvNonzero huOdd hvEven
  have hrLowOut : (rCoeffLowBit tail counterWidth).get routed = false := by
    calc
      (rCoeffLowBit tail counterWidth).get routed =
          (rCoeffLowBit tail counterWidth).get
            (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
                tail counterWidth comparisonIndex roundIndex workIndex
                fullInput, true), false), x.2) :=
        congrArg (fun y => (rCoeffLowBit tail counterWidth).get y) hroute
      _ =
          (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex
            fullInput).1.1.1.rCoeff.val.testBit 0 :=
        rCoeffLowBit_get_fullRoundWork tail counterWidth _ true false x.2
      _ = selected.1.1.rCoeff.val.testBit 0 :=
        congrArg (fun output => output.1.1.1.rCoeff.val.testBit 0) hconcrete
      _ = false := hrSelected
  exact branchResidueCertificate_vEven tail counterWidth roundIndex routed
    hactiveOut hcounterOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- The active nonterminating odd `uGreater` route leaves the carried
comparison/branch-code residue expected by the physical cleanup suffix. -/
lemma routedStepBeforeCleanup_active_uGreater_residueCertificate
    (tail counterWidth modulus kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvOdd :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = true)
    (hlt :
      (dataRegisters tail counterWidth x).v.val <
        (dataRegisters tail counterWidth x).u.val)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout :
      RoundState.BezoutInvariant modulus
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x) kaliskiSteps paddingSteps))
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  let concrete :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex fullInput
  let nonzero :=
    fullRoundWorkKaliskiActiveNonzeroRoundStep
      tail counterWidth comparisonIndex roundIndex fullInput
  let oddSelected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth comparisonIndex coeffInput
  let oddCarried :=
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routed = (((concrete, true), false), x.2) := by
    dsimp [routed, concrete]
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcounterClean :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get fullInput =
        false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryInBit_get_clean tail counterWidth d
  have hcounterWorkClean :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
          fullInput = false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryWorkBit_get_clean
      tail counterWidth workIndex d
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get coeffInput =
        false := by
    dsimp [coeffInput]
    exact liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (d, cleanComparisonWork tail.succ)
  have hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          coeffInput = false := by
    intro k
    dsimp [coeffInput]
    exact liftedCoeffAdderCarryWorkBit_get_clean
      tail.succ counterWidth k (d, cleanComparisonWork tail.succ)
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get coeffInput = true := by
    change d.active = true
    exact hactive
  have hconcreteFlip :
      concrete =
        (fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero := by
    dsimp [concrete]
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hvNonzero]
    simpa only [nonzero, fullInput, coeffInput] using
      (fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_lt
        tail counterWidth comparisonIndex roundIndex workIndex d
        (cleanCoeffAdderWork tail.succ)
        (cleanCounterIncrementWork counterWidth) hcounterClean
        hcounterWorkClean hinput.scratchA hinput.compare hfinal huOdd hvOdd
        hlt hcontrolWork hactiveCoeff)
  have hnonzeroOdd :
      nonzero = (oddCarried, cleanCounterIncrementWork counterWidth) := by
    simpa only [nonzero, fullInput, coeffInput, oddCarried] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow hvLow)
  have hoddBranch :
      oddCarried =
        coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail.succ counterWidth roundIndex Branch.uGreater oddSelected := by
    simpa only [oddCarried, oddSelected, coeffInput] using
      (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uGreaterDispatch_clean_lt
        tail counterWidth comparisonIndex roundIndex d
        (cleanCoeffAdderWork tail.succ) hinput.scratchA hinput.compare hfinal
        huOdd hvOdd hlt)
  have hconcreteCoeff : concrete.1 = oddCarried := by
    calc
      concrete.1 =
          ((fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero).1 :=
        congrArg Prod.fst hconcreteFlip
      _ = nonzero.1 :=
        fullRoundWorkCounterCarryInBit_flip_coeffState
          tail counterWidth nonzero
      _ = oddCarried := congrArg Prod.fst hnonzeroOdd
  have hnonzeroCounter :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get nonzero =
        false := by
    rw [hnonzeroOdd]
    change
      (counterIncrementCarryInBit counterWidth).get
        (cleanCounterIncrementWork counterWidth) = false
    rfl
  have hconcreteCounter :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get concrete =
        true := by
    rw [hconcreteFlip, EncodedBit.get_flip_self, hnonzeroCounter]
    rfl
  have hselectedActive :
      (coeffAdderActiveBit tail.succ counterWidth).get oddSelected = true := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork]
    exact hactiveCoeff
  have hltD : d.v.val < d.u.val := by
    simpa [d] using hlt
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get oddSelected = true := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hinput.compare hfinal
      hcontrolWork]
    simp [hltD]
  have hselectedScratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get oddSelected = false := by
    dsimp [oddSelected]
    exact coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchA_clean
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork
  have hselectedScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get oddSelected = false := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchB
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork]
    change d.scratchB = false
    exact hinput.scratchB
  have hselectedHistory :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
          oddSelected = false := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
      tail.succ counterWidth comparisonIndex roundIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork]
    exact hinput.historyFresh
  have hoddActive :
      (coeffAdderActiveBit tail.succ counterWidth).get oddCarried = true := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active]
    exact hselectedActive
  have hoddCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get oddCarried = true := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare]
    exact hselectedCompare
  have hoddScratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get oddCarried = true := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
        tail.succ counterWidth roundIndex Branch.uGreater oddSelected
        hselectedScratchA]
    rw [hselectedActive]
    rfl
  have hoddScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get oddCarried = true := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
        tail.succ counterWidth roundIndex Branch.uGreater oddSelected
        hselectedScratchB]
    rw [hselectedActive]
    rfl
  have hoddHistory :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
          oddCarried = true := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
        tail.succ counterWidth roundIndex Branch.uGreater oddSelected
        hselectedScratchB]
    rw [hselectedHistory, hselectedActive]
    rfl
  have hactiveOut : (activeBit tail counterWidth).get routed = true := by
    calc
      (activeBit tail counterWidth).get routed =
          (activeBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (activeBit tail counterWidth).get y) hroute
      _ = (coeffAdderActiveBit tail.succ counterWidth).get concrete.1 :=
        activeBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderActiveBit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = true := hoddActive
  have hcounterOut :
      (counterCarryInBit tail counterWidth).get routed = true := by
    calc
      (counterCarryInBit tail counterWidth).get routed =
          (counterCarryInBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (counterCarryInBit tail counterWidth).get y) hroute
      _ = (fullRoundWorkCounterCarryInBit tail counterWidth).get concrete :=
        counterCarryInBit_get_fullRoundWork
          tail counterWidth concrete true false x.2
      _ = true := hconcreteCounter
  have hcompareOut : (compareBit tail counterWidth).get routed = true := by
    calc
      (compareBit tail counterWidth).get routed =
          (compareBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (compareBit tail counterWidth).get y) hroute
      _ = (coeffAdderCompareBit tail.succ counterWidth).get concrete.1 :=
        compareBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderCompareBit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = true := hoddCompare
  have hscratchAOut : (scratchABit tail counterWidth).get routed = true := by
    calc
      (scratchABit tail counterWidth).get routed =
          (scratchABit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (scratchABit tail counterWidth).get y) hroute
      _ = (coeffAdderScratchABit tail.succ counterWidth).get concrete.1 :=
        scratchABit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderScratchABit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = true := hoddScratchA
  have hscratchBOut : (scratchBBit tail counterWidth).get routed = true := by
    calc
      (scratchBBit tail counterWidth).get routed =
          (scratchBBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (scratchBBit tail counterWidth).get y) hroute
      _ = (coeffAdderScratchBBit tail.succ counterWidth).get concrete.1 :=
        scratchBBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderScratchBBit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = true := hoddScratchB
  have hhistoryOut :
      (historyBit tail counterWidth roundIndex).get routed = true := by
    calc
      (historyBit tail counterWidth roundIndex).get routed =
          (historyBit tail counterWidth roundIndex).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y =>
          (historyBit tail counterWidth roundIndex).get y) hroute
      _ =
          (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
            concrete.1 :=
        historyBit_get_fullRoundWork tail counterWidth roundIndex
          concrete true false x.2
      _ =
          (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
            oddCarried := by
        rw [hconcreteCoeff]
      _ = true := hoddHistory
  let st :=
    RoundState.fromRegisters tail.succ counterWidth d kaliskiSteps paddingSteps
  have hstActive : st.active = true := by
    simpa [st, RoundState.fromRegisters, d] using hactive
  have hstV : st.v ≠ 0 := by
    simpa [st, RoundState.fromRegisters, d] using hvNonzero
  have hselect : RoundState.selectBranch st = Branch.uGreater := by
    apply RoundState.selectBranch_uGreater_of_odd_odd_lt
    · dsimp [st, RoundState.fromRegisters, d]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true d.u.val huOdd
    · dsimp [st, RoundState.fromRegisters, d]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true d.v.val hvOdd
    · simpa [st, RoundState.fromRegisters, d] using hlt
  have hroundParity : (RoundState.round st).rCoeff.testBit 0 = true := by
    calc
      (RoundState.round st).rCoeff.testBit 0 =
          (RoundState.applyBranch
            (RoundState.selectBranch st) st).rCoeff.testBit 0 := by
        rw [RoundState.round_active_nonzero_eq_applyBranch_selectBranch
          st hstActive hstV]
      _ = (RoundState.selectBranch st).auxBit :=
        sourceApplyBranch_rCoeff_testBit_zero_eq_auxBit modulus st
          hmodulusOdd hbezout
      _ = true := by
        rw [hselect]
        rfl
  have hrOddCarried :
      oddCarried.1.1.rCoeff.val = (RoundState.round st).rCoeff := by
    simpa only [oddCarried, coeffInput, st] using
      (coeffWorkSelectedOddCarriedDispatch_get_rCoeff_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex kaliskiSteps paddingSteps
        d (cleanCoeffAdderWork tail.succ) hinput.scratchA hinput.compare
        hfinal (by simpa [RegisterBits.activeBit_get] using hactive) huOdd
        hvOdd hlt hcontrolWork hcoeffWork
        (arith.uGreater_add hactive hvNonzero huOdd hvOdd hlt))
  have hrLowOut : (rCoeffLowBit tail counterWidth).get routed = true := by
    calc
      (rCoeffLowBit tail counterWidth).get routed =
          (rCoeffLowBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (rCoeffLowBit tail counterWidth).get y) hroute
      _ = concrete.1.1.1.rCoeff.val.testBit 0 :=
        rCoeffLowBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = oddCarried.1.1.rCoeff.val.testBit 0 :=
        congrArg (fun coeff => coeff.1.1.rCoeff.val.testBit 0) hconcreteCoeff
      _ = (RoundState.round st).rCoeff.testBit 0 :=
        congrArg (fun z : Nat => z.testBit 0) hrOddCarried
      _ = true := hroundParity
  exact branchResidueCertificate_uGreater tail counterWidth roundIndex routed
    hactiveOut hcounterOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- The active nonterminating odd `vLe` route leaves the zero-valued carried
branch code together with the odd-route counter latch.  The low `r` bit is
proved directly from the physical doubling path. -/
lemma routedStepBeforeCleanup_active_vLe_residueCertificate
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvOdd :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ (dataRegisters tail counterWidth x).v.val <
      (dataRegisters tail counterWidth x).u.val)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  let concrete :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex fullInput
  let nonzero :=
    fullRoundWorkKaliskiActiveNonzeroRoundStep
      tail counterWidth comparisonIndex roundIndex fullInput
  let oddSelected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth comparisonIndex coeffInput
  let oddCarried :=
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute : routed = (((concrete, true), false), x.2) := by
    dsimp [routed, concrete]
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcounterClean :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get fullInput =
        false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryInBit_get_clean tail counterWidth d
  have hcounterWorkClean :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
          fullInput = false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryWorkBit_get_clean
      tail counterWidth workIndex d
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get coeffInput =
        false := by
    dsimp [coeffInput]
    exact liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (d, cleanComparisonWork tail.succ)
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get coeffInput = true := by
    change d.active = true
    exact hactive
  have hconcreteFlip :
      concrete =
        (fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero := by
    dsimp [concrete]
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hvNonzero]
    simpa only [nonzero, fullInput, coeffInput] using
      (fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_not_lt
        tail counterWidth comparisonIndex roundIndex workIndex d
        (cleanCoeffAdderWork tail.succ)
        (cleanCounterIncrementWork counterWidth) hcounterClean
        hcounterWorkClean hinput.scratchA hinput.compare hfinal huOdd hvOdd
        hnlt hcontrolWork hactiveCoeff)
  have hnonzeroOdd :
      nonzero = (oddCarried, cleanCounterIncrementWork counterWidth) := by
    simpa only [nonzero, fullInput, coeffInput, oddCarried] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow hvLow)
  have hoddBranch :
      oddCarried =
        coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail.succ counterWidth roundIndex Branch.vLe oddSelected := by
    simpa only [oddCarried, oddSelected, coeffInput] using
      (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vLeDispatch_clean_not_lt
        tail counterWidth comparisonIndex roundIndex d
        (cleanCoeffAdderWork tail.succ) hinput.scratchA hinput.compare hfinal
        huOdd hvOdd hnlt)
  have hconcreteCoeff : concrete.1 = oddCarried := by
    calc
      concrete.1 =
          ((fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero).1 :=
        congrArg Prod.fst hconcreteFlip
      _ = nonzero.1 :=
        fullRoundWorkCounterCarryInBit_flip_coeffState
          tail counterWidth nonzero
      _ = oddCarried := congrArg Prod.fst hnonzeroOdd
  have hnonzeroCounter :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get nonzero =
        false := by
    rw [hnonzeroOdd]
    change
      (counterIncrementCarryInBit counterWidth).get
        (cleanCounterIncrementWork counterWidth) = false
    rfl
  have hconcreteCounter :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get concrete =
        true := by
    rw [hconcreteFlip, EncodedBit.get_flip_self, hnonzeroCounter]
    rfl
  have hselectedActive :
      (coeffAdderActiveBit tail.succ counterWidth).get oddSelected = true := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork]
    exact hactiveCoeff
  have hnltD : ¬ d.v.val < d.u.val := by
    simpa [d] using hnlt
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get oddSelected = false := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hinput.compare hfinal
      hcontrolWork]
    simp [hnltD]
  have hselectedScratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get oddSelected = false := by
    dsimp [oddSelected]
    exact coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchA_clean
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork
  have hselectedScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get oddSelected = false := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchB
      tail.succ counterWidth comparisonIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork]
    change d.scratchB = false
    exact hinput.scratchB
  have hselectedHistory :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
          oddSelected = false := by
    dsimp [oddSelected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
      tail.succ counterWidth comparisonIndex roundIndex d
      (cleanCoeffAdderWork tail.succ) hinput.scratchA hcontrolWork]
    exact hinput.historyFresh
  have hoddActive :
      (coeffAdderActiveBit tail.succ counterWidth).get oddCarried = true := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active]
    exact hselectedActive
  have hoddCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get oddCarried = false := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare]
    exact hselectedCompare
  have hoddScratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get oddCarried = false := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
        tail.succ counterWidth roundIndex Branch.vLe oddSelected
        hselectedScratchA]
    rw [hselectedActive]
    rfl
  have hoddScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get oddCarried = false := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
        tail.succ counterWidth roundIndex Branch.vLe oddSelected
        hselectedScratchB]
    rw [hselectedActive]
    rfl
  have hoddHistory :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
          oddCarried = false := by
    rw [hoddBranch,
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
        tail.succ counterWidth roundIndex Branch.vLe oddSelected
        hselectedScratchB]
    rw [hselectedHistory, hselectedActive]
    rfl
  have hactiveOut : (activeBit tail counterWidth).get routed = true := by
    calc
      (activeBit tail counterWidth).get routed =
          (activeBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (activeBit tail counterWidth).get y) hroute
      _ = (coeffAdderActiveBit tail.succ counterWidth).get concrete.1 :=
        activeBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderActiveBit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = true := hoddActive
  have hcounterOut :
      (counterCarryInBit tail counterWidth).get routed = true := by
    calc
      (counterCarryInBit tail counterWidth).get routed =
          (counterCarryInBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (counterCarryInBit tail counterWidth).get y) hroute
      _ = (fullRoundWorkCounterCarryInBit tail counterWidth).get concrete :=
        counterCarryInBit_get_fullRoundWork
          tail counterWidth concrete true false x.2
      _ = true := hconcreteCounter
  have hcompareOut : (compareBit tail counterWidth).get routed = false := by
    calc
      (compareBit tail counterWidth).get routed =
          (compareBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (compareBit tail counterWidth).get y) hroute
      _ = (coeffAdderCompareBit tail.succ counterWidth).get concrete.1 :=
        compareBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderCompareBit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = false := hoddCompare
  have hscratchAOut : (scratchABit tail counterWidth).get routed = false := by
    calc
      (scratchABit tail counterWidth).get routed =
          (scratchABit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (scratchABit tail counterWidth).get y) hroute
      _ = (coeffAdderScratchABit tail.succ counterWidth).get concrete.1 :=
        scratchABit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderScratchABit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = false := hoddScratchA
  have hscratchBOut : (scratchBBit tail counterWidth).get routed = false := by
    calc
      (scratchBBit tail counterWidth).get routed =
          (scratchBBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (scratchBBit tail counterWidth).get y) hroute
      _ = (coeffAdderScratchBBit tail.succ counterWidth).get concrete.1 :=
        scratchBBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = (coeffAdderScratchBBit tail.succ counterWidth).get oddCarried := by
        rw [hconcreteCoeff]
      _ = false := hoddScratchB
  have hhistoryOut :
      (historyBit tail counterWidth roundIndex).get routed = false := by
    calc
      (historyBit tail counterWidth roundIndex).get routed =
          (historyBit tail counterWidth roundIndex).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y =>
          (historyBit tail counterWidth roundIndex).get y) hroute
      _ =
          (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
            concrete.1 :=
        historyBit_get_fullRoundWork tail counterWidth roundIndex
          concrete true false x.2
      _ =
          (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
            oddCarried := by
        rw [hconcreteCoeff]
      _ = false := hoddHistory
  have hrOddCarried :
      oddCarried.1.1.rCoeff = wordDouble (tail.succ + 1) d.rCoeff := by
    simpa only [oddCarried, coeffInput] using
      (coeffWorkSelectedOddCarriedDispatch_get_rCoeff_vLe_wordDouble_clean
        tail counterWidth comparisonIndex roundIndex d
        (cleanCoeffAdderWork tail.succ) hinput.scratchA hinput.compare hfinal
        huOdd hvOdd hnlt hcontrolWork hactiveCoeff
        (arith.vLe_msb hactive hvNonzero huOdd hvOdd hnlt))
  have hrLowOut : (rCoeffLowBit tail counterWidth).get routed = false := by
    calc
      (rCoeffLowBit tail counterWidth).get routed =
          (rCoeffLowBit tail counterWidth).get
            (((concrete, true), false), x.2) :=
        congrArg (fun y => (rCoeffLowBit tail counterWidth).get y) hroute
      _ = concrete.1.1.1.rCoeff.val.testBit 0 :=
        rCoeffLowBit_get_fullRoundWork tail counterWidth concrete true false x.2
      _ = oddCarried.1.1.rCoeff.val.testBit 0 :=
        congrArg (fun coeff => coeff.1.1.rCoeff.val.testBit 0) hconcreteCoeff
      _ = (wordDouble (tail.succ + 1) d.rCoeff).val.testBit 0 :=
        congrArg (fun word => word.val.testBit 0) hrOddCarried
      _ = false := by
        simp
  exact branchResidueCertificate_vLe tail counterWidth roundIndex routed
    hactiveOut hcounterOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- Inactive padding reaches the complete reusable-work boundary before the
four residue targets are inspected. -/
lemma routedStepBeforeCleanup_inactive_reusableWorkspaceClean
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = false) :
    ReusableWorkspaceClean tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  rw [routedStepBeforeCleanup,
    controlledActiveOnlyStructuredStep_after_latch_padding_inactive_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive]
  constructor <;> rfl

/-- The terminating active route restores every reusable work register before
the common residue-cleanup suffix. -/
lemma routedStepBeforeCleanup_active_terminated_reusableWorkspaceClean
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvZero : (dataRegisters tail counterWidth x).v.val = 0) :
    ReusableWorkspaceClean tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  rw [routedStepBeforeCleanup,
    controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive]
  rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
    tail counterWidth comparisonIndex roundIndex workIndex
    (dataRegisters tail counterWidth x) hinput.compare hactive hvZero
    hinput.scratchA hinput.scratchB]
  constructor <;> rfl

/-- The concrete active `uEven` route preserves all reusable work objects;
only the four certified branch residues remain for the common cleanup. -/
lemma routedStepBeforeCleanup_active_uEven_reusableWorkspaceClean
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huEven :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = false) :
    ReusableWorkspaceClean tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let selected :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x =
        (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex fullInput,
          true), false), x.2) := by
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = false := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hconcrete :
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex fullInput =
        (selected, cleanCounterIncrementWork counterWidth) := by
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hvNonzero huLow]
    simpa [selected, coeffInput] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow)
  have hcomparison : selected.1.2 = cleanComparisonWork tail.succ := by
    simpa [selected, coeffInput] using
      selectedDispatch_comparisonWork_clean tail counterWidth
        comparisonIndex roundIndex d hinput.scratchA hinput.scratchB
  have hcoefficient : selected.2 = cleanCoeffAdderWork tail.succ := by
    simpa [selected, coeffInput] using
      selectedDispatch_coefficientWork_clean tail counterWidth
        comparisonIndex roundIndex d
  rw [hroute, hconcrete]
  exact
    { comparisonWork := hcomparison
      coefficientWork := hcoefficient
      counterSource := rfl
      counterCarryWork := rfl
      control := rfl }

private lemma routedStepBeforeCleanup_active_uEven_counter
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huEven :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = false) :
    (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).counter =
      (dataRegisters tail counterWidth x).counter := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let selected :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x =
        (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex fullInput,
          true), false), x.2) := by
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = false := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hconcrete :
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex fullInput =
        (selected, cleanCounterIncrementWork counterWidth) := by
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hvNonzero huLow]
    simpa [selected, coeffInput] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow)
  rw [hroute, hconcrete]
  change selected.1.1.counter = d.counter
  simpa only [selected, coeffInput] using
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_counter
      tail counterWidth comparisonIndex roundIndex coeffInput)

private lemma routedStepBeforeCleanup_active_vEven_counter
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvEven :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = false) :
    (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).counter =
      (dataRegisters tail counterWidth x).counter := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let selected :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x =
        (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex fullInput,
          true), false), x.2) := by
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = false := by
    dsimp [coeffInput, d]
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hconcrete :
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex fullInput =
        (selected, cleanCounterIncrementWork counterWidth) := by
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
        tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
        hvNonzero huLow hvLow]
    simpa [selected, coeffInput] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow hvLow)
  rw [hroute, hconcrete]
  change selected.1.1.counter = d.counter
  simpa only [selected, coeffInput] using
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_counter
      tail counterWidth comparisonIndex roundIndex coeffInput)

/-- The concrete active `vEven` route has the same complete reusable-work
boundary as `uEven`. -/
lemma routedStepBeforeCleanup_active_vEven_reusableWorkspaceClean
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvEven :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = false) :
    ReusableWorkspaceClean tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let selected :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x =
        (((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
            tail counterWidth comparisonIndex roundIndex workIndex fullInput,
          true), false), x.2) := by
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = false := by
    dsimp [coeffInput, d]
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hconcrete :
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex fullInput =
        (selected, cleanCounterIncrementWork counterWidth) := by
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
        tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
        hvNonzero huLow hvLow]
    simpa [selected, coeffInput] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow hvLow)
  have hcomparison : selected.1.2 = cleanComparisonWork tail.succ := by
    simpa [selected, coeffInput] using
      selectedDispatch_comparisonWork_clean tail counterWidth
        comparisonIndex roundIndex d hinput.scratchA hinput.scratchB
  have hcoefficient : selected.2 = cleanCoeffAdderWork tail.succ := by
    simpa [selected, coeffInput] using
      selectedDispatch_coefficientWork_clean tail counterWidth
        comparisonIndex roundIndex d
  rw [hroute, hconcrete]
  exact
    { comparisonWork := hcomparison
      coefficientWork := hcoefficient
      counterSource := rfl
      counterCarryWork := rfl
      control := rfl }

set_option maxHeartbeats 800000 in
-- Normalizing the shared odd-route cleanup expands the complete nested workspace.
/-- Both active odd branches share one physical reusable-work proof.  The
comparison decision affects source data and branch-code residue, but the
complete comparison/coefficient work and the non-latch counter work are clean
on either side of that decision. -/
lemma routedStepBeforeCleanup_active_odd_reusableWorkspaceClean
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvOdd :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = true)
    (hfinal : comparisonIndex.val + 1 = tail.succ) :
    ReusableWorkspaceClean tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let concrete :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex fullInput
  let nonzero :=
    fullRoundWorkKaliskiActiveNonzeroRoundStep
      tail counterWidth comparisonIndex roundIndex fullInput
  let oddCarried :=
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x = (((concrete, true), false), x.2) := by
    dsimp [concrete]
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcounterClean :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get fullInput =
        false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryInBit_get_clean tail counterWidth d
  have hcounterWorkClean :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
          fullInput = false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryWorkBit_get_clean
      tail counterWidth workIndex d
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get coeffInput =
        false := by
    dsimp [coeffInput]
    exact liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (d, cleanComparisonWork tail.succ)
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get coeffInput = true := by
    change d.active = true
    exact hactive
  have hnonzeroOdd :
      nonzero = (oddCarried, cleanCounterIncrementWork counterWidth) := by
    simpa only [nonzero, fullInput, coeffInput, oddCarried] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow hvLow)
  have hconcreteFlip :
      concrete =
        (fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero := by
    dsimp [concrete]
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hvNonzero]
    by_cases hlt : d.v.val < d.u.val
    · simpa only [nonzero, fullInput, coeffInput] using
        (fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_lt
          tail counterWidth comparisonIndex roundIndex workIndex d
          (cleanCoeffAdderWork tail.succ)
          (cleanCounterIncrementWork counterWidth) hcounterClean
          hcounterWorkClean hinput.scratchA hinput.compare hfinal huOdd hvOdd
          hlt hcontrolWork hactiveCoeff)
    · simpa only [nonzero, fullInput, coeffInput] using
        (fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_not_lt
          tail counterWidth comparisonIndex roundIndex workIndex d
          (cleanCoeffAdderWork tail.succ)
          (cleanCounterIncrementWork counterWidth) hcounterClean
          hcounterWorkClean hinput.scratchA hinput.compare hfinal huOdd hvOdd
          hlt hcontrolWork hactiveCoeff)
  have hconcreteCoeff : concrete.1 = oddCarried := by
    calc
      concrete.1 =
          ((fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero).1 :=
        congrArg Prod.fst hconcreteFlip
      _ = nonzero.1 :=
        fullRoundWorkCounterCarryInBit_flip_coeffState
          tail counterWidth nonzero
      _ = oddCarried := congrArg Prod.fst hnonzeroOdd
  have hoddComparison :
      oddCarried.1.2 = cleanComparisonWork tail.succ := by
    simpa only [oddCarried, coeffInput] using
      (oddCarriedDispatch_comparisonWork_clean tail counterWidth
        comparisonIndex roundIndex d hinput.scratchA hfinal)
  have hoddCoefficient :
      oddCarried.2 = cleanCoeffAdderWork tail.succ := by
    simpa only [oddCarried, coeffInput] using
      (oddCarriedDispatch_coefficientWork_clean tail counterWidth
        comparisonIndex roundIndex d hinput.scratchA)
  have hconcreteComparison :
      concrete.1.1.2 = cleanComparisonWork tail.succ := by
    rw [hconcreteCoeff]
    exact hoddComparison
  have hconcreteCoefficient :
      concrete.1.2 = cleanCoeffAdderWork tail.succ := by
    rw [hconcreteCoeff]
    exact hoddCoefficient
  have hconcreteCounterSource : concrete.2.1 = 1 := by
    rw [hconcreteFlip, hnonzeroOdd]
    rfl
  have hconcreteCounterCarryWork :
      concrete.2.2.2 =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork counterWidth := by
    rw [hconcreteFlip, hnonzeroOdd]
    rfl
  rw [hroute]
  exact
    { comparisonWork := hconcreteComparison
      coefficientWork := hconcreteCoefficient
      counterSource := hconcreteCounterSource
      counterCarryWork := hconcreteCounterCarryWork
      control := rfl }

set_option maxHeartbeats 800000 in
-- The counter proof expands both even dispatches and the carried odd route.
private lemma routedStepBeforeCleanup_active_odd_counter
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvOdd :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = true)
    (hfinal : comparisonIndex.val + 1 = tail.succ) :
    (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).counter =
      (dataRegisters tail counterWidth x).counter := by
  let d := dataRegisters tail counterWidth x
  let coeffInput : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((d, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
  let fullInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (coeffInput, cleanCounterIncrementWork counterWidth)
  let concrete :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex fullInput
  let nonzero :=
    fullRoundWorkKaliskiActiveNonzeroRoundStep
      tail counterWidth comparisonIndex roundIndex fullInput
  let oddCarried :=
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
      tail counterWidth comparisonIndex roundIndex coeffInput
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x = (((concrete, true), false), x.2) := by
    dsimp [concrete]
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          coeffInput = true := by
    dsimp [coeffInput, d]
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcounterClean :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get fullInput =
        false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryInBit_get_clean tail counterWidth d
  have hcounterWorkClean :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
          fullInput = false := by
    dsimp [fullInput, coeffInput]
    exact fullRoundWorkCounterCarryWorkBit_get_clean
      tail counterWidth workIndex d
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get coeffInput =
        false := by
    dsimp [coeffInput]
    exact liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (d, cleanComparisonWork tail.succ)
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get coeffInput = true := by
    change d.active = true
    exact hactive
  have hnonzeroOdd :
      nonzero = (oddCarried, cleanCounterIncrementWork counterWidth) := by
    simpa only [nonzero, fullInput, coeffInput, oddCarried] using
      (fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
        tail counterWidth comparisonIndex roundIndex
        ((((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)) huLow hvLow)
  have hconcreteFlip :
      concrete =
        (fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero := by
    dsimp [concrete]
    rw [show fullInput =
        (((d, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) by rfl]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hvNonzero]
    by_cases hlt : d.v.val < d.u.val
    · simpa only [nonzero, fullInput, coeffInput] using
        (fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_lt
          tail counterWidth comparisonIndex roundIndex workIndex d
          (cleanCoeffAdderWork tail.succ)
          (cleanCounterIncrementWork counterWidth) hcounterClean
          hcounterWorkClean hinput.scratchA hinput.compare hfinal huOdd hvOdd
          hlt hcontrolWork hactiveCoeff)
    · simpa only [nonzero, fullInput, coeffInput] using
        (fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_not_lt
          tail counterWidth comparisonIndex roundIndex workIndex d
          (cleanCoeffAdderWork tail.succ)
          (cleanCounterIncrementWork counterWidth) hcounterClean
          hcounterWorkClean hinput.scratchA hinput.compare hfinal huOdd hvOdd
          hlt hcontrolWork hactiveCoeff)
  have hconcreteCoeff : concrete.1 = oddCarried := by
    calc
      concrete.1 =
          ((fullRoundWorkCounterCarryInBit tail counterWidth).flip nonzero).1 :=
        congrArg Prod.fst hconcreteFlip
      _ = nonzero.1 :=
        fullRoundWorkCounterCarryInBit_flip_coeffState
          tail counterWidth nonzero
      _ = oddCarried := congrArg Prod.fst hnonzeroOdd
  rw [hroute]
  change concrete.1.1.1.counter = d.counter
  rw [hconcreteCoeff]
  exact
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_get_counter_clean
      tail counterWidth comparisonIndex roundIndex coeffInput hinput.scratchA
      hcontrolWork

/-- Every active nonterminating route preserves the physical padding counter.
The proof splits only on the physical parity controls used by the static
dispatcher. -/
lemma routedStepBeforeCleanup_active_nonzero_counter
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (hfinal : comparisonIndex.val + 1 = tail.succ) :
    (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).counter =
      (dataRegisters tail counterWidth x).counter := by
  by_cases huEven :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = false
  · exact routedStepBeforeCleanup_active_uEven_counter
      tail counterWidth comparisonIndex roundIndex workIndex x hinput hactive
      hvNonzero huEven
  · have huOdd :
        (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true := by
      cases h : (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) <;>
        simp_all
    by_cases hvEven :
        (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = false
    · exact routedStepBeforeCleanup_active_vEven_counter
        tail counterWidth comparisonIndex roundIndex workIndex x hinput
        hactive hvNonzero huOdd hvEven
    · have hvOdd :
          (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = true := by
        cases h :
            (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) <;>
          simp_all
      exact routedStepBeforeCleanup_active_odd_counter
        tail counterWidth comparisonIndex roundIndex workIndex x hinput
        hactive hvNonzero huOdd hvOdd hfinal

private lemma routedPersistentBoundary_of_raw
    (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) (source : RoundState)
    (before routed : RegistersWithRouteHistory tail.succ counterWidth)
    (hu : (dataRegisters tail counterWidth routed).u.val =
      (RoundState.round source).u)
    (hv : (dataRegisters tail counterWidth routed).v.val =
      (RoundState.round source).v)
    (hr : (dataRegisters tail counterWidth routed).rCoeff.val =
      (RoundState.round source).rCoeff)
    (hs : (dataRegisters tail counterWidth routed).sCoeff.val =
      (RoundState.round source).sCoeff)
    (ha : (dataRegisters tail counterWidth routed).active =
      (RoundState.round source).active)
    (hc : (dataRegisters tail counterWidth routed).counter.val =
      (RoundState.round source).paddingSteps % 2 ^ counterWidth)
    (hh : (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
      (dataRegisters tail counterWidth routed) = RoundState.historyBit source)
    (hpres : ∀ observed : Fin (2 * tail.succ), roundIndex ≠ observed ->
      (RegisterBits.historyBit tail.succ counterWidth observed).get
          (dataRegisters tail counterWidth routed) =
        (RegisterBits.historyBit tail.succ counterWidth observed).get
          (dataRegisters tail counterWidth before)) :
    RoutedPersistentBoundary tail counterWidth roundIndex source before
      routed := by
  refine
    { sourceAfter := ?_
      counterAfter := hc
      historyWritten := hh
      historyPreserved := hpres }
  cases hround : RoundState.round source with
  | mk u v rCoeff sCoeff kaliskiSteps paddingSteps active =>
      simp only [hround] at hu hv hr hs ha
      simp [RoundState.fromRegisters, hu, hv, hr, hs, ha]

set_option maxHeartbeats 800000 in
-- The active getter unfolds the complete routed concrete round and cleanup suffix.
private lemma routedStepBeforeCleanup_active_nonzero_get_active
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (hfinal : comparisonIndex.val + 1 = tail.succ) :
    (dataRegisters tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x)).active = true := by
  rw [routedStepBeforeCleanup,
    controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive]
  change
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex
      ((((dataRegisters tail counterWidth x),
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)).1.1.1.active = true
  exact fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_active_clean
    tail counterWidth comparisonIndex roundIndex workIndex
    (dataRegisters tail counterWidth x) hinput.scratchA hinput.compare hfinal
    hactive hvNonzero

set_option maxHeartbeats 800000 in
-- Preserving an arbitrary history slot unfolds the routed round's nested products.
private lemma routedStepBeforeCleanup_active_nonzero_get_historyBit_of_ne
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex observed : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (hne : roundIndex ≠ observed) :
    (RegisterBits.historyBit tail.succ counterWidth observed).get
        (dataRegisters tail counterWidth
          (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
            workIndex x)) =
      (RegisterBits.historyBit tail.succ counterWidth observed).get
        (dataRegisters tail counterWidth x) := by
  rw [routedStepBeforeCleanup,
    controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive]
  change
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex roundIndex workIndex
          ((((dataRegisters tail counterWidth x),
              cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1 = _
  exact
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_historyBit_of_ne_clean
      tail counterWidth comparisonIndex roundIndex observed workIndex
      (dataRegisters tail counterWidth x) hinput.compare hactive hvNonzero
      hinput.scratchA hne

set_option maxHeartbeats 800000 in
-- Packaging the raw branch readouts normalizes every persistent register projection.
private lemma routedPersistentBoundary_active_nonzero_of_raw
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource :
      RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x)
          source.kaliskiSteps source.paddingSteps = source)
    (hcounter :
      (dataRegisters tail counterWidth x).counter.val =
        source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hu :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).u.val = (RoundState.round source).u)
    (hv :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).v.val = (RoundState.round source).v)
    (hr :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).rCoeff.val = (RoundState.round source).rCoeff)
    (hs :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).sCoeff.val = (RoundState.round source).sCoeff)
    (hh :
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
          (dataRegisters tail counterWidth
            (routedStepBeforeCleanup tail counterWidth comparisonIndex
              roundIndex workIndex x)) = RoundState.historyBit source) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  have hsourceActive : source.active = true := by
    calc
      source.active =
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps).active :=
        congrArg RoundState.active hsource.symm
      _ = true := hactive
  have hsourceV : source.v ≠ 0 := by
    intro hz
    apply hvNonzero
    calc
      (dataRegisters tail counterWidth x).v.val =
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps).v := rfl
      _ = source.v := congrArg RoundState.v hsource
      _ = 0 := hz
  have hroundActive : (RoundState.round source).active = true := by
    exact RoundState.round_active_nonzero_active source hsourceActive hsourceV
  have hroundPadding :
      (RoundState.round source).paddingSteps = source.paddingSteps := by
    exact RoundState.round_active_nonzero_paddingSteps source hsourceActive
      hsourceV
  have ha :
      (dataRegisters tail counterWidth routed).active =
        (RoundState.round source).active := by
    exact
      (routedStepBeforeCleanup_active_nonzero_get_active
        tail counterWidth comparisonIndex roundIndex workIndex x hinput
        hactive hvNonzero hfinal).trans hroundActive.symm
  have hc :
      (dataRegisters tail counterWidth routed).counter.val =
        (RoundState.round source).paddingSteps % 2 ^ counterWidth := by
    calc
      (dataRegisters tail counterWidth routed).counter.val =
          (dataRegisters tail counterWidth x).counter.val := by
        exact congrArg Fin.val
          (routedStepBeforeCleanup_active_nonzero_counter
            tail counterWidth comparisonIndex roundIndex workIndex x hinput
            hactive hvNonzero hfinal)
      _ = source.paddingSteps % 2 ^ counterWidth := hcounter
      _ = (RoundState.round source).paddingSteps % 2 ^ counterWidth := by
        rw [hroundPadding]
  have hpres :
      ∀ observed : Fin (2 * tail.succ), roundIndex ≠ observed ->
        (RegisterBits.historyBit tail.succ counterWidth observed).get
            (dataRegisters tail counterWidth routed) =
          (RegisterBits.historyBit tail.succ counterWidth observed).get
            (dataRegisters tail counterWidth x) := by
    intro observed hne
    exact
      routedStepBeforeCleanup_active_nonzero_get_historyBit_of_ne
        tail counterWidth comparisonIndex roundIndex observed workIndex x
        hinput hactive hvNonzero hne
  exact routedPersistentBoundary_of_raw tail counterWidth roundIndex source x
    routed hu hv hr hs ha hc hh hpres

/-- Inactive padding preserves source data/history, advances only the physical
counter, and matches the source inactive round. -/
lemma routedStepBeforeCleanup_inactive_persistentBoundary
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = false) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  have hsourceActive : source.active = false := by
    calc
      source.active =
          (RoundState.fromRegisters tail.succ counterWidth d
            source.kaliskiSteps source.paddingSteps).active :=
        congrArg RoundState.active hsource.symm
      _ = false := hactive
  have hroute :
      routed =
        (((((({ d with counter := wordIncrement counterWidth d.counter },
            cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), false), false), x.2) := by
    dsimp [routed]
    exact controlledActiveOnlyStructuredStep_after_latch_padding_inactive_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive
  have hu : (dataRegisters tail counterWidth routed).u.val =
      (RoundState.round source).u := by
    rw [hroute, RoundState.round_inactive source hsourceActive]
    exact congrArg RoundState.u hsource
  have hv : (dataRegisters tail counterWidth routed).v.val =
      (RoundState.round source).v := by
    rw [hroute, RoundState.round_inactive source hsourceActive]
    exact congrArg RoundState.v hsource
  have hr : (dataRegisters tail counterWidth routed).rCoeff.val =
      (RoundState.round source).rCoeff := by
    rw [hroute, RoundState.round_inactive source hsourceActive]
    exact congrArg RoundState.rCoeff hsource
  have hs : (dataRegisters tail counterWidth routed).sCoeff.val =
      (RoundState.round source).sCoeff := by
    rw [hroute, RoundState.round_inactive source hsourceActive]
    exact congrArg RoundState.sCoeff hsource
  have ha : (dataRegisters tail counterWidth routed).active =
      (RoundState.round source).active := by
    rw [hroute, RoundState.round_inactive source hsourceActive]
    exact congrArg RoundState.active hsource
  have hc : (dataRegisters tail counterWidth routed).counter.val =
      (RoundState.round source).paddingSteps % 2 ^ counterWidth := by
    rw [hroute,
      RoundState.round_inactive_paddingSteps source hsourceActive]
    change (wordIncrement counterWidth d.counter).val =
      (source.paddingSteps + 1) % 2 ^ counterWidth
    rw [wordIncrement_val, hcounter, Nat.mod_add_mod]
  have hh :
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
          (dataRegisters tail counterWidth routed) =
        RoundState.historyBit source := by
    rw [hroute]
    calc
      _ = false := hinput.historyFresh
      _ = RoundState.historyBit source :=
        (RoundState.historyBit_inactive source hsourceActive).symm
  have hpres :
      ∀ observed : Fin (2 * tail.succ), roundIndex ≠ observed ->
        (RegisterBits.historyBit tail.succ counterWidth observed).get
            (dataRegisters tail counterWidth routed) =
          (RegisterBits.historyBit tail.succ counterWidth observed).get
            (dataRegisters tail counterWidth x) := by
    intro observed _
    rw [hroute]
    change
      (RegisterBits.historyBit tail.succ counterWidth observed).get d =
        (RegisterBits.historyBit tail.succ counterWidth observed).get
          (dataRegisters tail counterWidth x)
    rfl
  exact routedPersistentBoundary_of_raw tail counterWidth roundIndex source x
    routed hu hv hr hs ha hc hh hpres

/-- An active terminating round preserves source data/history, clears active,
and advances the physical padding counter exactly once. -/
lemma routedStepBeforeCleanup_active_terminated_persistentBoundary
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvZero : (dataRegisters tail counterWidth x).v.val = 0) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d := dataRegisters tail counterWidth x
  let terminated : Registers tail.succ counterWidth :=
    { { d with active := false } with
      counter := wordIncrement counterWidth d.counter }
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  have hsourceActive : source.active = true := by
    calc
      source.active =
          (RoundState.fromRegisters tail.succ counterWidth d
            source.kaliskiSteps source.paddingSteps).active :=
        congrArg RoundState.active hsource.symm
      _ = true := hactive
  have hsourceV : source.v = 0 := by
    calc
      source.v =
          (RoundState.fromRegisters tail.succ counterWidth d
            source.kaliskiSteps source.paddingSteps).v :=
        congrArg RoundState.v hsource.symm
      _ = 0 := hvZero
  have hroute :
      routed =
        ((((((terminated, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), true), false), x.2) := by
    dsimp [routed]
    rw [routedStepBeforeCleanup,
      controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean hactive]
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
      tail counterWidth comparisonIndex roundIndex workIndex d hinput.compare
      hactive hvZero hinput.scratchA hinput.scratchB]
  have hu : (dataRegisters tail counterWidth routed).u.val =
      (RoundState.round source).u := by
    rw [hroute, RoundState.round_active_terminated source hsourceActive
      hsourceV]
    exact congrArg RoundState.u hsource
  have hv : (dataRegisters tail counterWidth routed).v.val =
      (RoundState.round source).v := by
    rw [hroute, RoundState.round_active_terminated source hsourceActive
      hsourceV]
    exact congrArg RoundState.v hsource
  have hr : (dataRegisters tail counterWidth routed).rCoeff.val =
      (RoundState.round source).rCoeff := by
    rw [hroute, RoundState.round_active_terminated source hsourceActive
      hsourceV]
    exact congrArg RoundState.rCoeff hsource
  have hs : (dataRegisters tail counterWidth routed).sCoeff.val =
      (RoundState.round source).sCoeff := by
    rw [hroute, RoundState.round_active_terminated source hsourceActive
      hsourceV]
    exact congrArg RoundState.sCoeff hsource
  have ha : (dataRegisters tail counterWidth routed).active =
      (RoundState.round source).active := by
    rw [hroute, RoundState.round_active_terminated source hsourceActive
      hsourceV]
    change terminated.active = false
    rfl
  have hc : (dataRegisters tail counterWidth routed).counter.val =
      (RoundState.round source).paddingSteps % 2 ^ counterWidth := by
    rw [hroute,
      RoundState.round_active_terminated_paddingSteps source hsourceActive
        hsourceV]
    change (wordIncrement counterWidth d.counter).val =
      (source.paddingSteps + 1) % 2 ^ counterWidth
    rw [wordIncrement_val, hcounter, Nat.mod_add_mod]
  have hh :
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
          (dataRegisters tail counterWidth routed) =
        RoundState.historyBit source := by
    rw [hroute]
    calc
      _ = false := hinput.historyFresh
      _ = RoundState.historyBit source :=
        (RoundState.historyBit_active_terminated source hsourceActive
          hsourceV).symm
  have hpres :
      ∀ observed : Fin (2 * tail.succ), roundIndex ≠ observed ->
        (RegisterBits.historyBit tail.succ counterWidth observed).get
            (dataRegisters tail counterWidth routed) =
          (RegisterBits.historyBit tail.succ counterWidth observed).get
            (dataRegisters tail counterWidth x) := by
    intro observed _
    rw [hroute]
    change
      (RegisterBits.historyBit tail.succ counterWidth observed).get terminated =
        (RegisterBits.historyBit tail.succ counterWidth observed).get d
    rfl
  exact routedPersistentBoundary_of_raw tail counterWidth roundIndex source x
    routed hu hv hr hs ha hc hh hpres

set_option maxHeartbeats 800000 in
-- The u-even boundary combines all raw readouts with the full source-state extensionality.
/-- The active nonterminating `uEven` route matches the raw source round and
preserves all persistent state outside the selected history slot. -/
lemma routedStepBeforeCleanup_active_uEven_persistentBoundary
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huEven :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d : Registers tail.succ counterWidth :=
    dataRegisters tail counterWidth x
  let concrete : RegistersWithFullRoundWork tail.succ counterWidth :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex
      (((d, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  let routed : RegistersWithRouteHistory tail.succ counterWidth :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  have hroute : routed = (((concrete, true), false), x.2) := by
    dsimp [routed, concrete]
    exact controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get d = true := by
    simpa [d, RegisterBits.activeBit_get] using hactive
  have hsourceD :
      RoundState.fromRegisters tail.succ counterWidth d
        source.kaliskiSteps source.paddingSteps = source := by
    simpa only [d] using hsource
  have hdata :
      dataRegisters tail counterWidth routed = concrete.1.1.1 := by
    calc
      dataRegisters tail counterWidth routed =
          dataRegisters tail counterWidth
            (((concrete, true), false), x.2) :=
        congrArg (dataRegisters tail counterWidth) hroute
      _ = concrete.1.1.1 := rfl
  have huConcrete :
      concrete.1.1.1.u.val = (RoundState.round source).u := by
    calc
      concrete.1.1.1.u.val =
          (RoundState.round
            (RoundState.fromRegisters tail.succ counterWidth d
              source.kaliskiSteps source.paddingSteps)).u := by
        simpa only [concrete] using
          (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uEven_eq_sourceRound_clean
            tail counterWidth comparisonIndex roundIndex workIndex
            source.kaliskiSteps source.paddingSteps d hinput.scratchA
            hinput.scratchB hinput.compare hactiveBit hvNonzero huEven)
      _ = (RoundState.round source).u :=
        congrArg (fun state => (RoundState.round state).u) hsourceD
  have hu : (dataRegisters tail counterWidth routed).u.val =
      (RoundState.round source).u := by
    rw [hdata]
    exact huConcrete
  have hvConcrete :
      concrete.1.1.1.v.val = (RoundState.round source).v := by
    calc
      concrete.1.1.1.v.val =
          (RoundState.round
            (RoundState.fromRegisters tail.succ counterWidth d
              source.kaliskiSteps source.paddingSteps)).v := by
        simpa only [concrete] using
          (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_uEven_eq_sourceRound_clean
            tail counterWidth comparisonIndex roundIndex workIndex
            source.kaliskiSteps source.paddingSteps d hinput.scratchA
            hinput.scratchB hinput.compare hactiveBit hvNonzero huEven)
      _ = (RoundState.round source).v :=
        congrArg (fun state => (RoundState.round state).v) hsourceD
  have hv : (dataRegisters tail counterWidth routed).v.val =
      (RoundState.round source).v := by
    rw [hdata]
    exact hvConcrete
  have hrConcrete :
      concrete.1.1.1.rCoeff.val = (RoundState.round source).rCoeff := by
    calc
      concrete.1.1.1.rCoeff.val =
          (RoundState.round
            (RoundState.fromRegisters tail.succ counterWidth d
              source.kaliskiSteps source.paddingSteps)).rCoeff := by
        simpa only [concrete] using
          (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uEven_eq_sourceRound_clean
            tail counterWidth comparisonIndex roundIndex workIndex
            source.kaliskiSteps source.paddingSteps d hinput.scratchA
            hinput.scratchB hinput.compare hactiveBit hvNonzero huEven)
      _ = (RoundState.round source).rCoeff :=
        congrArg (fun state => (RoundState.round state).rCoeff) hsourceD
  have hr : (dataRegisters tail counterWidth routed).rCoeff.val =
      (RoundState.round source).rCoeff := by
    rw [hdata]
    exact hrConcrete
  have hsConcrete :
      concrete.1.1.1.sCoeff.val = (RoundState.round source).sCoeff := by
    calc
      concrete.1.1.1.sCoeff.val =
          (RoundState.round
            (RoundState.fromRegisters tail.succ counterWidth d
              source.kaliskiSteps source.paddingSteps)).sCoeff := by
        simpa only [concrete] using
          (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uEven_eq_sourceRound_clean
            tail counterWidth comparisonIndex roundIndex workIndex
            source.kaliskiSteps source.paddingSteps d hinput.scratchA
            hinput.scratchB hinput.compare hactiveBit hvNonzero huEven
            (arith.uEven_msb hactive hvNonzero huEven)
            (arith.uEven_double hactive hvNonzero huEven))
      _ = (RoundState.round source).sCoeff :=
        congrArg (fun state => (RoundState.round state).sCoeff) hsourceD
  have hs : (dataRegisters tail counterWidth routed).sCoeff.val =
      (RoundState.round source).sCoeff := by
    rw [hdata]
    exact hsConcrete
  have hhConcrete :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get concrete.1 =
        RoundState.historyBit source := by
    calc
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get concrete.1 =
          RoundState.historyBit
            (RoundState.fromRegisters tail.succ counterWidth d
              source.kaliskiSteps source.paddingSteps) := by
        simpa only [concrete] using
          (
        fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_uEven_eq_sourceHistoryBit_clean
            tail counterWidth comparisonIndex roundIndex workIndex
            source.kaliskiSteps source.paddingSteps d hinput.scratchA
            hinput.scratchB hinput.compare hactiveBit hinput.historyFresh
            hvNonzero huEven)
      _ = RoundState.historyBit source :=
        congrArg RoundState.historyBit hsourceD
  have hh :
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
          (dataRegisters tail counterWidth routed) =
        RoundState.historyBit source := by
    rw [hdata]
    change
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get concrete.1 = _
    exact hhConcrete
  exact routedPersistentBoundary_active_nonzero_of_raw tail counterWidth
    comparisonIndex roundIndex workIndex source x hinput hsource hcounter
    hactive hvNonzero hfinal hu hv hr hs hh

set_option maxHeartbeats 800000 in
-- This wrapper normalizes the concrete branch readouts before applying the raw boundary.
private lemma routedPersistentBoundary_active_nonzero_of_concrete
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (concrete : RegistersWithFullRoundWork tail.succ counterWidth)
    (hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x = (((concrete, true), false), x.2))
    (huConcrete : concrete.1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x) source.kaliskiSteps
          source.paddingSteps)).u)
    (hvConcrete : concrete.1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x) source.kaliskiSteps
          source.paddingSteps)).v)
    (hrConcrete : concrete.1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x) source.kaliskiSteps
          source.paddingSteps)).rCoeff)
    (hsConcrete : concrete.1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x) source.kaliskiSteps
          source.paddingSteps)).sCoeff)
    (hhConcrete :
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get concrete.1 =
        RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps)) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  have hdata :
      dataRegisters tail counterWidth
          (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
            workIndex x) = concrete.1.1.1 := by
    calc
      _ = dataRegisters tail counterWidth
          (((concrete, true), false), x.2) :=
        congrArg (dataRegisters tail counterWidth) hroute
      _ = concrete.1.1.1 := rfl
  have hu :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).u.val = (RoundState.round source).u := by
    calc
      _ = concrete.1.1.1.u.val :=
        congrArg (fun regs => regs.u.val) hdata
      _ = (RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps)).u := huConcrete
      _ = (RoundState.round source).u :=
        congrArg (fun state => (RoundState.round state).u) hsource
  have hv :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).v.val = (RoundState.round source).v := by
    calc
      _ = concrete.1.1.1.v.val :=
        congrArg (fun regs => regs.v.val) hdata
      _ = (RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps)).v := hvConcrete
      _ = (RoundState.round source).v :=
        congrArg (fun state => (RoundState.round state).v) hsource
  have hr :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).rCoeff.val = (RoundState.round source).rCoeff := by
    calc
      _ = concrete.1.1.1.rCoeff.val :=
        congrArg (fun regs => regs.rCoeff.val) hdata
      _ = (RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps)).rCoeff := hrConcrete
      _ = (RoundState.round source).rCoeff :=
        congrArg (fun state => (RoundState.round state).rCoeff) hsource
  have hs :
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).sCoeff.val = (RoundState.round source).sCoeff := by
    calc
      _ = concrete.1.1.1.sCoeff.val :=
        congrArg (fun regs => regs.sCoeff.val) hdata
      _ = (RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps)).sCoeff := hsConcrete
      _ = (RoundState.round source).sCoeff :=
        congrArg (fun state => (RoundState.round state).sCoeff) hsource
  have hh :
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
          (dataRegisters tail counterWidth
            (routedStepBeforeCleanup tail counterWidth comparisonIndex
              roundIndex workIndex x)) = RoundState.historyBit source := by
    calc
      _ = (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
          concrete.1.1.1 :=
        congrArg
          (fun regs =>
            (RegisterBits.historyBit tail.succ counterWidth roundIndex).get regs)
          hdata
      _ = (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
          concrete.1 := rfl
      _ = RoundState.historyBit
          (RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x) source.kaliskiSteps
            source.paddingSteps) := hhConcrete
      _ = RoundState.historyBit source :=
        congrArg RoundState.historyBit hsource
  exact routedPersistentBoundary_active_nonzero_of_raw tail counterWidth
    comparisonIndex roundIndex workIndex source x hinput hsource hcounter
    hactive hvNonzero hfinal hu hv hr hs hh

set_option maxHeartbeats 800000 in
-- The v-even boundary combines the complete concrete route and source-state readout.
/-- The active nonterminating `vEven` route matches the raw source round and
preserves all persistent state outside the selected history slot. -/
lemma routedStepBeforeCleanup_active_vEven_persistentBoundary
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvEven :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d : Registers tail.succ counterWidth :=
    dataRegisters tail counterWidth x
  let concrete : RegistersWithFullRoundWork tail.succ counterWidth :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex
      (((d, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x = (((concrete, true), false), x.2) := by
    dsimp [concrete]
    exact controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get d = true := by
    simpa [d, RegisterBits.activeBit_get] using hactive
  apply routedPersistentBoundary_active_nonzero_of_concrete tail counterWidth
    comparisonIndex roundIndex workIndex source x hinput hsource hcounter
    hactive hvNonzero hfinal concrete hroute
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA
        hinput.scratchB hinput.compare hactiveBit huOdd hvEven hvNonzero)
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA
        hinput.scratchB hinput.compare hactiveBit huOdd hvEven hvNonzero)
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA
        hinput.scratchB hinput.compare hactiveBit huOdd hvEven hvNonzero
        (arith.vEven_msb hactive hvNonzero huOdd hvEven)
        (arith.vEven_double hactive hvNonzero huOdd hvEven))
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA
        hinput.scratchB hinput.compare hactiveBit huOdd hvEven hvNonzero)
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_vEven_eq_sourceHistoryBit_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA
        hinput.scratchB hinput.compare hactiveBit hinput.historyFresh huOdd
        hvEven hvNonzero)

set_option maxHeartbeats 800000 in
-- The u-greater boundary combines the carried odd route and all persistent readouts.
/-- The active odd `uGreater` route matches the raw source round and preserves
all persistent state outside the selected history slot. -/
lemma routedStepBeforeCleanup_active_uGreater_persistentBoundary
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvOdd :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = true)
    (hlt : (dataRegisters tail counterWidth x).v.val <
      (dataRegisters tail counterWidth x).u.val)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d : Registers tail.succ counterWidth :=
    dataRegisters tail counterWidth x
  let concrete : RegistersWithFullRoundWork tail.succ counterWidth :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex
      (((d, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x = (((concrete, true), false), x.2) := by
    dsimp [concrete]
    exact controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get d = true := by
    simpa [d, RegisterBits.activeBit_get] using hactive
  apply routedPersistentBoundary_active_nonzero_of_concrete tail counterWidth
    comparisonIndex roundIndex workIndex source x hinput hsource hcounter
    hactive hvNonzero hfinal concrete hroute
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hlt
        (arith.uGreater_lsb hactive hvNonzero huOdd hvOdd hlt))
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hlt)
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hlt
        (arith.uGreater_add hactive hvNonzero huOdd hvOdd hlt))
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hlt
        (arith.uGreater_msb hactive hvNonzero huOdd hvOdd hlt)
        (arith.uGreater_double hactive hvNonzero huOdd hvOdd hlt))
  · simpa only [concrete] using
      (
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_uGreater_eq_sourceHistoryBit_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA
        hinput.scratchB hinput.compare hfinal hactiveBit hinput.historyFresh
        huOdd hvOdd hlt)

set_option maxHeartbeats 800000 in
-- The v-less-or-equal boundary combines the carried odd route and persistent readouts.
/-- The active odd `vLe` route matches the raw source round and preserves all
persistent state outside the selected history slot. -/
lemma routedStepBeforeCleanup_active_vLe_persistentBoundary
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hactive : (dataRegisters tail counterWidth x).active = true)
    (hvNonzero : (dataRegisters tail counterWidth x).v.val ≠ 0)
    (huOdd :
      (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) = true)
    (hvOdd :
      (dataRegisters tail counterWidth x).v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ (dataRegisters tail counterWidth x).v.val <
      (dataRegisters tail counterWidth x).u.val)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    RoutedPersistentBoundary tail counterWidth roundIndex source x
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x) := by
  let d : Registers tail.succ counterWidth :=
    dataRegisters tail counterWidth x
  let concrete : RegistersWithFullRoundWork tail.succ counterWidth :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex roundIndex workIndex
      (((d, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  have hroute :
      routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x = (((concrete, true), false), x.2) := by
    dsimp [concrete]
    exact controlledActiveOnlyStructuredStep_after_latch_padding_active_eq
      tail counterWidth comparisonIndex roundIndex workIndex x
      hinput.toPhysicalWorkspaceClean hactive
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get d = true := by
    simpa [d, RegisterBits.activeBit_get] using hactive
  apply routedPersistentBoundary_active_nonzero_of_concrete tail counterWidth
    comparisonIndex roundIndex workIndex source x hinput hsource hcounter
    hactive hvNonzero hfinal concrete hroute
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hnlt)
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hnlt
        (arith.vLe_lsb hactive hvNonzero huOdd hvOdd hnlt))
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hnlt
        (arith.vLe_msb hactive hvNonzero huOdd hvOdd hnlt)
        (arith.vLe_double hactive hvNonzero huOdd hvOdd hnlt))
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA hinput.compare
        hfinal hactiveBit huOdd hvOdd hnlt
        (arith.vLe_add hactive hvNonzero huOdd hvOdd hnlt))
  · simpa only [concrete] using
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_history_vLe_eq_sourceHistoryBit_clean
        tail counterWidth comparisonIndex roundIndex workIndex
        source.kaliskiSteps source.paddingSteps d hinput.scratchA
        hinput.scratchB hinput.compare hfinal hactiveBit hinput.historyFresh
        huOdd hvOdd hnlt)


lemma workingPathBit_routeHistoryBit_wire_ne
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (workingPathBit tail counterWidth).wire ≠
      (routeHistoryBit tail counterWidth roundIndex).wire :=
  prodLeftBit_prodRightBit_wire_ne
    (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
    (wordEncoding (2 * tail.succ))
    (fullRoundPathControlWorkPathBit tail counterWidth)
    (BinaryLabelEncoding.finIdentityBit (2 * tail.succ) roundIndex)

lemma routeHistoryBit_routeHistoryBit_wire_ne
    (tail counterWidth : Nat)
    (left right : Fin (2 * tail.succ)) (h : left ≠ right) :
    (routeHistoryBit tail counterWidth left).wire ≠
      (routeHistoryBit tail counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [routeHistoryBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire, wordEncoding,
    BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit] using hval

end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
