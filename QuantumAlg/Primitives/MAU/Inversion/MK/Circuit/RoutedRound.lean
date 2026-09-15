/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Fold
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.RouteWorkspace
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.ControlledRoute
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Semantics
import all QuantumAlg.Primitives.MAU.Inversion.MK.Termination
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Termination

/-!
# Fixed-round spill and structured boundary semantics
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit

noncomputable section

open MK
open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD
/-! ## Route-history spill and path reset -/

/-- Store the current working path in the clean route slot. -/
def spillWorkingPathGate (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    EncodedBit.GateSpec (encoding tail.succ counterWidth) :=
  EncodedBit.GateSpec.cnot
    (workingPathBit tail counterWidth)
    (routeHistoryBit tail counterWidth roundIndex)
    (workingPathBit_routeHistoryBit_wire_ne
      tail counterWidth roundIndex)

/-- Singleton gate list that spills the working path into one route slot. -/
def spillWorkingPathGates (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  [spillWorkingPathGate tail counterWidth roundIndex]

/-- Semantic action of spilling the working path into one route slot. -/
def spillWorkingPathStep (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (spillWorkingPathGates tail counterWidth roundIndex)

/-- Base-gate program that spills the working path into one route slot. -/
def spillWorkingPathProgram (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (spillWorkingPathGates tail counterWidth roundIndex)

theorem spillWorkingPath_realizes (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (spillWorkingPathProgram tail counterWidth roundIndex)
      (spillWorkingPathStep tail counterWidth roundIndex) :=
  EncodedBit.GateSpec.realizesList
    (spillWorkingPathGates tail counterWidth roundIndex)

/-- Reset the working path from the just-written route slot. -/
def resetWorkingPathGate (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    EncodedBit.GateSpec (encoding tail.succ counterWidth) :=
  EncodedBit.GateSpec.cnot
    (routeHistoryBit tail counterWidth roundIndex)
    (workingPathBit tail counterWidth)
    (workingPathBit_routeHistoryBit_wire_ne
      tail counterWidth roundIndex).symm

/-- Singleton gate list that resets the working path from its route slot. -/
def resetWorkingPathGates (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  [resetWorkingPathGate tail counterWidth roundIndex]

/-- Semantic action of resetting the working path from its route slot. -/
def resetWorkingPathStep (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (resetWorkingPathGates tail counterWidth roundIndex)

/-- Base-gate program that resets the working path from its route slot. -/
def resetWorkingPathProgram (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (resetWorkingPathGates tail counterWidth roundIndex)

theorem resetWorkingPath_realizes (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (resetWorkingPathProgram tail counterWidth roundIndex)
      (resetWorkingPathStep tail counterWidth roundIndex) :=
  EncodedBit.GateSpec.realizesList
    (resetWorkingPathGates tail counterWidth roundIndex)

theorem spillWorkingPathStep_get_path
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (workingPathBit tail counterWidth).get
        (spillWorkingPathStep tail counterWidth roundIndex x) =
      (workingPathBit tail counterWidth).get x := by
  change (workingPathBit tail counterWidth).get
      (EncodedBit.cnotStep
        (workingPathBit tail counterWidth)
        (routeHistoryBit tail counterWidth roundIndex) x) = _
  exact EncodedBit.cnotStep_get_of_target_ne
    (workingPathBit tail counterWidth)
    (routeHistoryBit tail counterWidth roundIndex)
    (workingPathBit tail counterWidth)
    (workingPathBit_routeHistoryBit_wire_ne
      tail counterWidth roundIndex).symm x

theorem spillWorkingPathStep_get_route
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth roundIndex).get
        (spillWorkingPathStep tail counterWidth roundIndex x) =
      ((routeHistoryBit tail counterWidth roundIndex).get x ^^
        (workingPathBit tail counterWidth).get x) := by
  change (routeHistoryBit tail counterWidth roundIndex).get
      (EncodedBit.cnotStep
        (workingPathBit tail counterWidth)
        (routeHistoryBit tail counterWidth roundIndex) x) = _
  exact EncodedBit.cnotStep_get_target
    (workingPathBit tail counterWidth)
    (routeHistoryBit tail counterWidth roundIndex) x

theorem spillWorkingPathStep_get_other_route
    (tail counterWidth : Nat)
    (roundIndex otherIndex : Fin (2 * tail.succ))
    (hne : roundIndex ≠ otherIndex)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth otherIndex).get
        (spillWorkingPathStep tail counterWidth roundIndex x) =
      (routeHistoryBit tail counterWidth otherIndex).get x := by
  change (routeHistoryBit tail counterWidth otherIndex).get
      (EncodedBit.cnotStep
        (workingPathBit tail counterWidth)
        (routeHistoryBit tail counterWidth roundIndex) x) = _
  exact EncodedBit.cnotStep_get_of_target_ne
    (workingPathBit tail counterWidth)
    (routeHistoryBit tail counterWidth roundIndex)
    (routeHistoryBit tail counterWidth otherIndex)
    (routeHistoryBit_routeHistoryBit_wire_ne
      tail counterWidth roundIndex otherIndex hne) x

theorem resetWorkingPathStep_get_path
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (workingPathBit tail counterWidth).get
        (resetWorkingPathStep tail counterWidth roundIndex x) =
      ((workingPathBit tail counterWidth).get x ^^
        (routeHistoryBit tail counterWidth roundIndex).get x) := by
  change (workingPathBit tail counterWidth).get
      (EncodedBit.cnotStep
        (routeHistoryBit tail counterWidth roundIndex)
        (workingPathBit tail counterWidth) x) = _
  exact EncodedBit.cnotStep_get_target
    (routeHistoryBit tail counterWidth roundIndex)
    (workingPathBit tail counterWidth) x

/-- Reset writes only the path wire, so this covers both the selected route
bit and every other route bit. -/
theorem resetWorkingPathStep_get_route
    (tail counterWidth : Nat)
    (roundIndex observedIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth observedIndex).get
        (resetWorkingPathStep tail counterWidth roundIndex x) =
      (routeHistoryBit tail counterWidth observedIndex).get x := by
  change (routeHistoryBit tail counterWidth observedIndex).get
      (EncodedBit.cnotStep
        (routeHistoryBit tail counterWidth roundIndex)
        (workingPathBit tail counterWidth) x) = _
  exact EncodedBit.cnotStep_get_of_target_ne
    (routeHistoryBit tail counterWidth roundIndex)
    (workingPathBit tail counterWidth)
    (routeHistoryBit tail counterWidth observedIndex)
    (workingPathBit_routeHistoryBit_wire_ne
      tail counterWidth observedIndex) x

theorem spillResetWorkingPathStep_get_selected_route_of_clean
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hclean :
      (routeHistoryBit tail counterWidth roundIndex).get x = false) :
    (routeHistoryBit tail counterWidth roundIndex).get
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex x)) =
      (workingPathBit tail counterWidth).get x := by
  rw [resetWorkingPathStep_get_route,
    spillWorkingPathStep_get_route, hclean]
  simp

theorem spillResetWorkingPathStep_get_path_of_clean
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hclean :
      (routeHistoryBit tail counterWidth roundIndex).get x = false) :
    (workingPathBit tail counterWidth).get
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex x)) = false := by
  rw [resetWorkingPathStep_get_path,
    spillWorkingPathStep_get_path,
    spillWorkingPathStep_get_route, hclean]
  cases (workingPathBit tail counterWidth).get x <;> rfl

theorem spillResetWorkingPathStep_get_other_route
    (tail counterWidth : Nat)
    (roundIndex otherIndex : Fin (2 * tail.succ))
    (hne : roundIndex ≠ otherIndex)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth otherIndex).get
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex x)) =
      (routeHistoryBit tail counterWidth otherIndex).get x := by
  rw [resetWorkingPathStep_get_route,
    spillWorkingPathStep_get_other_route tail counterWidth
      roundIndex otherIndex hne]

private structure FullRoundControlSnapshot (tail counterWidth : Nat) where
  fullRound : RegistersWithFullRoundWork tail.succ counterWidth
  control : Bool

private def fullRoundControlSnapshot (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    FullRoundControlSnapshot tail counterWidth where
  fullRound := x.1.1.1
  control := x.1.2

private theorem spillWorkingPathStep_fullRoundControlSnapshot
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    fullRoundControlSnapshot tail counterWidth
        (spillWorkingPathStep tail counterWidth roundIndex x) =
      fullRoundControlSnapshot tail counterWidth x := by
  unfold spillWorkingPathStep
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [spillWorkingPathGates, List.mem_singleton] at hgate
  subst gate
  intro y
  rfl

private theorem resetWorkingPathStep_fullRoundControlSnapshot
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    fullRoundControlSnapshot tail counterWidth
        (resetWorkingPathStep tail counterWidth roundIndex x) =
      fullRoundControlSnapshot tail counterWidth x := by
  unfold resetWorkingPathStep
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [resetWorkingPathGates, List.mem_singleton] at hgate
  subst gate
  intro y
  rfl

theorem spillWorkingPathStep_get_fullRound
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (spillWorkingPathStep tail counterWidth roundIndex x).1.1.1 =
      x.1.1.1 := by
  exact congrArg FullRoundControlSnapshot.fullRound
    (spillWorkingPathStep_fullRoundControlSnapshot
      tail counterWidth roundIndex x)

theorem resetWorkingPathStep_get_fullRound
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (resetWorkingPathStep tail counterWidth roundIndex x).1.1.1 =
      x.1.1.1 := by
  exact congrArg FullRoundControlSnapshot.fullRound
    (resetWorkingPathStep_fullRoundControlSnapshot
      tail counterWidth roundIndex x)

theorem spillWorkingPathStep_get_control
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (spillWorkingPathStep tail counterWidth roundIndex x).1.2 = x.1.2 := by
  exact congrArg FullRoundControlSnapshot.control
    (spillWorkingPathStep_fullRoundControlSnapshot
      tail counterWidth roundIndex x)

theorem resetWorkingPathStep_get_control
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (resetWorkingPathStep tail counterWidth roundIndex x).1.2 = x.1.2 := by
  exact congrArg FullRoundControlSnapshot.control
    (resetWorkingPathStep_fullRoundControlSnapshot
      tail counterWidth roundIndex x)

theorem spillResetWorkingPathStep_get_dataRegisters
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    dataRegisters tail counterWidth
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex x)) =
      dataRegisters tail counterWidth x := by
  unfold dataRegisters
  rw [resetWorkingPathStep_get_fullRound,
    spillWorkingPathStep_get_fullRound]

/-- Source-semantic and persistent bookkeeping fields that are not targets of
the residue-cleanup or path spill/reset suffix. -/
private structure PersistentDataSnapshot (tail counterWidth : Nat) where
  u : Word tail.succ
  v : Word tail.succ
  rCoeff : Word (tail.succ + 1)
  sCoeff : Word (tail.succ + 1)
  active : Bool
  counter : Word counterWidth
  history : Word (2 * tail.succ)

private def persistentDataSnapshot (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    PersistentDataSnapshot tail counterWidth where
  u := (dataRegisters tail counterWidth x).u
  v := (dataRegisters tail counterWidth x).v
  rCoeff := (dataRegisters tail counterWidth x).rCoeff
  sCoeff := (dataRegisters tail counterWidth x).sCoeff
  active := (dataRegisters tail counterWidth x).active
  counter := (dataRegisters tail counterWidth x).counter
  history := (dataRegisters tail counterWidth x).history

private theorem branchResidueCleanupStep_persistentDataSnapshot
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    persistentDataSnapshot tail counterWidth
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      persistentDataSnapshot tail counterWidth x := by
  unfold branchResidueCleanupStep
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [branchResidueCleanupGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro y
    rfl

private theorem spillWorkingPathStep_persistentDataSnapshot
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    persistentDataSnapshot tail counterWidth
        (spillWorkingPathStep tail counterWidth roundIndex x) =
      persistentDataSnapshot tail counterWidth x := by
  unfold spillWorkingPathStep
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [spillWorkingPathGates, List.mem_singleton] at hgate
  subst gate
  intro y
  rfl

private theorem resetWorkingPathStep_persistentDataSnapshot
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    persistentDataSnapshot tail counterWidth
        (resetWorkingPathStep tail counterWidth roundIndex x) =
      persistentDataSnapshot tail counterWidth x := by
  unfold resetWorkingPathStep
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [resetWorkingPathGates, List.mem_singleton] at hgate
  subst gate
  intro y
  rfl

private theorem cleanupSpillReset_persistentDataSnapshot
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    persistentDataSnapshot tail counterWidth
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex
            (branchResidueCleanupStep tail counterWidth roundIndex x))) =
      persistentDataSnapshot tail counterWidth x := by
  rw [resetWorkingPathStep_persistentDataSnapshot,
    spillWorkingPathStep_persistentDataSnapshot,
    branchResidueCleanupStep_persistentDataSnapshot]

/-- The physical suffix preserves the raw source-state projection for any
explicit source step counters. -/
theorem cleanupSpillReset_fromRegisters
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    RoundState.fromRegisters tail.succ counterWidth
        (dataRegisters tail counterWidth
          (resetWorkingPathStep tail counterWidth roundIndex
            (spillWorkingPathStep tail counterWidth roundIndex
              (branchResidueCleanupStep tail counterWidth roundIndex x))))
        kaliskiSteps paddingSteps =
      RoundState.fromRegisters tail.succ counterWidth
        (dataRegisters tail counterWidth x) kaliskiSteps paddingSteps := by
  have hs := cleanupSpillReset_persistentDataSnapshot
    tail counterWidth roundIndex x
  have hu := congrArg PersistentDataSnapshot.u hs
  have hv := congrArg PersistentDataSnapshot.v hs
  have hr := congrArg PersistentDataSnapshot.rCoeff hs
  have hsc := congrArg PersistentDataSnapshot.sCoeff hs
  have ha := congrArg PersistentDataSnapshot.active hs
  dsimp only [persistentDataSnapshot] at hu hv hr hsc ha
  unfold RoundState.fromRegisters
  rw [hu, hv, hr, hsc, ha]

theorem cleanupSpillReset_get_counter
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (dataRegisters tail counterWidth
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex
            (branchResidueCleanupStep tail counterWidth roundIndex x)))).counter =
      (dataRegisters tail counterWidth x).counter := by
  have hs := cleanupSpillReset_persistentDataSnapshot
    tail counterWidth roundIndex x
  simpa [persistentDataSnapshot] using
    congrArg PersistentDataSnapshot.counter hs

theorem cleanupSpillReset_get_history
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (dataRegisters tail counterWidth
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex
            (branchResidueCleanupStep tail counterWidth roundIndex x)))).history =
      (dataRegisters tail counterWidth x).history := by
  have hs := cleanupSpillReset_persistentDataSnapshot
    tail counterWidth roundIndex x
  simpa [persistentDataSnapshot] using
    congrArg PersistentDataSnapshot.history hs

theorem cleanupSpillReset_get_selected_route_of_clean
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hclean :
      (routeHistoryBit tail counterWidth roundIndex).get x = false) :
    (routeHistoryBit tail counterWidth roundIndex).get
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex
            (branchResidueCleanupStep tail counterWidth roundIndex x))) =
      (workingPathBit tail counterWidth).get x := by
  rw [spillResetWorkingPathStep_get_selected_route_of_clean]
  · exact branchResidueCleanupStep_get_path
      tail counterWidth roundIndex x
  · rw [branchResidueCleanupStep_get_route]
    exact hclean

theorem cleanupSpillReset_get_other_route
    (tail counterWidth : Nat)
    (roundIndex observed : Fin (2 * tail.succ))
    (hne : roundIndex ≠ observed)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth observed).get
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex
            (branchResidueCleanupStep tail counterWidth roundIndex x))) =
      (routeHistoryBit tail counterWidth observed).get x := by
  rw [spillResetWorkingPathStep_get_other_route
    tail counterWidth roundIndex observed hne]
  exact branchResidueCleanupStep_get_route
    tail counterWidth roundIndex observed x

/-- Residue cleanup followed by the fixed spill/reset suffix restores the
complete physical workspace.  The proof reconstructs every work product from
the raw physical endpoint; it does not pass through a masked readout. -/
theorem cleanupSpillReset_physicalWorkspaceClean
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (cert : BranchResidueCertificate tail counterWidth roundIndex x)
    (hreusable : ReusableWorkspaceClean tail counterWidth x)
    (hrouteFresh :
      (routeHistoryBit tail counterWidth roundIndex).get x = false) :
    PhysicalWorkspaceClean tail counterWidth
      (resetWorkingPathStep tail counterWidth roundIndex
        (spillWorkingPathStep tail counterWidth roundIndex
          (branchResidueCleanupStep tail counterWidth roundIndex x))) := by
  let cleaned := branchResidueCleanupStep tail counterWidth roundIndex x
  let after :=
    resetWorkingPathStep tail counterWidth roundIndex
      (spillWorkingPathStep tail counterWidth roundIndex cleaned)
  have hendpoint : BranchResidueCleanEndpoint tail counterWidth cleaned := by
    exact branchResidueCleanupStep_cleanEndpoint
      tail counterWidth roundIndex x cert
  have hwork : ReusableWorkspaceClean tail counterWidth cleaned := by
    exact branchResidueCleanupStep_reusableWorkspaceClean
      tail counterWidth roundIndex x hreusable
  have hrouteCleaned :
      (routeHistoryBit tail counterWidth roundIndex).get cleaned = false := by
    rw [branchResidueCleanupStep_get_route]
    exact hrouteFresh
  have hcounter :
      cleaned.1.1.1.2 = cleanCounterIncrementWork counterWidth := by
    apply Prod.ext
    · exact hwork.counterSource
    · apply Prod.ext
      · change cleaned.1.1.1.2.2.1 = false
        have hcarry := hendpoint.counterCarry
        change cleaned.1.1.1.2.2.1 = false at hcarry
        exact hcarry
      · exact hwork.counterCarryWork
  have hfullRound :
      cleaned.1.1.1 =
        (((dataRegisters tail counterWidth cleaned,
            cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact hwork.comparisonWork
      · exact hwork.coefficientWork
    · exact hcounter
  have hafterFullRound : after.1.1.1 = cleaned.1.1.1 := by
    dsimp [after]
    rw [resetWorkingPathStep_get_fullRound,
      spillWorkingPathStep_get_fullRound]
  have hafterData :
      dataRegisters tail counterWidth after =
        dataRegisters tail counterWidth cleaned := by
    dsimp [after]
    exact spillResetWorkingPathStep_get_dataRegisters
      tail counterWidth roundIndex cleaned
  have hafterPath : (workingPathBit tail counterWidth).get after = false := by
    dsimp [after]
    exact spillResetWorkingPathStep_get_path_of_clean
      tail counterWidth roundIndex cleaned hrouteCleaned
  have hafterControl : after.1.2 = false := by
    dsimp [after]
    rw [resetWorkingPathStep_get_control,
      spillWorkingPathStep_get_control]
    exact hwork.control
  change PhysicalWorkspaceClean tail counterWidth after
  constructor
  · unfold withCleanFullRoundPathControlWork withCleanFullRoundPathWork
    apply Prod.ext
    · apply Prod.ext
      · rw [hafterFullRound, hfullRound, hafterData]
      · change (workingPathBit tail counterWidth).get after = false
        exact hafterPath
    · exact hafterControl
  · have hs := hendpoint.scratchA
    change (dataRegisters tail counterWidth cleaned).scratchA = false at hs
    exact (congrArg Registers.scratchA hafterData).trans hs
  · have hs := hendpoint.scratchB
    change (dataRegisters tail counterWidth cleaned).scratchB = false at hs
    exact (congrArg Registers.scratchB hafterData).trans hs
  · have hc := hendpoint.compare
    change (dataRegisters tail counterWidth cleaned).compare = false at hc
    exact (congrArg Registers.compare hafterData).trans hc

/-- Structured six-stage action of one fixed round on the clean-control
slice.  The gate ledger below realizes this function on every state satisfying
that slice condition. -/
def roundStructuredStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  fun x =>
    resetWorkingPathStep tail counterWidth roundIndex
      (spillWorkingPathStep tail counterWidth roundIndex
        (branchResidueCleanupStep tail counterWidth roundIndex
          (controlledActiveOnlyStructuredStep tail counterWidth
            comparisonIndex roundIndex workIndex
            (inactivePaddingStep tail counterWidth
              (originalActiveLatchStep tail counterWidth x)))))

/-- Once the routed state supplies its physical residue certificate and the
remaining reusable-work boundary, the fixed cleanup/spill/reset suffix reaches
the complete round workspace boundary. -/
theorem roundStructuredStep_physicalWorkspaceClean_of_routed
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hcert : BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x))
    (hreusable : ReusableWorkspaceClean tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x)) :
    PhysicalWorkspaceClean tail counterWidth
      (roundStructuredStep tail counterWidth comparisonIndex workIndex
        roundIndex x) := by
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  have hrouteFresh :
      (routeHistoryBit tail counterWidth roundIndex).get routed = false := by
    dsimp [routed]
    rw [routedStepBeforeCleanup_get_route]
    exact hinput.routeFresh
  change PhysicalWorkspaceClean tail counterWidth
    (resetWorkingPathStep tail counterWidth roundIndex
      (spillWorkingPathStep tail counterWidth roundIndex
        (branchResidueCleanupStep tail counterWidth roundIndex routed)))
  exact cleanupSpillReset_physicalWorkspaceClean
    tail counterWidth roundIndex routed hcert hreusable hrouteFresh

theorem roundStructuredStep_fromRegisters_eq_routed
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    RoundState.fromRegisters tail.succ counterWidth
        (dataRegisters tail counterWidth
          (roundStructuredStep tail counterWidth comparisonIndex workIndex
            roundIndex x)) kaliskiSteps paddingSteps =
      RoundState.fromRegisters tail.succ counterWidth
        (dataRegisters tail counterWidth
          (routedStepBeforeCleanup tail counterWidth comparisonIndex
            roundIndex workIndex x)) kaliskiSteps paddingSteps := by
  change RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth
        (resetWorkingPathStep tail counterWidth roundIndex
          (spillWorkingPathStep tail counterWidth roundIndex
            (branchResidueCleanupStep tail counterWidth roundIndex
              (routedStepBeforeCleanup tail counterWidth comparisonIndex
                roundIndex workIndex x))))) kaliskiSteps paddingSteps = _
  exact cleanupSpillReset_fromRegisters tail counterWidth kaliskiSteps
    paddingSteps roundIndex
    (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x)

theorem roundStructuredStep_get_counter_eq_routed
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (dataRegisters tail counterWidth
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x)).counter =
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).counter := by
  change (dataRegisters tail counterWidth
      (resetWorkingPathStep tail counterWidth roundIndex
        (spillWorkingPathStep tail counterWidth roundIndex
          (branchResidueCleanupStep tail counterWidth roundIndex
            (routedStepBeforeCleanup tail counterWidth comparisonIndex
              roundIndex workIndex x))))).counter = _
  exact cleanupSpillReset_get_counter tail counterWidth roundIndex
    (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x)

theorem roundStructuredStep_get_history_eq_routed
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (dataRegisters tail counterWidth
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x)).history =
      (dataRegisters tail counterWidth
        (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
          workIndex x)).history := by
  change (dataRegisters tail counterWidth
      (resetWorkingPathStep tail counterWidth roundIndex
        (spillWorkingPathStep tail counterWidth roundIndex
          (branchResidueCleanupStep tail counterWidth roundIndex
            (routedStepBeforeCleanup tail counterWidth comparisonIndex
              roundIndex workIndex x))))).history = _
  exact cleanupSpillReset_get_history tail counterWidth roundIndex
    (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x)

theorem roundStructuredStep_get_selected_route
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x) :
    (routeHistoryBit tail counterWidth roundIndex).get
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x) =
      (dataRegisters tail counterWidth x).active := by
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  have hrouteFresh :
      (routeHistoryBit tail counterWidth roundIndex).get routed = false := by
    dsimp [routed]
    rw [routedStepBeforeCleanup_get_route]
    exact hinput.routeFresh
  calc
    (routeHistoryBit tail counterWidth roundIndex).get
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x) =
        (workingPathBit tail counterWidth).get routed := by
          change (routeHistoryBit tail counterWidth roundIndex).get
            (resetWorkingPathStep tail counterWidth roundIndex
              (spillWorkingPathStep tail counterWidth roundIndex
                (branchResidueCleanupStep tail counterWidth roundIndex
                  routed))) = _
          exact cleanupSpillReset_get_selected_route_of_clean
            tail counterWidth roundIndex routed hrouteFresh
    _ = (dataRegisters tail counterWidth x).active :=
      routedStepBeforeCleanup_get_path_eq_originalActive
        tail counterWidth comparisonIndex roundIndex workIndex x
        hinput.toPhysicalWorkspaceClean

theorem roundStructuredStep_get_other_route
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex observed : Fin (2 * tail.succ))
    (hne : roundIndex ≠ observed)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth observed).get
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x) =
      (routeHistoryBit tail counterWidth observed).get x := by
  calc
    (routeHistoryBit tail counterWidth observed).get
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x) =
        (routeHistoryBit tail counterWidth observed).get
          (routedStepBeforeCleanup tail counterWidth comparisonIndex
            roundIndex workIndex x) := by
              change (routeHistoryBit tail counterWidth observed).get
                (resetWorkingPathStep tail counterWidth roundIndex
                  (spillWorkingPathStep tail counterWidth roundIndex
                    (branchResidueCleanupStep tail counterWidth roundIndex
                      (routedStepBeforeCleanup tail counterWidth
                        comparisonIndex roundIndex workIndex x)))) = _
              exact cleanupSpillReset_get_other_route
                tail counterWidth roundIndex observed hne _
    _ = (routeHistoryBit tail counterWidth observed).get x :=
      routedStepBeforeCleanup_get_route tail counterWidth comparisonIndex
        roundIndex observed workIndex x

/-- Lift the exact routed source boundary through the common physical
cleanup/spill/reset suffix.  This is the only theorem that assembles the
physical and semantic halves of a fixed round. -/
theorem roundStructuredStep_cleanBoundary_of_routed
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource :
      RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x)
          source.kaliskiSteps source.paddingSteps = source)
    (hcert : BranchResidueCertificate tail counterWidth roundIndex
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x))
    (hreusable : ReusableWorkspaceClean tail counterWidth
      (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x))
    (hpersistent : RoutedPersistentBoundary tail counterWidth roundIndex source
      x (routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
        workIndex x)) :
    RoundCleanBoundary tail counterWidth roundIndex source x
      (roundStructuredStep tail counterWidth comparisonIndex workIndex
        roundIndex x) := by
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  refine
    { toPhysicalWorkspaceClean :=
        roundStructuredStep_physicalWorkspaceClean_of_routed
          tail counterWidth comparisonIndex workIndex roundIndex x hinput
          hcert hreusable
      sourceAfter := ?_
      counterAfter := ?_
      historyWritten := ?_
      routeWritten := ?_
      historyPreserved := ?_
      routePreserved := ?_ }
  · rw [roundStructuredStep_fromRegisters_eq_routed
      tail counterWidth (RoundState.round source).kaliskiSteps
      (RoundState.round source).paddingSteps comparisonIndex workIndex
      roundIndex x]
    exact hpersistent.sourceAfter
  · have hcounter := roundStructuredStep_get_counter_eq_routed
      tail counterWidth comparisonIndex workIndex roundIndex x
    rw [hcounter]
    exact hpersistent.counterAfter
  · have hhistory := roundStructuredStep_get_history_eq_routed
      tail counterWidth comparisonIndex workIndex roundIndex x
    change
      (dataRegisters tail counterWidth
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x)).history.val.testBit
          (WireAddress.bitIndex roundIndex).val = _
    rw [hhistory]
    simpa [RegisterBits.historyBit_get] using hpersistent.historyWritten
  · rw [roundStructuredStep_get_selected_route
      tail counterWidth comparisonIndex workIndex roundIndex x hinput]
    have hactive := congrArg RoundState.active hsource
    simpa [RoundState.fromRegisters] using hactive
  · intro observed hne
    have hhistory := roundStructuredStep_get_history_eq_routed
      tail counterWidth comparisonIndex workIndex roundIndex x
    change
      (dataRegisters tail counterWidth
        (roundStructuredStep tail counterWidth comparisonIndex workIndex
          roundIndex x)).history.val.testBit
          (WireAddress.bitIndex observed).val = _
    rw [hhistory]
    simpa [RegisterBits.historyBit_get] using
      hpersistent.historyPreserved observed hne
  · intro observed hne
    exact roundStructuredStep_get_other_route
      tail counterWidth comparisonIndex workIndex roundIndex observed hne x

end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
