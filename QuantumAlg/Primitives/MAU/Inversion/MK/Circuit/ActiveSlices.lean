/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Fold
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.RouteWorkspace
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Semantics
import all QuantumAlg.Primitives.MAU.Inversion.MK.Termination
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Termination

/-!
# Fixed-round source slices over route history
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
/-! ## Existing source-round slices lifted over route history -/

/-- Lift the original-active latch action over the route-history word. -/
def originalActiveLatchStep (tail counterWidth : Nat) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  fun x =>
    (fullRoundPathControlWorkOriginalActiveLatchStep
      tail counterWidth x.1, x.2)

/-- Gate list for the original-active latch after lifting over control work
and route history. -/
def originalActiveLatchGates (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  ((fullRoundPathWorkOriginalActiveLatchGates tail counterWidth).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodLeft (wordEncoding (2 * tail.succ)))

/-- The lifted original-active latch list has exactly the named route-history
action. -/
lemma originalActiveLatchGates_stepList_eq
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (originalActiveLatchGates tail counterWidth) x =
      originalActiveLatchStep tail counterWidth x := by
  unfold originalActiveLatchGates originalActiveLatchStep
  let baseGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)) :=
    fullRoundPathWorkOriginalActiveLatchGates tail counterWidth
  let controlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    baseGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    EncodedBit.GateSpec.stepList
        (controlGates.map
          (EncodedBit.GateSpec.prodLeft
            (wordEncoding (2 * tail.succ)))) x = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  change
    (EncodedBit.GateSpec.stepList controlGates x.1, x.2) = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rfl

/-- Base-gate program for the lifted original-active latch. -/
def originalActiveLatchProgram (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (originalActiveLatchGates tail counterWidth)

lemma originalActiveLatch_realizes (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (originalActiveLatchProgram tail counterWidth) environment
      (originalActiveLatchStep tail counterWidth) := by
  exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (originalActiveLatchGates tail counterWidth)
    (originalActiveLatchGates_stepList_eq tail counterWidth)

/-- The directly compiled original-active gate list realizes the same named
route-history action as the structural lifted circuit. -/
lemma originalActiveLatchGates_realizes (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (originalActiveLatchGates tail counterWidth)) environment
      (originalActiveLatchStep tail counterWidth) :=
  originalActiveLatch_realizes tail counterWidth

/-- The structural original-active circuit has exactly its lifted primitive
event trace. -/
lemma originalActiveLatchProgram_eventTrace (tail counterWidth : Nat) :
    (originalActiveLatchProgram tail counterWidth).eventTrace =
      (originalActiveLatchGates tail counterWidth).map
        (EncodedBit.GateSpec.event .empty) := by
  exact EncodedBit.GateSpec.programList_eventTrace
    (QubitLayout.canonical _) .empty
    (originalActiveLatchGates tail counterWidth)

/-- Lift the inactive-padding action over the route-history word. -/
def inactivePaddingStep (tail counterWidth : Nat) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  fun x =>
    (fullRoundPathControlWorkActiveFalseInactivePaddingStep
      tail counterWidth x.1, x.2)

/-- Gate list for inactive padding after inserting coefficient work and
lifting over path, control, and route-history fields. -/
def inactivePaddingGates (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  ((((detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth).map
    (EncodedBit.GateSpec.insertMiddle
      (coeffAdderWorkEncoding tail.succ))).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodLeft (wordEncoding (2 * tail.succ)))

lemma event_insertMiddleGateSpec
    {Left Middle Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    (middle : BinaryLabelEncoding Middle)
    (gate : EncodedBit.GateSpec (BinaryLabelEncoding.prod left right)) :
    (EncodedBit.GateSpec.event .empty)
        (EncodedBit.GateSpec.insertMiddle middle gate) =
      (EncodedBit.GateSpec.event .empty) gate := by
  cases gate <;> rfl

/-- The lifted inactive-padding list has exactly the named route-history
action. -/
lemma inactivePaddingGates_stepList_eq
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (inactivePaddingGates tail counterWidth) x =
      inactivePaddingStep tail counterWidth x := by
  unfold inactivePaddingGates inactivePaddingStep
  let detectorGates :
      List (EncodedBit.GateSpec
        (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)) :=
    detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth
  let fullRoundGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
    detectorGates.map
      (EncodedBit.GateSpec.insertMiddle
        (coeffAdderWorkEncoding tail.succ))
  let pathGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    fullRoundGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let pathControlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (registersWithFullRoundWorkEncoding tail.succ counterWidth)
            BinaryLabelEncoding.bool)
          BinaryLabelEncoding.bool)) :=
    pathGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    EncodedBit.GateSpec.stepList
        (pathControlGates.map
          (EncodedBit.GateSpec.prodLeft
            (wordEncoding (2 * tail.succ)))) x = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  change
    (EncodedBit.GateSpec.stepList pathControlGates x.1, x.2) = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  change
    ((EncodedBit.GateSpec.stepList pathGates x.1.1, x.1.2), x.2) = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  change
    (((EncodedBit.GateSpec.stepList
        (detectorGates.map
          (EncodedBit.GateSpec.insertMiddle
            (coeffAdderWorkEncoding tail.succ))) x.1.1.1,
      x.1.1.2), x.1.2), x.2) = _
  rw [EncodedBit.GateSpec.stepList_insertMiddle]
  rfl

/-- Base-gate program for the lifted inactive-padding action. -/
def inactivePaddingProgram (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (inactivePaddingGates tail counterWidth)

lemma inactivePadding_realizes (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (inactivePaddingProgram tail counterWidth) environment
      (inactivePaddingStep tail counterWidth) := by
  exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (inactivePaddingGates tail counterWidth)
    (inactivePaddingGates_stepList_eq tail counterWidth)

/-- The directly compiled inactive-padding list realizes the same named
route-history action as the structural lifted circuit. -/
lemma inactivePaddingGates_realizes (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (inactivePaddingGates tail counterWidth)) environment
      (inactivePaddingStep tail counterWidth) :=
  inactivePadding_realizes tail counterWidth

/-- The structural inactive-padding circuit has exactly its lifted primitive
event trace. -/
lemma inactivePaddingProgram_eventTrace (tail counterWidth : Nat) :
    (inactivePaddingProgram tail counterWidth).eventTrace =
      (inactivePaddingGates tail counterWidth).map
        (EncodedBit.GateSpec.event .empty) := by
  exact EncodedBit.GateSpec.programList_eventTrace
    (QubitLayout.canonical _) .empty
    (inactivePaddingGates tail counterWidth)

/-- The comparison-work-backed zero detector lifted over the counter work as
one explicit base-gate list. -/
def detectorCounterVZeroDetectorGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithDetectorCounterWorkEncoding n counterWidth)) :=
  (vZeroDetectorWithComparisonWorkGates n counterWidth).map
    (EncodedBit.GateSpec.prodLeft
      (counterIncrementWorkEncoding counterWidth))

/-- The lifted detector gate list has the same action as the existing
detector/counter step. -/
lemma detectorCounterVZeroDetectorGates_stepList_eq
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (detectorCounterVZeroDetectorGates n counterWidth) x =
      detectorCounterVZeroDetectorStep n counterWidth x := by
  unfold detectorCounterVZeroDetectorGates detectorCounterVZeroDetectorStep
  exact EncodedBit.GateSpec.stepList_prodLeft
    (counterIncrementWorkEncoding counterWidth)
    (vZeroDetectorWithComparisonWorkGates n counterWidth) x

/-- Complete detector-gated terminating route as one explicit base-gate list:
compute the zero detector, run the detector-controlled counter mode, then
uncompute the detector. -/
def detectorGatedTerminatingCounterModeWithWorkGates
    (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)) :=
  detectorCounterVZeroDetectorGates tail.succ counterWidth ++
  detectorCounterControlledTerminatingCounterModeGates tail counterWidth ++
  detectorCounterVZeroDetectorGates tail.succ counterWidth

/-- The explicit detector-gated terminating list realizes the same folded
detector/counter action as the existing actual circuit. -/
lemma detectorGatedTerminatingCounterModeWithWorkGates_stepList_eq
    (tail counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (detectorGatedTerminatingCounterModeWithWorkGates
          tail counterWidth) x =
      detectorGatedTerminatingCounterModeWithWorkStep
        tail counterWidth x := by
  unfold detectorGatedTerminatingCounterModeWithWorkGates
    detectorGatedTerminatingCounterModeWithWorkStep
  rw [EncodedBit.GateSpec.stepList_append]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [detectorCounterVZeroDetectorGates_stepList_eq]
  rw [detectorCounterVZeroDetectorGates_stepList_eq]
  rfl

/-- The terminating detector/counter route transported to the standard
full-round layout by inserting coefficient-adder work between the comparison
and counter-work fields. -/
def fullRoundWorkTerminatingStandardLayoutGates
    (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  (detectorGatedTerminatingCounterModeWithWorkGates
      tail counterWidth).map
    (EncodedBit.GateSpec.insertMiddle
      (coeffAdderWorkEncoding tail.succ))

/-- The inserted-middle terminating list has the standard full-round
terminating action and preserves coefficient-adder work. -/
lemma fullRoundWorkTerminatingStandardLayoutGates_stepList_eq
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (fullRoundWorkTerminatingStandardLayoutGates
          tail counterWidth) x =
      fullRoundWorkTerminatingStep tail counterWidth x := by
  unfold fullRoundWorkTerminatingStandardLayoutGates
  let detectorGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithComparisonWorkEncoding tail.succ counterWidth)
          (counterIncrementWorkEncoding counterWidth))) :=
    detectorGatedTerminatingCounterModeWithWorkGates tail counterWidth
  change
    EncodedBit.GateSpec.stepList
        (detectorGates.map
          (EncodedBit.GateSpec.insertMiddle
            (coeffAdderWorkEncoding tail.succ))) x = _
  have hdetector :=
    detectorGatedTerminatingCounterModeWithWorkGates_stepList_eq
      tail counterWidth (x.1.1, x.2)
  change
    EncodedBit.GateSpec.stepList detectorGates (x.1.1, x.2) =
      detectorGatedTerminatingCounterModeWithWorkStep
        tail counterWidth (x.1.1, x.2) at hdetector
  rw [EncodedBit.GateSpec.stepList_insertMiddle]
  rw [hdetector]
  exact fullRoundWorkTerminatingStandardLayoutStep_eq tail counterWidth x

/-- Complete active-only route as one explicit base-gate list: the terminating
prefix followed by the active odd-odd latch and selected/compare-carried
dispatch. -/
def fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  fullRoundWorkTerminatingStandardLayoutGates tail counterWidth ++
  fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
    tail counterWidth comparisonIndex historyIndex workIndex

/-- The explicit complete active-only list realizes the existing folded
terminating-prefix-then-dispatch semantic route. -/
lemma fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_stepList_eq
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
          tail counterWidth comparisonIndex historyIndex workIndex) x =
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex x := by
  unfold fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
  rw [EncodedBit.GateSpec.stepList_append]
  rw [fullRoundWorkTerminatingStandardLayoutGates_stepList_eq]
  rfl

/-- Whole active-only round lifted over path, clean control work, and route history. -/
def liftedActiveOnlyStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  fun x =>
    (liftFullRoundWorkStepToPathControlWork tail.succ counterWidth
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex) x.1,
      x.2)

/-- The complete active-only base-gate list lifted over path, control work, and
route history.  All three fields remain outside the uncontrolled payload. -/
def liftedActiveOnlyGates (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  (((fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodLeft (wordEncoding (2 * tail.succ)))

/-- The triply lifted list has exactly the named lifted active-only action. -/
lemma liftedActiveOnlyGates_stepList_eq
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (liftedActiveOnlyGates tail counterWidth comparisonIndex
          historyIndex workIndex) x =
      liftedActiveOnlyStep tail counterWidth comparisonIndex historyIndex
        workIndex x := by
  unfold liftedActiveOnlyGates liftedActiveOnlyStep
  let baseGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex
  let pathGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    baseGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let pathControlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (registersWithFullRoundWorkEncoding tail.succ counterWidth)
            BinaryLabelEncoding.bool)
          BinaryLabelEncoding.bool)) :=
    pathGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    EncodedBit.GateSpec.stepList
        (pathControlGates.map
          (EncodedBit.GateSpec.prodLeft
            (wordEncoding (2 * tail.succ)))) x = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  change
    (EncodedBit.GateSpec.stepList
        (pathGates.map
          (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)) x.1,
      x.2) = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  change
    ((EncodedBit.GateSpec.stepList
        (baseGates.map
          (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)) x.1.1,
      x.1.2), x.2) = _
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  dsimp [baseGates]
  rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_stepList_eq]
  rfl

/-- Base-gate program for the active-only round lifted over route history. -/
def liftedActiveOnlyProgram (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex)

lemma liftedActiveOnly_realizes (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (liftedActiveOnlyProgram tail counterWidth comparisonIndex
        historyIndex workIndex) environment
      (liftedActiveOnlyStep tail counterWidth comparisonIndex
        historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty
    (liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex)
    (liftedActiveOnlyGates_stepList_eq tail counterWidth comparisonIndex
      historyIndex workIndex)

/-- Lifting the complete active-only route over path, control work, and route
history leaves the path bit untouched. -/
lemma liftedActiveOnlyGates_bitDisjoint_path
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ∀ gate,
      gate ∈ liftedActiveOnlyGates tail counterWidth comparisonIndex
        historyIndex workIndex ->
      EncodedBit.GateSpec.bitDisjoint
        (workingPathBit tail counterWidth) gate := by
  intro gate hgate
  unfold liftedActiveOnlyGates at hgate
  rcases List.mem_map.mp hgate with
    ⟨pathControlGate, hpathControlGate, rfl⟩
  rcases List.mem_map.mp hpathControlGate with
    ⟨pathGate, hpathGate, rfl⟩
  rcases List.mem_map.mp hpathGate with ⟨baseGate, _hbaseGate, rfl⟩
  exact
    gateSpecProdLeft_bitDisjoint_prodLeftBit
      (wordEncoding (2 * tail.succ))
      (fullRoundPathControlWorkPathBit tail counterWidth)
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool baseGate))
      (gateSpecProdLeft_bitDisjoint_prodLeftBit BinaryLabelEncoding.bool
        (fullRoundPathWorkPathBit tail counterWidth)
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool baseGate)
        (gateSpecProdLeft_bitDisjoint_prodRightBit
          BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit baseGate))

/-- The same lifted route also leaves the dedicated clean control-work bit
untouched. -/
lemma liftedActiveOnlyGates_bitDisjoint_controlWork
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ∀ gate,
      gate ∈ liftedActiveOnlyGates tail counterWidth comparisonIndex
        historyIndex workIndex ->
      EncodedBit.GateSpec.bitDisjoint
        (workingControlBit tail counterWidth) gate := by
  intro gate hgate
  unfold liftedActiveOnlyGates at hgate
  rcases List.mem_map.mp hgate with
    ⟨pathControlGate, hpathControlGate, rfl⟩
  rcases List.mem_map.mp hpathControlGate with
    ⟨pathGate, _hpathGate, rfl⟩
  exact
    gateSpecProdLeft_bitDisjoint_prodLeftBit
      (wordEncoding (2 * tail.succ))
      (fullRoundPathControlWorkControlWorkBit tail counterWidth)
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool pathGate)
      (gateSpecProdLeft_bitDisjoint_prodRightBit
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit pathGate)

/-- The shared path and clean control-work wires are physically distinct. -/
lemma workingPathBit_workingControlBit_wire_ne
    (tail counterWidth : Nat) :
    (workingPathBit tail counterWidth).wire ≠
      (workingControlBit tail counterWidth).wire :=
  EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding (2 * tail.succ))
    (fullRoundPathControlWorkPathBit_controlWorkBit_wire_ne
      tail counterWidth)

end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
