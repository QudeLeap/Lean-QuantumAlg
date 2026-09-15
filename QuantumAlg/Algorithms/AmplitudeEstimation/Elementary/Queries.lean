/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Algorithms.AmplitudeEstimation.StagePlacement
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Components.Oracle.AmplitudeAmplification.Circuit
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# The three actual source-query coordinates in elementary amplitude estimation

Preparation and inverse preparation act only on the final original source
wires. Only the source-granted good reflection receives the actual phase
control. Every phase and exceptional work system remains present in the
same full register; no controlled access to preparation is assumed.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

open AmplitudeAmplificationSource

/-- An ordinary preparation query on the source, beside all actual phase/work systems. -/
def preparation {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits (totalQubits t n)) :=
  let phase := UnitaryCircuit.identity (Qubits (phaseWidth t n))
    (List.range (phaseWidth t n)) List.nodup_range
  UnitaryCircuit.tensorQubits phase
    (AmplitudeAmplificationSource.Circuit.preparation (phaseWidth t n) U)
    (qpePhaseSystemLayout (phaseWidth t n) n phase rfl)

/-- An ordinary inverse query on the same original source positions. -/
def inversePreparation {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits (totalQubits t n)) :=
  let phase := UnitaryCircuit.identity (Qubits (phaseWidth t n))
    (List.range (phaseWidth t n)) List.nodup_range
  UnitaryCircuit.tensorQubits phase
    (AmplitudeAmplificationSource.Circuit.inversePreparation (phaseWidth t n) U)
    (qpePhaseSystemLayout (phaseWidth t n) n phase rfl)

/-- The actual good-reflection query is controlled by the original selected phase position. -/
def controlledGoodReflection {n t : Nat} (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (totalQubits t n)) :=
  StagePlacement.stageCall (AmplitudeAmplificationSource.Circuit.controlledGoodReflection good)
    (AmplitudeAmplificationSource.Circuit.controlledGoodReflection_physical_idx good)
    (extendedStage n stage)

theorem preparation_matrix {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (preparation t U).matrix =
      UnitaryOperator.tensor (1 : UnitaryOperator (Qubits (phaseWidth t n))) U := rfl

theorem inversePreparation_matrix {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (inversePreparation t U).matrix =
      UnitaryOperator.tensor (1 : UnitaryOperator (Qubits (phaseWidth t n))) U.dagger := rfl

theorem controlledGoodReflection_matrix {n t : Nat} (good : NormalizedVector (Qubits n))
    (stage : Fin t) :
    (controlledGoodReflection good stage).matrix = qpeControlledBitOp (phaseWidth t n)
      (OrthogonalProjector.rankOnePhaseReflectionOp good) (extendedStage n stage) :=
  StagePlacement.stageCall_matrix_controlled
    (AmplitudeAmplificationSource.Circuit.controlledGoodReflection good)
    (AmplitudeAmplificationSource.Circuit.controlledGoodReflection_physical_idx good)
    _ rfl (extendedStage n stage)

private theorem canonical_append (phases n : Nat) :
    List.range phases ++ List.range' phases n = List.range (phases + n) := by
  simpa only [List.range_eq_range', Nat.zero_add] using
    (List.range'_append_1 (s := 0) (m := phases) (n := n))

theorem preparation_physical_idx {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (preparation t U).physical_idx = List.range (totalQubits t n) :=
  canonical_append (phaseWidth t n) n

theorem inversePreparation_physical_idx {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (inversePreparation t U).physical_idx = List.range (totalQubits t n) :=
  canonical_append (phaseWidth t n) n

theorem controlledGoodReflection_full_physical_idx {n t : Nat}
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (controlledGoodReflection good stage).physical_idx = List.range (totalQubits t n) :=
  StagePlacement.stageCall_physical_idx _ _ _

theorem preparation_eventCost {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (preparation t U).eventCost = ResourcePool.singleton (preparationEvent n) := by
  change 0 + ResourcePool.singleton (preparationEvent n) = _
  exact zero_add _

theorem inversePreparation_eventCost {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (inversePreparation t U).eventCost = ResourcePool.singleton (inversePreparationEvent n) := by
  change 0 + ResourcePool.singleton (inversePreparationEvent n) = _
  exact zero_add _

theorem controlledGoodReflection_eventCost {n t : Nat} (good : NormalizedVector (Qubits n))
    (stage : Fin t) :
    (controlledGoodReflection good stage).eventCost =
      ResourcePool.singleton ((goodReflectionEvent n).controlForDimension 2) := by
  rw [controlledGoodReflection, StagePlacement.stageCall_eventCost]
  rfl

theorem preparation_unitDepth {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (preparation t U).evaluatedEventDepth (fun _ => 1) = 1 := rfl

theorem inversePreparation_unitDepth {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n)) :
    (inversePreparation t U).evaluatedEventDepth (fun _ => 1) = 1 := rfl

theorem controlledGoodReflection_unitDepth {n t : Nat} (good : NormalizedVector (Qubits n))
    (stage : Fin t) :
    (controlledGoodReflection good stage).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [controlledGoodReflection, StagePlacement.stageCall_evaluatedEventDepth]
  rfl

end

end QuantumAlg.AmplitudeEstimation.Elementary
