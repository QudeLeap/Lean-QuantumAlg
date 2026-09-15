/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Physically placed amplitude-amplification source queries

These actual occurrences implement the three distinct source operations on
consecutive source wires. Only the good-reflection occurrence is offered
with a leading control. Known all-zero reflections are implemented by the
separate elementary zero-reflection owners.
-/

namespace QuantumAlg.AmplitudeAmplificationSource.Circuit

noncomputable section

/-- One source preparation on the consecutive source wires. -/
def preparation {n : Nat} (offset : Nat) (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf (preparationLeafAt U (List.range' offset n))
    List.nodup_range'

/-- One inverse call to the same source preparation. -/
def inversePreparation {n : Nat} (offset : Nat) (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf (inversePreparationLeafAt U (List.range' offset n))
    List.nodup_range'

/-- The source good-state phase reflection on the source wires. -/
def goodReflection {n : Nat} (offset : Nat) (good : NormalizedVector (Qubits n)) :
    UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf (goodReflectionLeafAt good (List.range' offset n))
    List.nodup_range'

private theorem leadingLayout {n : Nat} (body : UnitaryCircuit (Qubits n))
    (placed : body.physical_idx = List.range' 1 n) :
    PhysicalLayout.DisjointMerge [0] body.physical_idx :=
  { left_nodup := by simp
    right_nodup := body.physical_idx_nodup
    disjoint := by
      rw [placed, List.disjoint_left]
      intro index atControl atSource
      have startsAtOne := List.left_le_of_mem_range' atSource
      simp only [List.mem_singleton] at atControl
      omega }

/-- Only the source good-state phase reflection receives quantum control. -/
def controlledGoodReflection {n : Nat} (good : NormalizedVector (Qubits n)) :
    UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.controlQubitsAt [0] (goodReflection 1 good) (leadingLayout _ rfl) 1

theorem controlledGoodReflection_physical_idx {n : Nat}
    (good : NormalizedVector (Qubits n)) :
    (controlledGoodReflection good).physical_idx =
      List.range (1 + n) := by
  change 0 :: List.range' 1 n = List.range (1 + n)
  simpa only [List.range_eq_range', Nat.add_comm] using
    (List.range'_succ (s := 0) (n := n)).symm

theorem preparation_physical_idx {n : Nat} (offset : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (preparation offset U).physical_idx = List.range' offset n := rfl

theorem inversePreparation_physical_idx {n : Nat} (offset : Nat)
    (U : UnitaryOperator (Qubits n)) :
    (inversePreparation offset U).physical_idx = List.range' offset n := rfl

theorem goodReflection_physical_idx {n : Nat} (offset : Nat)
    (good : NormalizedVector (Qubits n)) :
    (goodReflection offset good).physical_idx = List.range' offset n := rfl

theorem preparation_matrix {n : Nat} (offset : Nat) (U : UnitaryOperator (Qubits n)) :
    (preparation offset U).matrix = U := rfl

theorem inversePreparation_matrix {n : Nat} (offset : Nat) (U : UnitaryOperator (Qubits n)) :
    (inversePreparation offset U).matrix = U.dagger := rfl

theorem goodReflection_matrix {n : Nat} (offset : Nat) (good : NormalizedVector (Qubits n)) :
    (goodReflection offset good).matrix = OrthogonalProjector.rankOnePhaseReflectionOp good := rfl

theorem preparation_eventCost {n : Nat} (offset : Nat) (U : UnitaryOperator (Qubits n)) :
    (preparation offset U).eventCost = ResourcePool.singleton (preparationEvent n) := rfl

theorem inversePreparation_eventCost {n : Nat} (offset : Nat) (U : UnitaryOperator (Qubits n)) :
    (inversePreparation offset U).eventCost =
      ResourcePool.singleton (inversePreparationEvent n) := rfl

theorem goodReflection_eventCost {n : Nat} (offset : Nat)
    (good : NormalizedVector (Qubits n)) :
    (goodReflection offset good).eventCost = ResourcePool.singleton (goodReflectionEvent n) := rfl

end

end QuantumAlg.AmplitudeAmplificationSource.Circuit
