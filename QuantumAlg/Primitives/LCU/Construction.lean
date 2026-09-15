/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.LCU.Basic
public import QuantumAlg.Components.Oracle.UnitarySource
import all QuantumAlg.Primitives.LCU.Basic
import all QuantumAlg.Components.Oracle.UnitarySource
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Actual prepare, SELECT, unprepare execution

The source access model uses a supplied preparation unitary and its inverse,
and one declared SELECT query [Lin22, hermfunc.tex:531-554]. The physical
normalization at the boundary retains every supplied system and adds no event.
-/

namespace QuantumAlg.LinearCombinationOfUnitaries

noncomputable section

variable {a n : Nat}

/-- The actual three-query LCU circuit on the complete supplied joint register. -/
public def circuit (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits (a + n)) :=
  (lcuWalkCircuit (UnitarySource.program V) (UnitarySource.program_physicalIdx V) U).seq
    (UnitaryCircuit.identity (Qubits (a + n)) (List.range (a + n)) List.nodup_range)

/-- The concrete circuit has exactly the original metadata-free LCU operator. -/
theorem circuit_matrix (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (circuit V U).matrix = lcuWalk V U := by
  change 1 * (lcuWalkCircuit (UnitarySource.program V)
    (UnitarySource.program_physicalIdx V) U).matrix = _
  rw [one_mul]
  exact lcuWalkCircuit_matrix (UnitarySource.program V)
    (UnitarySource.program_physicalIdx V) U

private theorem prepare_contained (V : UnitaryOperator (Qubits a)) (n : Nat) :
    (lcuPrepareCircuit (UnitarySource.program V)
      (UnitarySource.program_physicalIdx V) n).physical_idx ⊆
      List.range (a + n) := by
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · intro wire present
    change wire ∈ List.range a at present
    simp only [List.mem_range] at present ⊢
    omega
  · intro wire present
    change wire ∈ (List.range n).map (fun index => a + index) at present
    obtain ⟨index, bounded, rfl⟩ := List.mem_map.mp present
    simp only [List.mem_range] at bounded ⊢
    omega

/-- The actual footprint is the original a+n supplied physical systems. -/
theorem circuit_physicalIdx (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (circuit V U).physical_idx = List.range (a + n) := by
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  apply UnitaryCircuit.seq_physical_idx_subset
  · apply UnitaryCircuit.seq_physical_idx_subset
    · exact prepare_contained V n
    · intro wire present
      exact present
  · exact UnitaryCircuit.dagger_physical_idx_subset _ (prepare_contained V n)

/-- Two source-unitary accesses and one SELECT access are the exact native pool. -/
theorem circuit_events (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (circuit V U).eventCost =
      2 • ResourcePool.singleton (UnitarySource.event a) +
        ResourcePool.singleton (lcuSelectEvent a n) := by
  simp only [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost,
    add_zero, lcuWalkCircuit_eventCost, UnitarySource.program_eventCost, two_nsmul]
  ac_rfl

/-- The same native execution has at most three unit-duration event layers. -/
theorem circuit_depth (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (circuit V U).evaluatedEventDepth (fun _ => 1) ≤ 3 := by
  calc
    _ ≤ DepthExpr.costEval (fun _ => 1) (circuit V U).eventDepth :=
      DepthExpr.depthEval_le_costEval (fun _ => 1) (circuit V U).eventDepth
    _ = (circuit V U).eventCost.card :=
      (DepthExpr.unitCost_eq_eventPool_card (circuit V U).eventDepth).trans
        (congrArg Multiset.card (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost _))
    _ = 3 := by
      rw [circuit_events]
      simp [ResourcePool.singleton]

end

end QuantumAlg.LinearCombinationOfUnitaries
