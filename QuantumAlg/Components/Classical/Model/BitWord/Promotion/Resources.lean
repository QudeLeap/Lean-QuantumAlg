/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Promotion
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight

/-! # Native coordinate observations of quantum-ledger selection -/

namespace QuantumAlg.BitWord

noncomputable section

/-- Selecting native bit/word operations preserves a quantum gate coordinate. -/
theorem liftQuantumPool_gate_count (gate : AlgorithmGate.Coordinate)
    (pool : ResourcePool (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate gate) (liftQuantumPool pool) =
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate gate) pool := by
  unfold ResourcePool.count liftQuantumPool
  rw [Multiset.count_map]
  have predicate (event : Resource.Event (.quantum AlgorithmGate.model .empty)) :
      (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty BitWord.model) gate =
          liftQuantumEvent event) ↔
        (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) gate = event) := by
    cases event with
    | classicalOperation impossible => cases impossible
    | classicalQuery impossible => cases impossible
    | gate coordinate => simp [liftQuantumEvent]
    | oracle coordinate => simp [liftQuantumEvent]
    | preparation dimension => simp [liftQuantumEvent]
    | measurement dimension => simp [liftQuantumEvent]
  have filtered :
      Multiset.filter (fun event : Resource.Event (.quantum AlgorithmGate.model .empty) =>
        Resource.Event.gate (model := .quantum AlgorithmGate.model .empty BitWord.model) gate =
          liftQuantumEvent event) pool =
      Multiset.filter (fun event =>
        Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) gate = event) pool := by
    apply Multiset.filter_congr
    intro event _member
    exact predicate event
  exact (congrArg Multiset.card filtered).trans
    (Multiset.count_eq_card_filter_eq pool
      (.gate (model := .quantum AlgorithmGate.model .empty) gate)).symm

/-- A selected pure-quantum ledger has no classical-operation occurrences. -/
theorem liftQuantumPool_classicalWeight_zero
    (pool : ResourcePool (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (liftQuantumPool pool) = 0 := by
  rw [liftQuantumPool_weightedCount]
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event _present
  cases event with
  | classicalOperation impossible => cases impossible
  | classicalQuery impossible => cases impossible
  | gate coordinate => rfl
  | oracle coordinate => rfl
  | preparation dimension => rfl
  | measurement dimension => rfl

end

end QuantumAlg.BitWord
