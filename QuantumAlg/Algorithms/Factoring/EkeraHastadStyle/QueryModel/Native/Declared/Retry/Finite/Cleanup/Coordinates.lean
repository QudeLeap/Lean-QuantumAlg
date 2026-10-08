/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.ClassicalCoordinates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage

/-!
# Exact granted queries of declared EH primitives

Each actual sample member contributes one granted group query. Source
preparation, recovery, selection and physical resets contribute zero.
The first and reused batch primitives each contribute sixteen queries;
their canonical finite composition has a separate all-count theorem.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

private theorem count_zero_of_le {execution : ExecutionModel}
    (event : Resource.Event execution) {actual allowance : ResourcePool execution}
    (bounded : actual ≤ allowance) (zero : ResourcePool.count event allowance = 0) :
    ResourcePool.count event actual = 0 :=
  Nat.eq_zero_of_le_zero (zero ▸ ResourcePool.le_iff_count.mp bounded event)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private abbrev groupQuery : Resource.Event (model input) :=
  .oracle .groupOperation

private theorem source_zero : ResourcePool.count (groupQuery N input)
    (Batch.sourceEventBudget input) = 0 :=
  declared_source_count_eq_zero (groupQuery N input) (fun _ => by simp) N

private theorem reset_zero (path : (resetBank base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((resetBank base noQuantum N input).resourcePool path) = 0 := by
  apply count_zero_of_le _ (declaredReuse_reset_resourcePool_le base noQuantum N input path)
  simp [resetEventBudget, ZReset.Bank.envelope, ZReset.eventEnvelope]

private theorem setup_zero (path : (Batch.setup base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.setup base noQuantum N input).resourcePool path) = 0 := by
  apply count_zero_of_le _ (Batch.setup_pool base noQuantum N input path)
  simp only [Batch.setupEventBudget, ResourcePool.count_add, source_zero]
  simp [preparationEventBudget]

private theorem redraw_zero (path : (Batch.redraw base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.redraw base noQuantum N input).resourcePool path) = 0 :=
  count_zero_of_le _ (Batch.redraw_pool base noQuantum N input path) (source_zero N input)

private theorem copy_zero (index : Fin 16)
    (path : (Batch.copy base noQuantum N input index).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.copy base noQuantum N input index).resourcePool path) = 0 := by
  rw [Batch.copy_pool]
  simp [Batch.copyEvent]

private theorem member_query : ResourcePool.count (groupQuery N input)
    (memberEventBudget input) = 1 := by
  have word := UnitaryCircuit.unitaryCircuit_event_count_classical_context
    (ShortDLP.DeclaredStage.circuit (Native.encoding input) 1 1)
    BitWord.model .empty (groupQuery N input)
  have exactWord := word.trans
    (ShortDLP.DeclaredStage.circuit_groupQueryCount (Native.encoding input) 1 1)
  change ResourcePool.count (groupQuery N input)
    ((ShortDLP.DeclaredStage.prepare (Native.encoding input)).eventCost BitWord.model .empty +
      (ResourcePool.singleton (model := model input) (groupQuery N input) +
        (ShortDLP.DeclaredStage.readout (Native.encoding input)).eventCost
          BitWord.model .empty)) = 1 at exactWord
  simp only [memberEventBudget, ResourcePool.count_add]
  simpa using exactWord

private theorem reused_count (index : Fin 16)
    (path : (Batch.reusedSample base noQuantum N input index).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.reusedSample base noQuantum N input index).resourcePool path) = 1 := by
  change ResourcePool.count (groupQuery N input)
    (((resetBank (Batch.storageContext base N) (Batch.storage_empty base noQuantum N)
      N input).resourcePool path.1.1 + (body (Batch.storageContext base N)
        (Batch.storage_empty base noQuantum N) N input
        (Batch.parameter base N)).resourcePool path.1.2) +
      (Batch.copy base noQuantum N input index).resourcePool path.2) = _
  erw [ResourcePool.count_add, ResourcePool.count_add,
    reset_zero (Batch.storageContext base N) (Batch.storage_empty base noQuantum N),
    declaredSample_body_resourcePool, copy_zero, zero_add, add_zero]
  exact member_query N input

private theorem first_batch_count (path : (Batch.firstBatch base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.firstBatch base noQuantum N input).resourcePool path) = 16 := by
  have tail := Circuit.forRange_event_count (groupQuery N input) 15
    (fun index => Batch.reusedSample base noQuantum N input index.succ) 1
    (fun index => reused_count base noQuantum N input index.succ) path.2
  have head := (congrArg (ResourcePool.count (groupQuery N input))
    (declaredSample_body_resourcePool (Batch.storageContext base N)
      (Batch.storage_empty base noQuantum N) N input (Batch.parameter base N) path.1.1)).trans
      (member_query N input)
  have copied := copy_zero base noQuantum N input 0 path.1.2
  change ResourcePool.count (groupQuery N input)
    (((body (Batch.storageContext base N) (Batch.storage_empty base noQuantum N) N input
      (Batch.parameter base N)).resourcePool path.1.1 +
        (Batch.copy base noQuantum N input 0).resourcePool path.1.2) +
      (Circuit.forRange 15
        (fun index => Batch.reusedSample base noQuantum N input index.succ)).resourcePool
          path.2) = _
  erw [ResourcePool.count_add, ResourcePool.count_add]
  omega

private theorem batch_count (path : (Batch.code base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.code base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N input)
    ((Batch.setup base noQuantum N input).resourcePool path.1 +
      (Batch.firstBatch base noQuantum N input).resourcePool path.2) = _
  erw [ResourcePool.count_add, setup_zero, first_batch_count, zero_add]

private theorem next_batch_count (path : (Batch.nextBatch base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.nextBatch base noQuantum N input).resourcePool path) = 16 := by
  have tail := Circuit.forRange_event_count (groupQuery N input) 16
    (Batch.reusedSample base noQuantum N input) 1
    (reused_count base noQuantum N input) path.2
  change ResourcePool.count (groupQuery N input)
    ((Batch.redraw base noQuantum N input).resourcePool path.1 +
      (Circuit.forRange 16 (Batch.reusedSample base noQuantum N input)).resourcePool path.2) = _
  erw [ResourcePool.count_add, redraw_zero, tail, zero_add, mul_one]

private theorem recovery_zero (path : (Batch.Recovery.into base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.Recovery.into base noQuantum N input).resourcePool path) = 0 :=
  count_zero_of_le _ (Batch.Recovery.recovery_pool base noQuantum N input path)
    (declared_recovery_count_eq_zero (groupQuery N input) (fun _ => by simp) N)

private theorem recovery_first_count (path : (Batch.Recovery.first base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.Recovery.first base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N input)
    ((Batch.code base noQuantum N input).resourcePool path.1 +
      (Batch.Recovery.into base noQuantum N input).resourcePool path.2) = _
  calc
    _ = ResourcePool.count (groupQuery N input)
          ((Batch.code base noQuantum N input).resourcePool path.1) +
        ResourcePool.count (groupQuery N input)
          ((Batch.Recovery.into base noQuantum N input).resourcePool path.2) :=
      ResourcePool.count_add _ _ _
    _ = 16 + 0 := congrArg₂ (· + ·)
      (batch_count base noQuantum N input path.1)
      (recovery_zero base noQuantum N input path.2)
    _ = 16 := by omega

private theorem recovery_next_count (path : (Batch.Recovery.next base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Batch.Recovery.next base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N input)
    ((Batch.nextBatch base noQuantum N input).resourcePool path.1 +
      (Batch.Recovery.into base noQuantum N input).resourcePool path.2) = _
  erw [ResourcePool.count_add, next_batch_count, recovery_zero, add_zero]

private theorem select_zero (path : (Retry.select base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Retry.select base noQuantum N input).resourcePool path) = 0 := by
  apply count_zero_of_le _ (Retry.selection_pool base noQuantum N input path)
  simp [Retry.selectionEventBudget, ClassicalRoutines.FirstAccepted.Direct.Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace]

private theorem first_count (path : (Retry.first base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Retry.first base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N input) (0 +
    ((Batch.Recovery.first (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N
      input).resourcePool path.2.1 +
        (Retry.select base noQuantum N input).resourcePool path.2.2)) = _
  erw [zero_add, ResourcePool.count_add, recovery_first_count, select_zero, add_zero]

private theorem next_count (path : (Retry.next base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((Retry.next base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N input)
    ((Batch.Recovery.next (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N
      input).resourcePool path.1 + (Retry.select base noQuantum N input).resourcePool path.2) = _
  erw [ResourcePool.count_add, recovery_next_count, select_zero, add_zero]

private theorem terminal_reset_zero (path : (reset base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((reset base noQuantum N input).resourcePool path) = 0 :=
  reset_zero (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N)
      (Retry.caller_empty base noQuantum N) N) N input path

attribute [local irreducible] reset

-- Keep the arithmetic proof separate from the concrete circuit conversion.

/-- Each further physically completed batch pays exactly sixteen granted
group queries; its selector pack and bank reset add no query. -/
theorem nextCompleted_query_count
    (path : (nextCompletedCode base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N input)
      ((nextCompletedCode base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N input)
    (((Retry.next base noQuantum N input).resourcePool path.1.1 +
      ResourcePool.singleton (Retry.packEvent input)) +
      (reset base noQuantum N input).resourcePool path.2) = _
  simp only [ResourcePool.count_add, next_count, terminal_reset_zero,
    Retry.packEvent, ResourcePool.count_singleton, reduceCtorEq, if_false,
    add_zero]

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
