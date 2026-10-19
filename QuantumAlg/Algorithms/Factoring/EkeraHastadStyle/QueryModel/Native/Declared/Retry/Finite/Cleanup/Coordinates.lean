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

private lemma count_zero_of_le {execution : ExecutionModel}
    (event : Resource.Event execution) {actual allowance : ResourcePool execution}
    (bounded : actual ≤ allowance) (zero : ResourcePool.count event allowance = 0) :
    ResourcePool.count event actual = 0 :=
  Nat.eq_zero_of_le_zero (zero ▸ ResourcePool.le_iff_count.mp bounded event)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private abbrev groupQuery : Resource.Event (model N) :=
  .oracle .groupOperation

private lemma source_zero : ResourcePool.count (groupQuery N)
    (Batch.sourceEventBudget N) = 0 :=
  declared_source_count_eq_zero (groupQuery N) (fun _ => by simp) N

private lemma reset_zero (path : (resetBank base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((resetBank base noQuantum N).resourcePool path) = 0 := by
  apply count_zero_of_le _ (declaredReuse_reset_resourcePool_le base noQuantum N path)
  simp [resetEventBudget, ZReset.Bank.envelope, ZReset.eventEnvelope]

private lemma setup_zero (path : (Batch.setup base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.setup base noQuantum N).resourcePool path) = 0 := by
  apply count_zero_of_le _ (Batch.setup_pool base noQuantum N path)
  simp only [Batch.setupEventBudget, ResourcePool.count_add, source_zero]
  simp [preparationEventBudget]

private lemma redraw_zero (path : (Batch.redraw base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.redraw base noQuantum N).resourcePool path) = 0 :=
  count_zero_of_le _ (Batch.redraw_pool base noQuantum N path) (source_zero N)

private lemma copy_zero (index : Fin 16)
    (path : (Batch.copy base noQuantum N index).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.copy base noQuantum N index).resourcePool path) = 0 := by
  rw [Batch.copy_pool]
  simp [Batch.copyEvent]

private lemma member_query : ResourcePool.count (groupQuery N)
    (memberEventBudget N) = 1 := by
  have word := UnitaryCircuit.unitaryCircuit_event_count_classical_context
    (ShortDLP.DeclaredStage.circuit N (Native.parameters N) 1 1)
    BitWord.model .empty (groupQuery N)
  have exactWord := word.trans
    (ShortDLP.DeclaredStage.circuit_groupQueryCount N (Native.parameters N) 1 1)
  change ResourcePool.count (groupQuery N)
    ((ShortDLP.DeclaredStage.prepare N (Native.parameters N)).eventCost BitWord.model .empty +
      (ResourcePool.singleton (model := model N) (groupQuery N) +
        (ShortDLP.DeclaredStage.readout N (Native.parameters N)).eventCost
          BitWord.model .empty)) = 1 at exactWord
  simp only [memberEventBudget, ResourcePool.count_add]
  simpa using exactWord

private lemma reused_count (index : Fin 16)
    (path : (Batch.reusedSample base noQuantum N index).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.reusedSample base noQuantum N index).resourcePool path) = 1 := by
  change ResourcePool.count (groupQuery N)
    (((resetBank (Batch.storageContext base N) (Batch.storage_empty base noQuantum N)
      N).resourcePool path.1.1 + (body (Batch.storageContext base N)
        (Batch.storage_empty base noQuantum N) N
        (Batch.parameter base N)).resourcePool path.1.2) +
      (Batch.copy base noQuantum N index).resourcePool path.2) = _
  erw [ResourcePool.count_add, ResourcePool.count_add,
    reset_zero (Batch.storageContext base N) (Batch.storage_empty base noQuantum N),
    declaredSample_body_resourcePool, copy_zero, zero_add, add_zero]
  exact member_query N

private lemma first_batch_count (path : (Batch.firstBatch base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.firstBatch base noQuantum N).resourcePool path) = 16 := by
  have tail := Circuit.forRange_event_count (groupQuery N) 15
    (fun index => Batch.reusedSample base noQuantum N index.succ) 1
    (fun index => reused_count base noQuantum N index.succ) path.2
  have head := (congrArg (ResourcePool.count (groupQuery N))
    (declaredSample_body_resourcePool (Batch.storageContext base N)
      (Batch.storage_empty base noQuantum N) N (Batch.parameter base N) path.1.1)).trans
      (member_query N)
  have copied := copy_zero base noQuantum N 0 path.1.2
  change ResourcePool.count (groupQuery N)
    (((body (Batch.storageContext base N) (Batch.storage_empty base noQuantum N) N
      (Batch.parameter base N)).resourcePool path.1.1 +
        (Batch.copy base noQuantum N 0).resourcePool path.1.2) +
      (Circuit.forRange 15
        (fun index => Batch.reusedSample base noQuantum N index.succ)).resourcePool
          path.2) = _
  erw [ResourcePool.count_add, ResourcePool.count_add]
  omega

private lemma batch_count (path : (Batch.code base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.code base noQuantum N).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N)
    ((Batch.setup base noQuantum N).resourcePool path.1 +
      (Batch.firstBatch base noQuantum N).resourcePool path.2) = _
  erw [ResourcePool.count_add, setup_zero, first_batch_count, zero_add]

private lemma next_batch_count (path : (Batch.nextBatch base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.nextBatch base noQuantum N).resourcePool path) = 16 := by
  have tail := Circuit.forRange_event_count (groupQuery N) 16
    (Batch.reusedSample base noQuantum N) 1
    (reused_count base noQuantum N) path.2
  change ResourcePool.count (groupQuery N)
    ((Batch.redraw base noQuantum N).resourcePool path.1 +
      (Circuit.forRange 16 (Batch.reusedSample base noQuantum N)).resourcePool path.2) = _
  erw [ResourcePool.count_add, redraw_zero, tail, zero_add, mul_one]

private lemma recovery_zero (path : (Batch.Recovery.into base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.Recovery.into base noQuantum N input).resourcePool path) = 0 :=
  count_zero_of_le _ (Batch.Recovery.recovery_pool base noQuantum N input path)
    (declared_recovery_count_eq_zero (groupQuery N) (fun _ => by simp) N)

private lemma recovery_first_count (path : (Batch.Recovery.first base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.Recovery.first base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N)
    ((Batch.code base noQuantum N).resourcePool path.1 +
      (Batch.Recovery.into base noQuantum N input).resourcePool path.2) = _
  calc
    _ = ResourcePool.count (groupQuery N)
          ((Batch.code base noQuantum N).resourcePool path.1) +
        ResourcePool.count (groupQuery N)
          ((Batch.Recovery.into base noQuantum N input).resourcePool path.2) :=
      ResourcePool.count_add _ _ _
    _ = 16 + 0 := congrArg₂ (· + ·)
      (batch_count base noQuantum N path.1)
      (recovery_zero base noQuantum N input path.2)
    _ = 16 := by omega

private lemma recovery_next_count (path : (Batch.Recovery.next base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N)
      ((Batch.Recovery.next base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N)
    ((Batch.nextBatch base noQuantum N).resourcePool path.1 +
      (Batch.Recovery.into base noQuantum N input).resourcePool path.2) = _
  erw [ResourcePool.count_add, next_batch_count, recovery_zero, add_zero]

private lemma select_zero (path : (Retry.select base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((Retry.select base noQuantum N).resourcePool path) = 0 := by
  apply count_zero_of_le _ (Retry.selection_pool base noQuantum N path)
  simp [Retry.selectionEventBudget, ClassicalRoutines.FirstAccepted.Direct.Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace]

private lemma first_count (path : (Retry.first base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N)
      ((Retry.first base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N) (0 +
    ((Batch.Recovery.first (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N
      input).resourcePool path.2.1 +
        (Retry.select base noQuantum N).resourcePool path.2.2)) = _
  erw [zero_add, ResourcePool.count_add, recovery_first_count, select_zero, add_zero]

private lemma next_count (path : (Retry.next base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N)
      ((Retry.next base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N)
    ((Batch.Recovery.next (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N
      input).resourcePool path.1 + (Retry.select base noQuantum N).resourcePool path.2) = _
  erw [ResourcePool.count_add, recovery_next_count, select_zero, add_zero]

private lemma terminal_reset_zero (path : (reset base noQuantum N).Path) :
    ResourcePool.count (groupQuery N)
      ((reset base noQuantum N).resourcePool path) = 0 :=
  reset_zero (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N)
      (Retry.caller_empty base noQuantum N) N) N path

attribute [local irreducible] reset

-- Keep the arithmetic proof separate from the concrete circuit conversion.

/-- Each further physically completed batch pays exactly sixteen granted
group queries; its selector pack and bank reset add no query. -/
lemma nextCompleted_query_count
    (path : (nextCompletedCode base noQuantum N input).Path) :
    ResourcePool.count (groupQuery N)
      ((nextCompletedCode base noQuantum N input).resourcePool path) = 16 := by
  change ResourcePool.count (groupQuery N)
    (((Retry.next base noQuantum N input).resourcePool path.1.1 +
      ResourcePool.singleton (Retry.packEvent N)) +
      (reset base noQuantum N).resourcePool path.2) = _
  simp only [ResourcePool.count_add, next_count, terminal_reset_zero,
    Retry.packEvent, ResourcePool.count_singleton, reduceCtorEq, if_false,
    add_zero]

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
