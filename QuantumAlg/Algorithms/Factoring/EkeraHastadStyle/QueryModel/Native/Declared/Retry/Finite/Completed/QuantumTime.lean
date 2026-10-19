/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.Sample
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.ClassicalCoordinates
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Primitives.QFT.Native.Inverse.Depth
import all QuantumAlg.Core.Execution.Time

/-!
# Independent quantum time of every completed declared EH batch

The first batch has sixteen quantum members, fifteen internal bank resets,
and one terminal reset. Each further batch has sixteen members, sixteen
internal resets, and one terminal reset. Every reset uses the existing
one-layer correction bound. Actual source draws, recovery, selection, and
packing keep their native events and have zero canonical quantum duration.
The original arbitrary-duration total-work bounds remain separate.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

/-- Native inverse Fourier depth includes the actual phase expansions and parallel reversal. -/
public def nativeFourierQuantumTimeBound (width : Nat) : Nat :=
  width + 5 * width.choose 2 + (if width / 2 = 0 then 0 else 3)

/-- One Hadamard layer and one declared query precede two parallel native inverse QFTs. -/
public def memberQuantumTimeBound (N : Nat) : Nat :=
  2 + max
    (nativeFourierQuantumTimeBound (tradeoffBits N + shortLogBits N))
    (nativeFourierQuantumTimeBound (tradeoffBits N))

private lemma quantumWeight_zero_of_classical_coordinates {execution : ExecutionModel}
    (pool : ResourcePool execution)
    (absent : ∀ event : Resource.Event execution,
      (∀ label, event ≠ .classicalOperation label) → ResourcePool.count event pool = 0) :
    ResourcePool.weightedCount Resource.Event.quantumDuration pool = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event emitted
  cases event with
  | classicalOperation _ => rfl
  | classicalQuery _ => rfl
  | preparation _ => rfl
  | measurement _ => rfl
  | gate coordinate =>
      have zero := absent (.gate coordinate) (fun _ => by simp)
      have positive := Multiset.count_pos.mpr emitted
      exact False.elim ((Nat.ne_of_gt positive) zero)
  | oracle coordinate =>
      have zero := absent (.oracle coordinate) (fun _ => by simp)
      have positive := Multiset.count_pos.mpr emitted
      exact False.elim ((Nat.ne_of_gt positive) zero)

private lemma source_quantumWeight_zero (N : Nat) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (Batch.sourceEventBudget N) = 0 :=
  quantumWeight_zero_of_classical_coordinates _
    (fun event outside => declared_source_count_eq_zero event outside N)

private lemma recovery_quantumWeight_zero (N : Nat) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model N) N) = 0 :=
  quantumWeight_zero_of_classical_coordinates _
    (fun event outside => declared_recovery_count_eq_zero event outside N)

private lemma selection_quantumWeight_zero (N : Nat) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (Retry.selectionEventBudget N) = 0 := by
  simp [Retry.selectionEventBudget, Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace, Resource.Event.quantumDuration]

/-- The actual member clock retains the two parallel Fourier dependency paths. -/
lemma declaredSample_memberDuration_quantum_le (N : Nat) :
    memberDuration N Resource.Event.quantumDuration ≤ memberQuantumTimeBound N := by
  have prepared := (DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one
    ((ShortDLP.DeclaredStage.prepare N (Native.parameters N)).eventDepth
      BitWord.model .empty)).trans_eq
    (UnitaryCircuit.unitaryCircuit_unit_depth_classical_context
      (ShortDLP.DeclaredStage.prepare N (Native.parameters N)) BitWord.model .empty)
  rw [ShortDLP.DeclaredStage.prepare_unitDepth] at prepared
  have preparedOne : DepthExpr.depthEval Resource.Event.quantumDuration
      ((ShortDLP.DeclaredStage.prepare N (Native.parameters N)).eventDepth
        BitWord.model .empty) ≤ 1 :=
    prepared.trans (by split <;> omega)
  have readout := (DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one
    ((ShortDLP.DeclaredStage.readout N (Native.parameters N)).eventDepth
      BitWord.model .empty)).trans_eq
    (UnitaryCircuit.unitaryCircuit_unit_depth_classical_context
      (ShortDLP.DeclaredStage.readout N (Native.parameters N)) BitWord.model .empty)
  rw [ShortDLP.DeclaredStage.readout_unitDepth,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth] at readout
  change _ ≤ max
    (nativeFourierQuantumTimeBound (tradeoffBits N + shortLogBits N))
    (nativeFourierQuantumTimeBound (tradeoffBits N)) at readout
  simp only [memberDuration, DepthExpr.depthEval, Resource.Event.quantumDuration,
    Nat.mul_zero, Nat.add_zero]
  unfold memberQuantumTimeBound
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

namespace Batch

private lemma reused_quantumTime_le (index : Fin 16)
    (path : (reusedSample base noQuantum N index).Path) :
    (reusedSample base noQuantum N index).quantumTime path ≤
      resetQuantumTime N + memberQuantumTimeBound N := by
  change (reuse (storageContext base N) (storage_empty base noQuantum N)
    N (parameter base N)).quantumTime path.1 + 0 ≤ _
  exact (Nat.add_zero _).trans_le
    ((declaredReuse_quantumTime_le (storageContext base N)
      (storage_empty base noQuantum N) N (parameter base N) path.1).trans
      (Nat.add_le_add_left (declaredSample_memberDuration_quantum_le N) _))

private lemma firstBatch_quantumTime_le
    (path : (firstBatch base noQuantum N).Path) :
    (firstBatch base noQuantum N).quantumTime path ≤
      16 * memberQuantumTimeBound N + 15 * resetQuantumTime N := by
  have tail := Circuit.forRange_depth_le_sum 15
    (fun index => reusedSample base noQuantum N index.succ)
    Resource.Event.quantumDuration
    (fun _ => resetQuantumTime N + memberQuantumTimeBound N)
    (fun index => reused_quantumTime_le base noQuantum N index.succ) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  have first := (declaredSample_body_depth (storageContext base N)
    (storage_empty base noQuantum N) N (parameter base N)
    Resource.Event.quantumDuration path.1.1).trans_le
      (declaredSample_memberDuration_quantum_le N)
  change (body (storageContext base N) (storage_empty base noQuantum N)
      N (parameter base N)).depth Resource.Event.quantumDuration path.1.1 + 0 +
    (Circuit.forRange 15
      (fun index => reusedSample base noQuantum N index.succ)).depth
        Resource.Event.quantumDuration path.2 ≤ _
  nlinarith

private lemma first_quantumTime_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).quantumTime path ≤
      16 * memberQuantumTimeBound N + 15 * resetQuantumTime N := by
  have setupBound := setup_depth base noQuantum N Resource.Event.quantumDuration path.1
  have sourceZero := source_quantumWeight_zero N
  have setupZero : (setup base noQuantum N).quantumTime path.1 = 0 := by
    change (setup base noQuantum N).depth Resource.Event.quantumDuration path.1 = 0
    apply Nat.eq_zero_of_le_zero
    simpa only [sourceDurationBudget, sourceZero, preparationDuration,
      Resource.Event.quantumDuration, ite_self, Nat.zero_add] using setupBound
  change (setup base noQuantum N).quantumTime path.1 +
    (firstBatch base noQuantum N).quantumTime path.2 ≤ _
  rw [setupZero, Nat.zero_add]
  exact firstBatch_quantumTime_le base noQuantum N path.2

private lemma next_quantumTime_le (path : (nextBatch base noQuantum N).Path) :
    (nextBatch base noQuantum N).quantumTime path ≤
      16 * memberQuantumTimeBound N + 16 * resetQuantumTime N := by
  have head := Circuit.depth_le_weightedCount_of_pool_le (redraw base noQuantum N)
    Resource.Event.quantumDuration (sourceEventBudget N) path.1
    (redraw_pool base noQuantum N path.1)
  rw [source_quantumWeight_zero N] at head
  have tail := Circuit.forRange_depth_le_sum 16 (reusedSample base noQuantum N)
    Resource.Event.quantumDuration
    (fun _ => resetQuantumTime N + memberQuantumTimeBound N)
    (fun index => reused_quantumTime_le base noQuantum N index) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change (redraw base noQuantum N).depth Resource.Event.quantumDuration path.1 +
    (Circuit.forRange 16 (reusedSample base noQuantum N)).depth
      Resource.Event.quantumDuration path.2 ≤ _
  nlinarith

end Batch

namespace Batch.Recovery

private lemma recovery_quantumTime_zero (path : (into base noQuantum N input).Path) :
    (into base noQuantum N input).quantumTime path = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Circuit.depth_le_weightedCount_of_pool_le (into base noQuantum N input)
    Resource.Event.quantumDuration
    (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model N) N) path
    (recovery_pool base noQuantum N input path)).trans_eq
      (recovery_quantumWeight_zero N)

private lemma first_quantumTime_le (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).quantumTime path ≤
      16 * memberQuantumTimeBound N + 15 * resetQuantumTime N := by
  change (Batch.code base noQuantum N).quantumTime path.1 +
    (into base noQuantum N input).quantumTime path.2 ≤ _
  rw [recovery_quantumTime_zero, Nat.add_zero]
  exact Batch.first_quantumTime_le base noQuantum N path.1

private lemma next_quantumTime_le (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).quantumTime path ≤
      16 * memberQuantumTimeBound N + 16 * resetQuantumTime N := by
  change (Batch.nextBatch base noQuantum N).quantumTime path.1 +
    (into base noQuantum N input).quantumTime path.2 ≤ _
  rw [recovery_quantumTime_zero, Nat.add_zero]
  exact Batch.next_quantumTime_le base noQuantum N path.1

end Batch.Recovery

namespace Retry

private lemma selection_quantumTime_zero (path : (select base noQuantum N).Path) :
    (select base noQuantum N).quantumTime path = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (selection_depth base noQuantum N Resource.Event.quantumDuration path).trans_eq
    (selection_quantumWeight_zero N)

private lemma first_quantumTime_le (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).quantumTime path ≤
      16 * memberQuantumTimeBound N + 15 * resetQuantumTime N := by
  change 0 + ((Batch.Recovery.first (callerContext base N)
    (caller_empty base noQuantum N) N input).quantumTime path.2.1 +
      (select base noQuantum N).quantumTime path.2.2) ≤ _
  have selected := selection_quantumTime_zero base noQuantum N path.2.2
  have bounded := Batch.Recovery.first_quantumTime_le (callerContext base N)
    (caller_empty base noQuantum N) N input path.2.1
  exact (Nat.zero_add _).trans_le
    ((Nat.add_le_add bounded (Nat.le_of_eq selected)).trans_eq (Nat.add_zero _))

private lemma next_quantumTime_le (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).quantumTime path ≤
      16 * memberQuantumTimeBound N + 16 * resetQuantumTime N := by
  change (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input).quantumTime path.1 +
      (select base noQuantum N).quantumTime path.2 ≤ _
  have selected := selection_quantumTime_zero base noQuantum N path.2
  have bounded := Batch.Recovery.next_quantumTime_le (callerContext base N)
    (caller_empty base noQuantum N) N input path.1
  exact (Nat.add_le_add bounded (Nat.le_of_eq selected)).trans_eq (Nat.add_zero _)

namespace Finite.Cleanup

/-- Every completed member and every internal or terminal reset is charged in order. -/
public def completedQuantumTimeBudget (N laterCount : Nat) : Nat :=
  16 * (laterCount + 1) * memberQuantumTimeBound N +
    (16 + 17 * laterCount) * resetQuantumTime N

private lemma reset_quantumTime_le (path : (reset base noQuantum N).Path) :
    (reset base noQuantum N).quantumTime path ≤ resetQuantumTime N :=
  declaredReuse_reset_quantumTime_le (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N path

private lemma firstCompleted_quantumTime_le
    (path : (firstCompletedAlgorithm base noQuantum input).run.code.Path) :
    (firstCompletedAlgorithm base noQuantum input).run.code.quantumTime path ≤
      16 * memberQuantumTimeBound N + 16 * resetQuantumTime N := by
  have first := Retry.first_quantumTime_le base noQuantum N input path.1.1
  have last := reset_quantumTime_le base noQuantum N path.2
  change (Retry.first base noQuantum N input).quantumTime path.1.1 +
    (0 + 0) + (reset base noQuantum N).quantumTime path.2 ≤ _
  nlinarith

private lemma nextCompleted_quantumTime_le
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCode base noQuantum N input).quantumTime path ≤
      16 * memberQuantumTimeBound N + 17 * resetQuantumTime N := by
  have first := Retry.next_quantumTime_le base noQuantum N input path.1.1
  have last := reset_quantumTime_le base noQuantum N path.2
  change (Retry.next base noQuantum N input).quantumTime path.1.1 + 0 +
    (reset base noQuantum N).quantumTime path.2 ≤ _
  nlinarith

/-- The same complete code obeys an independent whole-run quantum bound at every count. -/
lemma declaredCompleted_quantumTime_le (laterCount : Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    (completedCode base noQuantum N input laterCount).quantumTime path ≤
      completedQuantumTimeBudget N laterCount := by
  have tail := Circuit.forRange_depth_le_sum laterCount
    (fun _ => nextCompletedCode base noQuantum N input) Resource.Event.quantumDuration
    (fun _ => 16 * memberQuantumTimeBound N + 17 * resetQuantumTime N)
    (fun _ => nextCompleted_quantumTime_le base noQuantum N input) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  have first := firstCompleted_quantumTime_le base noQuantum N input path.1
  change (firstCompletedAlgorithm base noQuantum input).run.code.quantumTime path.1 +
    (laterCompletedCode base noQuantum N input laterCount).depth
      Resource.Event.quantumDuration path.2 ≤ _
  calc
    _ ≤ (16 * memberQuantumTimeBound N + 16 * resetQuantumTime N) +
        laterCount * (16 * memberQuantumTimeBound N + 17 * resetQuantumTime N) :=
      Nat.add_le_add first tail
    _ = completedQuantumTimeBudget N laterCount := by
      unfold completedQuantumTimeBudget
      ring

end Finite.Cleanup
end Retry

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
