/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Resources.Bounds
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Resources

/-!
# Resources of the actual terminally cleaned three-attempt circuit

These bounds refer to the same emitted program as `runFinalized`. The terminal
reset contributes 854 real measurements and at most 854 native X gates, while
reusing its existing feedback cell and all 854 original physical systems.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Inputs

noncomputable section

open Execution ClassicalWorkspace ClassicalRoutines

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx)

private lemma repeated_count_upper {model : ExecutionModel} {inner : RuntimeCtx model.kind}
    {allocation : Bool} (code : Circuit model inner inner allocation)
    (event : Resource.Event model) (limit : Nat)
    (bounded : ∀ path, ResourcePool.count event (code.resourcePool path) ≤ limit)
    (count : Nat) (path : (Circuit.forRange count fun _ => code).Path) :
    ResourcePool.count event ((Circuit.forRange count fun _ => code).resourcePool path) ≤
      count * limit := by
  induction count with
  | zero =>
      change ResourcePool.count event (0 : ResourcePool model) ≤ 0 * limit
      simp only [ResourcePool.count_zero, Nat.zero_mul, Nat.le_refl]
  | succ count ih =>
      change ResourcePool.count event (code.resourcePool path.1 +
        (Circuit.forRange count fun _ => code).resourcePool path.2) ≤ _
      rw [ResourcePool.count_add, Nat.succ_mul]
      have first := bounded path.1
      have rest := ih path.2
      omega

private lemma finalizedInnerBody_measurement_count
    {inner : RuntimeCtx .quantum} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (selected : (inputs.finalizedInnerBody (services := services) sampler checkers count).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((inputs.finalizedInnerBody (services := services) sampler checkers count).resourcePool
        selected) = count * 71526 + 854 := by
  unfold finalizedInnerBody at selected ⊢
  let cleanup := finalizedCleanup sampler
  have attempts := Circuit.forRange_event_count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+)) count
    (fun _ => inputs.attempt (services := services) sampler checkers) 71526
    (fun _ current => inputs.attempt_measurement_count (services := services)
      sampler checkers current) selected.1
  have terminal := cleanup.circuit_measurement_count (services := services) selected.2
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+))
      (((Circuit.forRange count fun _ => inputs.attempt (services := services) sampler checkers).seq
        (.embed (ContextEmbedding.identity _) cleanup.circuit)).resourcePool selected) = _
  rw [Circuit.resourcePool_count_seq, Circuit.resourcePool_embed, attempts, terminal]

private lemma finalizedInnerBody_native_le
    {inner : RuntimeCtx .quantum} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (coordinate : AlgorithmGate.Coordinate)
    (selected : (inputs.finalizedInnerBody (services := services) sampler checkers count).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate)
      ((inputs.finalizedInnerBody (services := services) sampler checkers count).resourcePool
        selected) ≤ count * Recovery.Parameters.sampleNativeLimit coordinate +
          (if coordinate = .singleQubit then 854 else 0) := by
  unfold finalizedInnerBody at selected ⊢
  let cleanup := finalizedCleanup sampler
  have terminal := cleanup.circuit_native_counts (services := services) selected.2
  have one : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) (cleanup.circuit.resourcePool selected.2) ≤
        if coordinate = .singleQubit then 854 else 0 := by
    cases coordinate with
    | toffoli => exact terminal.1.le
    | cnot => exact terminal.2.1.le
    | singleQubit => exact terminal.2.2
  have repeated : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate)
      ((Circuit.forRange count fun _ => inputs.attempt (services := services) sampler
        checkers).resourcePool selected.1) ≤
          count * Recovery.Parameters.sampleNativeLimit coordinate := by
    exact repeated_count_upper
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      _ (.gate coordinate) _
      (fun current => inputs.attempt_native_le (services := services) sampler checkers
        coordinate current) count selected.1
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.gate coordinate)
      (((Circuit.forRange count fun _ => inputs.attempt (services := services) sampler checkers).seq
        (.embed (ContextEmbedding.identity _) cleanup.circuit)).resourcePool selected) ≤ _
  rw [Circuit.resourcePool_count_seq, Circuit.resourcePool_embed]
  exact Nat.add_le_add repeated one

private lemma finalizedInnerBody_quantumTime_le
    {inner : RuntimeCtx .quantum} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (selected : (inputs.finalizedInnerBody (services := services) sampler checkers count).Path) :
    (inputs.finalizedInnerBody (services := services) sampler checkers count).depth
      Resource.Event.quantumDuration selected ≤ count * 57061815979 + 854 := by
  unfold finalizedInnerBody at selected ⊢
  let cleanup := finalizedCleanup sampler
  have attempts := Recovery.Parameters.repeated_depth_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    _ Resource.Event.quantumDuration _
    (fun current => inputs.attempt_quantumTime_le (services := services)
      sampler checkers current) count selected.1
  have terminal := cleanup.circuit_quantumTime_le (services := services) selected.2
  change (((Circuit.forRange count fun _ => inputs.attempt (services := services)
    sampler checkers).seq
    (.embed (ContextEmbedding.identity _) cleanup.circuit)).depth
      Resource.Event.quantumDuration selected) ≤ _
  exact (Recovery.Parameters.sequential_depth _ _ Resource.Event.quantumDuration
    selected).le.trans (Nat.add_le_add attempts terminal)

private lemma finalizedInnerBody_classical_le
    {inner : RuntimeCtx .quantum} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (selected : (inputs.finalizedInnerBody (services := services) sampler checkers count).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((inputs.finalizedInnerBody (services := services) sampler checkers count).resourcePool
        selected) ≤ count * 6762727521 := by
  unfold finalizedInnerBody at selected ⊢
  let cleanup := finalizedCleanup sampler
  have attempts := Recovery.Parameters.repeated_weight_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    _ Resource.Event.classicalOperationWeight _
    (fun current => inputs.attempt_classical_le (services := services)
      sampler checkers current) count selected.1
  have terminal := cleanup.circuit_classical_zero (services := services) selected.2
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    (((Circuit.forRange count fun _ => inputs.attempt (services := services)
      sampler checkers).seq (.embed (ContextEmbedding.identity _) cleanup.circuit)).resourcePool
        selected) ≤ _
  rw [Recovery.Parameters.sequential_pool, ResourcePool.weightedCount_add,
    Circuit.resourcePool_embed, terminal, Nat.add_zero]
  exact attempts

attribute [local irreducible] scopedAttemptsFinalized withFrame

/-- The original attempt measurements and the final complete reset are counted
on the same path, through the one actual feedback-cell scope. -/
lemma scopedAttemptsFinalized_measurement_count (count : Nat)
    (path : (original.scopedAttemptsFinalized (services := services) count).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((original.scopedAttemptsFinalized (services := services) count).resourcePool path) =
        count * 71526 + 854 := by
  unfold scopedAttemptsFinalized at path ⊢
  apply withFrame_event_count (model := .quantum AlgorithmGate.model .empty BitWord.model
    services) _ 256 256 _ (.measurement (2 : ℕ+)) (count * 71526 + 854) ?_ path
  intro inner lift same frame fresh selected
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  exact inputs.finalizedInnerBody_measurement_count (services := services)
    sampler checkers count selected

/-- Terminal cleanup adds no Toffoli or CNOT and at most 854 one-qubit gates. -/
lemma scopedAttemptsFinalized_native_le (count : Nat)
    (coordinate : AlgorithmGate.Coordinate)
    (path : (original.scopedAttemptsFinalized (services := services) count).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate)
      ((original.scopedAttemptsFinalized (services := services) count).resourcePool path) ≤
        count * Recovery.Parameters.sampleNativeLimit coordinate +
          (if coordinate = .singleQubit then 854 else 0) := by
  unfold scopedAttemptsFinalized at path ⊢
  apply withFrame_count_le (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    _ 256 256 _ (.gate coordinate)
    (count * Recovery.Parameters.sampleNativeLimit coordinate +
      (if coordinate = .singleQubit then 854 else 0)) ?_ path
  intro inner lift same frame fresh selected
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  exact inputs.finalizedInnerBody_native_le (services := services)
    sampler checkers count coordinate selected

/-- The three actual attempts and terminal whole-bank reset have 215432 physical MZs. -/
lemma runFinalized_measurement_count
    (path : (original.runFinalized (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((original.runFinalized (services := services)).code.resourcePool path) = 215432 := by
  unfold runFinalized at path ⊢
  have repeated := original.scopedAttemptsFinalized_measurement_count
    (services := services) 3 path.1.2
  have packed := Recovery.Parameters.pack_nonclassical_zero (services := services)
    (.measurement (2 : ℕ+)) (by intro label same; cases same) path.2
  rw [Circuit.resourcePool_count_seq, Circuit.resourcePool_count_seq,
    EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    ResourcePool.count_zero, packed, Nat.zero_add, Nat.add_zero]
  exact repeated

/-- The same full program keeps its three-attempt native budget plus terminal X gates. -/
lemma runFinalized_native_le (coordinate : AlgorithmGate.Coordinate)
    (path : (original.runFinalized (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate)
      ((original.runFinalized (services := services)).code.resourcePool path) ≤
        Recovery.Parameters.runNativeLimit coordinate +
          (if coordinate = .singleQubit then 854 else 0) := by
  unfold runFinalized at path ⊢
  have repeated := original.scopedAttemptsFinalized_native_le (services := services)
    3 coordinate path.1.2
  have packed := Recovery.Parameters.pack_nonclassical_zero (services := services)
    (.gate coordinate) (by intro label same; cases same) path.2
  rw [Circuit.resourcePool_count_seq, Circuit.resourcePool_count_seq,
    EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    ResourcePool.count_zero, packed, Nat.zero_add, Nat.add_zero]
  simpa only [Recovery.Parameters.runNativeLimit] using repeated

/-- Quantum duration includes every possible terminal X after three attempts. -/
lemma scopedAttemptsFinalized_quantumTime_le (count : Nat)
    (path : (original.scopedAttemptsFinalized (services := services) count).Path) :
    (original.scopedAttemptsFinalized (services := services) count).depth
      Resource.Event.quantumDuration path ≤ count * 57061815979 + 854 := by
  unfold scopedAttemptsFinalized at path ⊢
  apply withFrame_depth_le (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    _ 256 256 _ Resource.Event.quantumDuration (count * 57061815979 + 854) ?_ path
  intro inner lift same frame fresh selected
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  exact inputs.finalizedInnerBody_quantumTime_le (services := services)
    sampler checkers count selected

/-- The full terminally cleaned run has an actual path bound of 171185448791. -/
lemma runFinalized_quantumTime_le
    (path : (original.runFinalized (services := services)).code.Path) :
    (original.runFinalized (services := services)).code.depth
      Resource.Event.quantumDuration path ≤ 171185448791 := by
  unfold runFinalized at path ⊢
  have repeated := original.scopedAttemptsFinalized_quantumTime_le
    (services := services) 3 path.1.2
  have retained := EllipticCurve.CandidateCheck.Native.retainPersistent_depth
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
      Resource.Event.quantumDuration path.1.1
  have packed := EllipticCurve.CandidateCheck.Native.packBatchResult_depth
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
      Resource.Event.quantumDuration path.2
  have packedZero : _ = (0 : Nat) := packed.trans rfl
  have outer := Recovery.Parameters.sequential_depth
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ((EllipticCurve.CandidateCheck.Native.retainPersistent (model := .quantum AlgorithmGate.model
      .empty BitWord.model services) ctx 256 260).seq
      (original.scopedAttemptsFinalized (services := services) 3))
    (EllipticCurve.CandidateCheck.Native.packBatchResult (model := .quantum AlgorithmGate.model
      .empty BitWord.model services) ctx 256 260)
    Resource.Event.quantumDuration path
  have inner := Recovery.Parameters.sequential_depth
    (EllipticCurve.CandidateCheck.Native.retainPersistent (model := .quantum AlgorithmGate.model
      .empty BitWord.model services) ctx 256 260)
    (original.scopedAttemptsFinalized (services := services) 3) Resource.Event.quantumDuration
      path.1
  rw [inner, retained, packedZero, Nat.zero_add, Nat.add_zero] at outer
  exact outer.le.trans repeated

/-- Terminal physical reset does not increase the modeled classical-operation budget. -/
lemma scopedAttemptsFinalized_classical_le (count : Nat)
    (path : (original.scopedAttemptsFinalized (services := services) count).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((original.scopedAttemptsFinalized (services := services) count).resourcePool path) ≤
        count * 6762727521 := by
  unfold scopedAttemptsFinalized at path ⊢
  apply withFrame_weightedCount_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    _ 256 256 _ Resource.Event.classicalOperationWeight (count * 6762727521) ?_ path
  intro inner lift same frame fresh selected
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  exact inputs.finalizedInnerBody_classical_le (services := services)
    sampler checkers count selected

/-- The full terminally cleaned run has the same modeled classical-operation limit. -/
lemma runFinalized_classical_le
    (path : (original.runFinalized (services := services)).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((original.runFinalized (services := services)).code.resourcePool path) ≤
        20288182564 := by
  unfold runFinalized at path ⊢
  have repeated := original.scopedAttemptsFinalized_classical_le
    (services := services) 3 path.1.2
  have packed : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((EllipticCurve.CandidateCheck.Native.packBatchResult (model := .quantum AlgorithmGate.model
        .empty BitWord.model services) ctx 256 260).resourcePool path.2) = 1 := by
    rw [EllipticCurve.CandidateCheck.Native.packBatchResult_resourcePool]
    rfl
  rw [Recovery.Parameters.sequential_pool, ResourcePool.weightedCount_add,
    Recovery.Parameters.sequential_pool, ResourcePool.weightedCount_add,
    EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    ResourcePool.weightedCount_zero, packed, Nat.zero_add]
  exact Nat.add_le_add_right repeated 1

end

end Storage.Inputs

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
