/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Widths
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Lift

/-! # Actual chronological sums through the allocating window sequence -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Parameters

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

private lemma depth_zero_of_id {model : ExecutionModel} {inner : RuntimeCtx model.kind}
    {allocation : Bool} (code : Circuit model inner inner allocation)
    (same : code = Circuit.id (model := model) (allowAllocation := allocation) inner)
    (duration : Resource.Event model → Nat) (path : code.Path) : code.depth duration path = 0 := by
  cases same
  rfl

attribute [local irreducible] Circuit.depth UnitaryCircuit.evaluatedEventDepth
attribute [local implicit_reducible] block sequence

/-- Both resets really measure each active system, beside all2048 point-middle measurements. -/
lemma block_measurement_count (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((parameters.block index).resourcePool path) =
        2048 + 2 * (index.lowerWidth + 1) := by
  have reset := parameters.reset_measurement_count index path.1
  have point := (parameters.pointParameters index).circuit_measurement_count parameters.frame
    parameters.modulus index.row (parameters.pointPath index path)
  have fourier := QuantumFourierTransform.Semiclassical.Window.inverseCode_measurement_count
    (operations := BitWord.model) (services := services) (parameters.ports index)
      (parameters.fourierPath index path)
  rw [block_resourcePool]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, reduceCtorEq, ↓reduceIte, Nat.mul_zero, reset, point, fourier,
    Nat.zero_add]
  omega

private lemma block_preparation_quantumTime_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := services) (QuantumFourierTransform.Semiclassical.Window.preparation
        (index.lowerWidth + 1) (parameters.ports index))).depth
          Resource.Event.quantumDuration path.2.1 ≤ index.lowerWidth + 1 := by
  have exactPool :
      (Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
        (classicalOracles := services) (QuantumFourierTransform.Semiclassical.Window.preparation
          (index.lowerWidth + 1) (parameters.ports index))).resourcePool path.2.1 =
        (index.lowerWidth + 1) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          (.gate .singleQubit) := by
    change ResourcePool.ofList
      ((QuantumFourierTransform.Semiclassical.Window.preparation
        (index.lowerWidth + 1) (parameters.ports index)).eventTrace BitWord.model services) = _
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services, preparation_pool]
  have actual := Circuit.depth_le_weightedCount_of_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) _
    Resource.Event.quantumDuration _ path.2.1 exactPool.le
  simpa only [ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.quantumDuration, Nat.one_mul, Nat.mul_one] using actual

/-- The literal four sequential components retain their true dependency time allowances. -/
lemma block_quantumTime_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (parameters.block index).depth Resource.Event.quantumDuration path ≤
      (parameters.pointParameters index).quantumTimeLimit +
        parameters.fourierSingleLimit index + 2 * (index.lowerWidth + 1) := by
  have reset := parameters.reset_quantumTime_le index path.1
  have prepare := parameters.block_preparation_quantumTime_le index path
  have point := (parameters.pointParameters index).circuit_quantumTime_le parameters.frame
    parameters.modulus index.row (parameters.pointPath index path)
  have fourier := QuantumFourierTransform.Semiclassical.Window.inverseCode_quantumTime_le
    (operations := BitWord.model) (services := services) (parameters.ports index)
      (parameters.fourierPath index path)
  have lifted := QuantumFourierTransform.Semiclassical.Window.window_liftedInverse_quantumTime
    (operations := BitWord.model) (services := services) (allowAllocation := true)
    (parameters.ports index) (parameters.fourierPath index path)
  change (QuantumFourierTransform.Semiclassical.Window.liftedInverse
      (operations := BitWord.model) (services := services) (allowAllocation := true)
      (parameters.ports index)).depth Resource.Event.quantumDuration
        (parameters.fourierPath index path) = _ at lifted
  rcases path with ⟨resetPath, preparationPath, middlePath, readoutPath⟩
  simp only [pointPath, fourierPath] at point fourier lifted
  dsimp only at reset prepare
  unfold Circuit.quantumTime at lifted
  unfold block
  rw [Circuit.depth_seq, Circuit.depth_seq, Circuit.depth_seq, lifted]
  change _ ≤ (parameters.pointParameters index).quantumTimeLimit +
    parameters.fourierSingleLimit index + 2 * (index.lowerWidth + 1)
  change _ ≤ parameters.fourierSingleLimit index at fourier
  omega

/-- Actual phase selection, H and physical resets add no native classical instruction. -/
lemma block_classical_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((parameters.block index).resourcePool path) ≤
        (parameters.pointParameters index).classicalLimit := by
  have reset := ResourcePool.weightedCount_mono
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    Resource.Event.classicalOperationWeight (parameters.reset_pool_le index path.1)
  have fourier := ResourcePool.weightedCount_mono
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    Resource.Event.classicalOperationWeight
    (QuantumFourierTransform.Semiclassical.Window.inverseCode_pool_le
      (operations := BitWord.model) (services := services) (parameters.ports index)
        (parameters.fourierPath index path))
  have point := (parameters.pointParameters index).circuit_classical_le parameters.frame
    parameters.modulus index.row (parameters.pointPath index path)
  simp only [ResourcePool.scale, Cleanup.Parameters.oneBudget,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight,
    Nat.mul_zero, Nat.add_zero] at reset fourier
  rw [block_resourcePool]
  simp only [ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight,
    Nat.mul_zero, Nat.zero_add]
  omega

/-- Native allowances add along each actual list path, retaining every table allocation. -/
lemma sequence_count_le
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (limit : WindowIndex → Nat)
    (bounded : ∀ index (path : (parameters.block (services := services) index).Path),
      ResourcePool.count focus ((parameters.block index).resourcePool path) ≤ limit index)
    (indices : List WindowIndex)
    (path : (parameters.sequence (services := services) indices).Path) :
    ResourcePool.count focus ((parameters.sequence indices).resourcePool path) ≤
      (indices.map limit).sum := by
  induction indices with
  | nil => exact le_rfl
  | cons index rest ih =>
      change ResourcePool.count focus ((parameters.block index).resourcePool path.1 +
        (parameters.sequence rest).resourcePool path.2) ≤
          limit index + (rest.map limit).sum
      rw [ResourcePool.count_add]
      exact Nat.add_le_add (bounded index path.1) (ih path.2)

/-- A constant occurrence law remains exact through the same actual list execution. -/
lemma sequence_count_eq
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (amount : WindowIndex → Nat)
    (exactCount : ∀ index (path : (parameters.block (services := services) index).Path),
      ResourcePool.count focus ((parameters.block index).resourcePool path) = amount index)
    (indices : List WindowIndex)
    (path : (parameters.sequence (services := services) indices).Path) :
    ResourcePool.count focus ((parameters.sequence indices).resourcePool path) =
      (indices.map amount).sum := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      change ResourcePool.count focus ((parameters.block index).resourcePool path.1 +
        (parameters.sequence rest).resourcePool path.2) =
          amount index + (rest.map amount).sum
      rw [ResourcePool.count_add]
      exact congrArg₂ (fun first second : Nat => first + second)
        (exactCount index path.1) (ih path.2)

/-- Classical charges add as classical work on precisely the same chronological paths. -/
lemma sequence_weight_le
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services) → Nat)
    (limit : WindowIndex → Nat)
    (bounded : ∀ index (path : (parameters.block (services := services) index).Path),
      ResourcePool.weightedCount weight ((parameters.block index).resourcePool path) ≤ limit index)
    (indices : List WindowIndex)
    (path : (parameters.sequence (services := services) indices).Path) :
    ResourcePool.weightedCount weight ((parameters.sequence indices).resourcePool path) ≤
      (indices.map limit).sum := by
  induction indices with
  | nil => exact le_rfl
  | cons index rest ih =>
      change ResourcePool.weightedCount weight ((parameters.block index).resourcePool path.1 +
        (parameters.sequence rest).resourcePool path.2) ≤
          limit index + (rest.map limit).sum
      rw [ResourcePool.weightedCount_add]
      exact Nat.add_le_add (bounded index path.1) (ih path.2)

/-- Actual chronological dependency times add before independent per-window bounds are applied. -/
lemma sequence_depth_le
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services) → Nat)
    (limit : WindowIndex → Nat)
    (bounded : ∀ index (path : (parameters.block (services := services) index).Path),
      (parameters.block index).depth duration path ≤ limit index)
    (indices : List WindowIndex)
    (path : (parameters.sequence (services := services) indices).Path) :
    (parameters.sequence indices).depth duration path ≤ (indices.map limit).sum := by
  induction indices with
  | nil =>
      exact (depth_zero_of_id (parameters.sequence (services := services) [])
        (parameters.sequence_nil (services := services)) duration path).le
  | cons index rest ih =>
      have split : (parameters.sequence (services := services) (index :: rest)).depth
          duration path = (parameters.block (services := services) index).depth duration path.1 +
            (parameters.sequence (services := services) rest).depth duration path.2 :=
        Circuit.depth_seq (parameters.block (services := services) index)
          (parameters.sequence (services := services) rest) duration path.1 path.2
      rw [split]
      exact Nat.add_le_add (bounded index path.1) (ih path.2)

end

end Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
