/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Resources

/-!
# The same paid active-bank reset before each actual source window

The selected C/W and address systems are genuinely measured and corrected
before H. The existing point output cell is reused. Every original Store,
service state, chronological Path and external reference is retained. Bounds
come from those actual MZ/X events; no qubit or result cell is allocated.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

variable (parameters : Parameters ctx)

/-- Literal identity embedding preserves the complete actual reset execution. -/
lemma reset_execute (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (parameters.reset index).execute environment Reference state =
      (parameters.resetParameters.run (index.lowerWidth + 1)
        (parameters.wire index)).execute environment Reference state :=
  Circuit.execute_identity_embed
    (parameters.resetParameters.run (index.lowerWidth + 1) (parameters.wire index))
      environment Reference state

/-- Every active wire is zero in every actual full output record, for arbitrary input states. -/
lemma reset_supported (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (bit : Fin (index.lowerWidth + 1)) :
    QuditShift.WireSupported (parameters.wire index bit) 0
      ((parameters.reset index).execute environment Reference state) := by
  exact Eq.mpr (congrArg (QuditShift.WireSupported (parameters.wire index bit) 0)
    (parameters.reset_execute index environment Reference state))
      (parameters.resetParameters.run_supported environment (index.lowerWidth + 1)
        (parameters.wire index) state bit)

/-- The actual pre-H word spends at most one X in addition to each mandatory MZ. -/
lemma reset_pool_le (index : WindowIndex)
    (path : (parameters.reset (services := services) index).Path) :
    (parameters.reset index).resourcePool path ≤
      ResourcePool.scale (index.lowerWidth + 1)
        (Cleanup.Parameters.oneBudget (services := services)) := by
  change (parameters.resetParameters.run (index.lowerWidth + 1)
    (parameters.wire index)).resourcePool path ≤ _
  exact Circuit.forRange_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (index.lowerWidth + 1)
    (fun bit => parameters.resetParameters.one (parameters.wire index bit))
    (Cleanup.Parameters.oneBudget (services := services))
    (fun bit current => parameters.resetParameters.one_pool_le
      (parameters.wire index bit) current) path

/-- Every actual path measures each selected physical bank position once. -/
lemma reset_measurement_count (index : WindowIndex)
    (path : (parameters.reset (services := services) index).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((parameters.reset index).resourcePool path) =
        index.lowerWidth + 1 := by
  have actual := Circuit.forRange_event_count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+)) (index.lowerWidth + 1)
    (fun bit => parameters.resetParameters.one (parameters.wire index bit)) 1
    (fun bit current => parameters.resetParameters.one_measurement_count
      (parameters.wire index bit) current) path
  exact actual.trans (Nat.mul_one _)

/-- The native reset introduces no Toffoli or CNOT and at most one X per active wire. -/
lemma reset_native_counts (index : WindowIndex)
    (path : (parameters.reset (services := services) index).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
        ((parameters.reset index).resourcePool path) = 0 ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
          ((parameters.reset index).resourcePool path) = 0 ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
          ((parameters.reset index).resourcePool path) ≤ index.lowerWidth + 1 := by
  have counts := (ResourcePool.le_iff_count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (left := (parameters.reset index).resourcePool path)
    (right := ResourcePool.scale (index.lowerWidth + 1)
      (Cleanup.Parameters.oneBudget (services := services)))).mp
        (parameters.reset_pool_le index path)
  have first := counts (.gate .toffoli)
  have second := counts (.gate .cnot)
  have third := counts (.gate .singleQubit)
  simp only [ResourcePool.count_scale, Cleanup.Parameters.oneBudget, ResourcePool.count_add,
    ResourcePool.count_singleton, reduceCtorEq, ↓reduceIte, Nat.zero_add,
    Nat.mul_one] at first second third
  exact ⟨Nat.eq_zero_of_le_zero first, Nat.eq_zero_of_le_zero second, third⟩

/-- Actual sequential quantum duration is bounded by one correction per selected wire. -/
lemma reset_quantumTime_le (index : WindowIndex)
    (path : (parameters.reset (services := services) index).Path) :
    (parameters.reset index).depth Resource.Event.quantumDuration path ≤
      index.lowerWidth + 1 := by
  have actual := Circuit.depth_le_weightedCount_of_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (parameters.reset index) Resource.Event.quantumDuration
    (ResourcePool.scale (index.lowerWidth + 1)
      (Cleanup.Parameters.oneBudget (services := services))) path
        (parameters.reset_pool_le index path)
  simpa only [ResourcePool.scale, ResourcePool.weightedCount_nsmul,
    Cleanup.Parameters.oneBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, Resource.Event.quantumDuration,
    Nat.mul_zero, Nat.mul_one, Nat.zero_add] using actual

/-- The same physical systems and original classical cells remain resident throughout. -/
lemma reset_peakResidentSpace (index : WindowIndex)
    (path : (parameters.reset (services := services) index).Path) :
    (parameters.reset index).peakResidentSpace path = ctx.residentSpace :=
  Circuit.peakResidentSpace_embed
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (ContextEmbedding.identity ctx)
    (parameters.resetParameters.run (index.lowerWidth + 1) (parameters.wire index)) path

/-- Complete auxiliary space, including every untouched complement system, is unchanged. -/
lemma reset_peakAuxiliarySpace (index : WindowIndex)
    (path : (parameters.reset (services := services) index).Path) :
    (parameters.reset index).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  Circuit.peakAuxiliarySpace_embed
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (ContextEmbedding.identity ctx)
    (parameters.resetParameters.run (index.lowerWidth + 1) (parameters.wire index)) path

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
