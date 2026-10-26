/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Prepared
import all QuantumAlg.Core.Base.Gate.Effect.Bounds
import all QuantumAlg.Core.Base.Gate.Effect.FixedInput
import all QuantumAlg.Core.Execution.Circuit.Support
import all QuantumAlg.Core.Execution.Instrument.Observation

/-!
# Actual post-restart observations from uniform pure-reference bounds

Each original positive-mass restart block is tested
with the same pulled-back observable; zero blocks contribute zero. The
conclusion retains every HiddenState and History and the full input mass.
The pure bound is an internal obligation, to be discharged by the actual
sampler theorem before constructing the final algorithm contract.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Inputs

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma pure_input_observation {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel}
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (decision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (record : Store ctx × (services.HiddenState × History))
    (observed : Store ctx → Effect (ctx.register.prod Reference))
    (seed : ctx.register.Index) (reference : NormalizedVector Reference) :
    storeEffectWeight code environment
        (@ExecutionState.ofValue _ _ _ decision record (DensityOperator.ofPure
          (NormalizedVector.prodTensor (NormalizedVector.ket seed) reference))) observed =
      (Effect.basisSliceEffect
        (code.effectPullback environment Reference (fun entry => observed entry.1) record)
        seed).weight (DensityOperator.ofPure reference) := by
  unfold storeEffectWeight
  rw [Circuit.effectWeight_execute, ExecutionState.effectWeight_ofValue_decision]
  exact (Effect.basisSliceEffect_weight_of_pure _ seed reference
    (NormalizedVector.prodTensor (NormalizedVector.ket seed) reference)
    (fun _ _ => rfl)).symm

private lemma observed_weight_lower_of_blocks {Record : Type} [Fintype Record] {R : Register}
    (state : ExecutionState Record R) (observed : Record → Effect R) (lower : ℝ)
    (bound : ∀ record, 0 < (state.block record).mass →
      (state.block record).mass * lower ≤ (observed record).weight (state.block record)) :
    state.mass * lower ≤ state.effectWeight observed := by
  unfold ExecutionState.mass ExecutionState.effectWeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro record _
  by_cases positive : 0 < (state.block record).mass
  · exact bound record positive
  · have zero : (state.block record).mass = 0 :=
      le_antisymm (le_of_not_gt positive) (state.block record).mass_nonneg
    rw [zero, zero_mul]
    exact (observed record).weight_nonneg (state.block record)

private def restartThenObservedLowerStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx)
    (output : CWriteRef ctx (.finite 2))
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx true)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (observed : Store ctx → Effect (ctx.register.prod Reference)) (lower : ℝ)
    (_bound : ∀ record : Store ctx × (services.HiddenState ×
        (History × (original.restart (services := services) output).Path)),
      0 < (original.restartBlock output environment state record).mass →
      ∀ reference : NormalizedVector Reference,
        lower ≤ storeEffectWeight code environment
          (ExecutionState.ofValue record (DensityOperator.ofPure
            (NormalizedVector.prodTensor
              (NormalizedVector.ket (original.restartSeed output)) reference))) observed),
    lower * state.mass ≤ storeEffectWeight
      ((original.restart (services := services) output).seq code) environment state observed

private lemma restartThenObservedLower_proof : restartThenObservedLowerStatement := by
  intro ctx services original output code environment Reference History inst state observed lower
    bound
  let restarted :=
    (original.restart (services := services) output).execute environment Reference state
  let pulled : Circuit.EffectFamily ctx Reference
      (services.HiddenState ×
        (History × (original.restart (services := services) output).Path)) :=
    code.effectPullback environment Reference (fun record => observed record.1)
  have observation := code.effectWeight_execute environment Reference restarted
    (fun record => observed record.1)
  change lower * state.mass ≤
    (((original.restart (services := services) output).seq code).execute
      environment Reference state).effectWeight (fun record => observed record.1)
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]
  change lower * state.mass ≤
    (code.execute environment Reference restarted).effectWeight (fun record => observed record.1)
  rw [observation]
  have mass : restarted.mass = state.mass :=
    (original.restart (services := services) output).execute_mass environment Reference state
  rw [← mass]
  rw [mul_comm lower restarted.mass]
  apply observed_weight_lower_of_blocks restarted pulled lower
  intro record positive
  apply original.restart_block_weight_lower output environment state record
    (pulled record) lower
  intro reference
  have pureBound := bound record positive reference
  refine pureBound.trans_eq ?_
  dsimp only [pulled]
  exact pure_input_observation code environment _ record observed
    (original.restartSeed output) reference

/-- An actual restart's conditional mixed blocks inherit the same actual pure-reference bound. -/
lemma restart_then_observed_lower {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx)
    (output : CWriteRef ctx (.finite 2))
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx true)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (observed : Store ctx → Effect (ctx.register.prod Reference)) (lower : ℝ)
    (bound : ∀ record : Store ctx × (services.HiddenState ×
        (History × (original.restart (services := services) output).Path)),
      0 < (original.restartBlock output environment state record).mass →
      ∀ reference : NormalizedVector Reference,
        lower ≤ storeEffectWeight code environment
          (ExecutionState.ofValue record (DensityOperator.ofPure
            (NormalizedVector.prodTensor
              (NormalizedVector.ket (original.restartSeed output)) reference))) observed) :
    lower * state.mass ≤ storeEffectWeight
      ((original.restart (services := services) output).seq code) environment state observed := by
  exact restartThenObservedLower_proof original output code environment state observed lower bound

end

end Storage.Inputs

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
