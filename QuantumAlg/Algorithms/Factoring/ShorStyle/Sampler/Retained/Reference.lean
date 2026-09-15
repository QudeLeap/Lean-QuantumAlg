/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Execution
import all QuantumAlg.Core.Execution.Random.Observation

/-!
# Actual sampler source weights retain every reference coordinate

The native sampler's complete result store is weighted by the same uniform
source integer that its real random instruction draws. Reading the parameter
and original sample therefore uses one source, including early-factor data.
These identities retain every original caller store block and both external
reference coordinates; no normalization or independence premise is needed.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The complete mathematical store contains the actual source bits in its retained sample cell. -/
theorem samplerRetained_resultStore_sample (input : Input N) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    (resultStore input store value).read (FirstAccepted.cellRead (sampleRef ctx N)) =
      .bits (PackedSample.storedBits value) :=
  (congrArg
    (fun output : Store (context ctx N) =>
      output.read (FirstAccepted.cellRead (sampleRef ctx N)))
    (samplerRetained_result_store input store value).symm).trans
    (samplerRetained_outcome_sample (pushStore N store) value)

/-- The retained parameter and source bits originate from the identical actual random draw. -/
theorem samplerRetained_resultStore_parameter (input : Input N) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    (resultStore input store value).read (FirstAccepted.cellRead (parameterRef ctx N)) =
      parameterValue input value :=
  (congrArg
    (fun output : Store (context ctx N) =>
      output.read (FirstAccepted.cellRead (parameterRef ctx N)))
    (samplerRetained_result_store input store value).symm).trans
    (samplerRetained_outcome_parameter input (pushStore N store) value)

/-- Actual retained sampling transports any complete-store weight to its genuine uniform source. -/
theorem samplerRetained_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store (context ctx N) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((circuit ctx N).execute Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (resultStore input entry.1 value)) leftRef rightRef := by
  let count : ℕ+ := ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩
  let update := fun entry : (Store ctx × History) × Fin count =>
    (resultStore input entry.1.1 entry.2,
      (entry.1.2, resultPath ctx N entry.1.1 entry.2))
  have executed := congrArg
    (fun output : State (context ctx N) Reference (History × (circuit ctx N).Path) =>
      ExecutionState.referenceFiberSum output (fun entry _ => weight entry.1)
        leftRef rightRef)
    (samplerRetained_execute ctx input Reference state)
  have pushed := ExecutionState.referenceFiberSum_mapClassical (uniformChoice state count)
    update (fun entry _ => weight entry.1) leftRef rightRef
  have sampled := referenceFiberSum_uniformChoice state count
    (fun entry _ => weight (update entry).1) leftRef rightRef
  have coefficient : (((count : ℝ)⁻¹ : ℝ) : ℂ) =
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) := by
    rw [Complex.ofReal_inv]
    exact congrArg (fun number : ℝ => (number : ℂ)⁻¹)
      (show (count : ℝ) = ((2 ^ residueSamplingBits N : Nat) : ℝ) from rfl)
  refine executed.trans (pushed.trans (sampled.trans ?_))
  apply congrArg
    (fun observe : (Store ctx × History) → ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry basis
  apply Finset.sum_congr rfl
  intro value _
  exact congrArg
    (fun scalar : ℂ => scalar * weight (resultStore input entry.1 value)) coefficient

/-- Joint parameter/sample weights preserve the full reference operator of the same source draw. -/
theorem samplerRetained_parameter_sample_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (weight : (ParameterShape (modulusBits N)).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((circuit ctx N).execute Reference state)
        (fun entry _ => weight
          (entry.1.read (FirstAccepted.cellRead (parameterRef ctx N)))
          (entry.1.read (FirstAccepted.cellRead (sampleRef ctx N)))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (parameterValue input value) (.bits (PackedSample.storedBits value)))
        leftRef rightRef := by
  refine (samplerRetained_reference input state
    (fun store => weight (store.read (FirstAccepted.cellRead (parameterRef ctx N)))
      (store.read (FirstAccepted.cellRead (sampleRef ctx N)))) leftRef rightRef).trans ?_
  apply congrArg
    (fun observe : (Store ctx × History) → ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry basis
  apply Finset.sum_congr rfl
  intro value _
  rw [samplerRetained_resultStore_parameter, samplerRetained_resultStore_sample]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
