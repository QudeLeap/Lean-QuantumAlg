/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Reference
import all QuantumAlg.Core.Execution.Store.Read

/-!
# The actual Shor sampler retains every earlier structural input

The native sampler's two initialized retained cells store its actual source
bits and parameter. Their real fresh keys are separate from every earlier
input. The source draw is therefore independent of earlier classical results
as an actual instruction, while those results keep all their reference
correlations. This is the frame needed when composing real repeated rounds.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

noncomputable section

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- An earlier actual structural input underneath the two retained sampler result cells. -/
def liftInput {shape : CShape} (input : CInputRef ctx shape) : CInputRef (context ctx N) shape :=
  (input.underRetained ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh).underRetained (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh

/-- The actual initialized store extension preserves every earlier input value. -/
lemma pushStore_read_liftInput {shape : CShape} (store : Store ctx)
    (input : CInputRef ctx shape) :
    (pushStore N store).read (liftInput (N := N) input) = store.read input :=
  (Store.read_pushRetained_underRetained _ _ _ _ _).trans
    (Store.read_pushRetained_underRetained _ _ _ _ _)

/-- The source sampler's actual complete result store leaves all earlier input cells intact. -/
lemma resultStore_read_liftInput (source : Input N) {shape : CShape}
    (store : Store ctx) (sample : Fin (2 ^ residueSamplingBits N))
    (input : CInputRef ctx shape) :
    (resultStore source store sample).read (liftInput (N := N) input) = store.read input := by
  let prior : CInputRef (sampleContext ctx N) shape :=
    input.underRetained ctx.canonicalFreshKey (.bits (residueSamplingBits N))
      ctx.canonicalFreshKey_fresh
  have parameterSeparate : (parameterRef ctx N).key ∉ (liftInput (N := N) input).storageKeys :=
    CInputRef.fresh_not_mem_storageKeys_underRetained prior (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh
  have sampleSeparate : (sampleRef ctx N).key ∉ (liftInput (N := N) input).storageKeys := by
    have support : (liftInput (N := N) input).storageKeys = prior.storageKeys :=
      CInputRef.storageKeys_underRetained (ctx := sampleContext ctx N) prior
        (sampleContext ctx N).canonicalFreshKey (ParameterShape (modulusBits N))
        (sampleContext ctx N).canonicalFreshKey_fresh
    have absent : ctx.canonicalFreshKey ∉ prior.storageKeys :=
      CInputRef.fresh_not_mem_storageKeys_underRetained input ctx.canonicalFreshKey
        (.bits (residueSamplingBits N)) ctx.canonicalFreshKey_fresh
    exact (congrArg (fun keys : List StorageKey => ctx.canonicalFreshKey ∉ keys) support).mpr absent
  exact (Store.read_write_of_not_mem_storageKeys _ (parameterRef ctx N)
    (parameterValue source sample) (liftInput (N := N) input) parameterSeparate).trans
    ((Store.read_write_of_not_mem_storageKeys (pushStore N store) (sampleRef ctx N)
      (.bits (PackedSample.storedBits sample)) (liftInput (N := N) input) sampleSeparate).trans
      (pushStore_read_liftInput store input))

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The real uniform sample and parameter retain the joint earlier-input reference weights. -/
lemma samplerRetained_reference_input (source : Input N) {shape : CShape}
    (input : CInputRef ctx shape) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (weight : shape.Value → (ParameterShape (modulusBits N)).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((circuit (model := model) ctx N).execute
      environment Reference state)
        (fun entry _ => weight (entry.1.read (liftInput (N := N) input))
          (entry.1.read (FirstAccepted.cellRead (parameterRef ctx N)))
          (entry.1.read (FirstAccepted.cellRead (sampleRef ctx N)))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (entry.1.read input) (parameterValue source sample)
              (.bits (PackedSample.storedBits sample))) leftRef rightRef := by
  refine (samplerRetained_reference source state
    (fun store => weight (store.read (liftInput (N := N) input))
      (store.read (FirstAccepted.cellRead (parameterRef ctx N)))
      (store.read (FirstAccepted.cellRead (sampleRef ctx N)))) leftRef rightRef).trans ?_
  apply congrArg
    (fun observe : Store ctx × (model.HiddenState × History) → ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry _
  apply Finset.sum_congr rfl
  intro sample _
  rw [resultStore_read_liftInput, samplerRetained_resultStore_parameter,
    samplerRetained_resultStore_sample]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
