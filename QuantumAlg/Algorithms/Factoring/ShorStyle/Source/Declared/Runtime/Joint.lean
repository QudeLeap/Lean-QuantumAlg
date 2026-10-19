/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Sampling
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Reference
import all QuantumAlg.Core.Execution.Preparation.Observation

/-!
# Actual Shor source sample and conditional measurement jointly

The sample retained by the native random instruction is precisely the draw
that selects the granted member. Its actual phase output has the original
conditional Born law with every external-reference coefficient preserved.
The owned preparation is part of the same actual program.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual parameter chosen by a source draw has the original conditional Born probability. -/
lemma sampled_sourceWeight {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (outcome : Fin (phaseBits N) → Bool) :
    sourceWeight N input (parameterValue input sample) outcome =
      ((sourceSampleOutcomePMF input sample outcome).toReal : ℂ) :=
  congrArg (fun distribution : PMF (TerminalZMeasure.Outcome (phaseBits N)) =>
    ((distribution outcome).toReal : ℂ)) (DeclaredSource.sample_outcomePMF_eq input sample)

/-- Actual sampling and selected measurement share one source draw in every reference fiber. -/
lemma iteration_outcome_reference (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (weight : (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcome : Fin (phaseBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Iteration.code ctx N sameWires).execute (environment input) Reference state)
      (fun entry _ => weight (entry.1.read (Iteration.sampleInput ctx N)) *
        (if entry.1.read (Iteration.phaseInput ctx N) = CShape.Value.bits outcome then 1 else 0))
      leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (.bits (Sampler.PackedSample.storedBits sample)) *
              ((sourceSampleOutcomePMF input sample outcome).toReal : ℂ))) leftRef rightRef := by
  let sampled := (Sampler.Retained.circuit (model := executionModel N) ctx N).execute
    (environment input) Reference state
  let parameter : CInputRef (Sampler.Retained.context ctx N)
      (ParameterShape (modulusBits N)) :=
    .storage (Sampler.Retained.parameterRef ctx N).toCStorageRef
  let observed : CInputRef (Sampler.Retained.context ctx N)
      (.bits (residueSamplingBits N)) :=
    .storage (Sampler.Retained.sampleRef ctx N).toCStorageRef
  have sampleSeed := Sampler.Retained.samplerRetained_seeded (environment := environment input)
    (model := executionModel N) (ctx := ctx) input ctx.quantumLayout.zeroLabel state seeded
  have sequence := Circuit.referenceFiberSum_execute_seq (environment := environment input)
    (Sampler.Retained.circuit (model := executionModel N) ctx N)
    (Runtime.code (Sampler.Retained.context ctx N) N
      ((Iteration.sampled_quantumWires ctx N).trans sameWires) parameter) state
    (fun store => weight (store.read (Iteration.sampleInput ctx N)) *
      (if store.read (Iteration.phaseInput ctx N) = CShape.Value.bits outcome then 1 else 0))
    leftRef rightRef
  have measured := code_outcome_weighted_reference (Sampler.Retained.context ctx N) N input
    ((Iteration.sampled_quantumWires ctx N).trans sameWires) parameter observed weight
    sampled sampleSeed outcome leftRef rightRef
  have sampledLaw := Sampler.Retained.samplerRetained_parameter_sample_reference
    (environment := environment input)
    (model := executionModel N) (ctx := ctx) input state
    (fun value sample => weight sample * sourceWeight N input value outcome) leftRef rightRef
  refine sequence.trans (measured.trans (sampledLaw.trans ?_))
  apply congrArg (fun observe =>
    ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry basis
  apply Finset.sum_congr rfl
  intro sample _
  rw [sampled_sourceWeight]

/-- The actual owned preparation and full first iteration have the original joint source weights. -/
lemma sampling_outcome_reference (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History))
    (weight : (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcome : Fin (phaseBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Sampling.code base noQuantum N).execute (environment input) Reference state)
      (fun entry _ => weight
        (entry.1.read (Iteration.sampleInput (bankContext base noQuantum N) N)) *
        (if entry.1.read (Iteration.phaseInput (bankContext base noQuantum N) N) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (.bits (Sampler.PackedSample.storedBits sample)) *
              ((sourceSampleOutcomePMF input sample outcome).toReal : ℂ))) leftRef rightRef := by
  let coefficient : ℂ := ∑ sample : Fin (2 ^ residueSamplingBits N),
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
      (weight (.bits (Sampler.PackedSample.storedBits sample)) *
        ((sourceSampleOutcomePMF input sample outcome).toReal : ℂ))
  have sequence := Circuit.referenceFiberSum_execute_seq (environment := environment input)
    (Sampling.prepare base noQuantum N)
    (Iteration.code (bankContext base noQuantum N) N
      (bankContext_wires base noQuantum N)) state
    (fun store => weight
      (store.read (Iteration.sampleInput (bankContext base noQuantum N) N)) *
      (if store.read (Iteration.phaseInput (bankContext base noQuantum N) N) =
        CShape.Value.bits outcome then 1 else 0)) leftRef rightRef
  have sampled := iteration_outcome_reference (bankContext base noQuantum N) N input
    (bankContext_wires base noQuantum N)
    ((Sampling.prepare base noQuantum N).execute (environment input) Reference state)
    (sampling_prepare_seeded
      (environment := environment input) base noQuantum N state) weight outcome leftRef rightRef
  have prepared := Circuit.referenceFiberSum_execute_prepareZero (environment := environment input)
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N) state (fun _ => coefficient) leftRef rightRef
  exact sequence.trans (sampled.trans prepared)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
