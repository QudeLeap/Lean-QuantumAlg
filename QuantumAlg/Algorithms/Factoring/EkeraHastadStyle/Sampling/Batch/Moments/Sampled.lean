/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Repetition.Semantics
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Initialization.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Reference

/-!
# The complete native batch uses the actual sampler's same-source distribution

The one-time preparation is eliminated only from weighted observations of
earlier structural inputs, using its proved full-reference preservation law.
The remaining sampler is its actual instruction sequence. Thus its parameter,
original source bits and all sixteen outcomes share exactly the original
uniform draw, with the conditional vector PMF proved from the real rounds.
Both external-reference coordinates remain arbitrary throughout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open ShortDLP.CompiledMAU
open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def conditionalMoment {N : Nat} {previousShape : CShape}
    (weight : (ParameterShape N).Value → previousShape.Value →
      (Fin 16 → (CShape.bits (measurementBits N)).Value) → ℂ)
    (parameter : (ParameterShape N).Value) (previous : previousShape.Value) : ℂ :=
  ∑ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
    ((PMF.independentReplicateVector
      ((ShortDLP.measurement (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N))).outcomePMF
        (evolvedState (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
          (parameterUnit parameter) (parameterTarget parameter))) 16 samples).toReal : ℂ) *
      weight parameter previous (fun index => .bits (samples.get index))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Complete round observations refer to the same actual sampler state before bank preparation. -/
lemma nativeBatch_sampled_weighted_reference {previousShape : CShape}
    (previous : CInputRef (sampledContext base N) previousShape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (weight : (ParameterShape N).Value → previousShape.Value →
      (Fin 16 → (CShape.bits (measurementBits N)).Value) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N).execute environment Reference state)
        (fun entry _ => weight (entry.1.read (finalParameter base noQuantum N))
          (entry.1.read (finalInput base noQuantum N previous))
          (entry.1.read (finalResults base noQuantum N)).get) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((ShorStyle.Canonical.Sampler.Retained.circuit
          (model := RuntimeRound.model) base N).execute environment Reference state)
        (fun entry _ => conditionalMoment weight
          (entry.1.read (.storage
            (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef))
          (entry.1.read previous)) leftRef rightRef := by
  let parameterInput : CInputRef (sampledContext base N) (ParameterShape N) :=
    .storage (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef
  let jointWeight := fun value : (CShape.product (ParameterShape N) previousShape).Value =>
    conditionalMoment weight value.first value.second
  have initializeLaw := nativeBatch_initialize_reference_input (environment := environment)
    base noQuantum N
    (.product parameterInput previous) state jointWeight leftRef rightRef
  have jointRead (store : Store (readyContext base noQuantum N)) :
      store.read (readyInput base noQuantum N (.product parameterInput previous)) =
        .product (store.read (parameter base noQuantum N))
          (store.read (readyInput base noQuantum N previous)) :=
    congrArg (fun input : CInputRef (readyContext base noQuantum N)
        (.product (ParameterShape N) previousShape) => store.read input)
      (nativeBatch_readyInput_product base noQuantum N parameterInput previous)
  have aligned := congrArg
    (fun observe : (Store (readyContext base noQuantum N) ×
        (RuntimeRound.model.HiddenState ×
          (History × (initializeBank base noQuantum N).Path))) →
        (readyContext base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum ((initializeBank base noQuantum N).execute
        environment Reference state)
        observe leftRef rightRef)
    (show (fun entry _ => conditionalMoment weight
        (entry.1.read (parameter base noQuantum N))
        (entry.1.read (readyInput base noQuantum N previous))) =
      (fun entry _ => jointWeight
        (entry.1.read (readyInput base noQuantum N (.product parameterInput previous)))) from by
      funext entry basis
      exact (congrArg jointWeight (jointRead entry.1)).symm)
  exact (nativeBatch_complete_weighted_reference base noQuantum N previous state weight
    leftRef rightRef).trans (aligned.trans initializeLaw)

/-- The actual batch's complete joint reference weight has one uniform source and sixteen draws. -/
lemma nativeBatch_source_weighted_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value →
      (Fin 16 → (CShape.bits (measurementBits N)).Value) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N).execute environment Reference state)
        (fun entry _ => weight (entry.1.read (finalParameter base noQuantum N))
          (entry.1.read (finalSample base noQuantum N))
          (entry.1.read (finalResults base noQuantum N)).get) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            conditionalMoment weight (parameterValue input value)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
        leftRef rightRef :=
  (nativeBatch_sampled_weighted_reference base noQuantum N
    (.storage (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef)
    state weight leftRef rightRef).trans
    (ShorStyle.Canonical.Sampler.Retained.samplerRetained_parameter_sample_reference
      (model := RuntimeRound.model) input.samplerInput state
      (conditionalMoment weight) leftRef rightRef)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
