/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Layout.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Distribution.Weights
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame

/-!
# A fresh source and sixteen reused-bank rounds retain the full joint reference law

The actual sampler draws the new source and computes its parameter. Its real
continuation uses the existing seeded bank for sixteen member and measurement
rounds. An earlier structural operand may be observed jointly whenever its
storage keys avoid the measurement cells that these rounds really overwrite.
The identity retains both arbitrary external-reference coordinates, including
all correlations with that protected operand. The seed premise is the internal
complete-store invariant produced and restored by the preceding actual code.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Consume the proved lift laws without expanding sixteen dependent retention transports.
attribute [local irreducible] RuntimeResults.context RuntimeResults.liftInput RuntimeResults.input

variable (base : RuntimeCtx .quantum) (N : Nat)
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

private lemma rounds_weighted_reference
    {previousShape : CShape} (previous : CInputRef base previousShape)
    (distinct : Function.Injective (fun index => (originalCells index).key))
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext base N) Reference (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatchReuse_sampled_wires base N sameWires) N state)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value →
      previousShape.Value → (Fin 16 → (CShape.bits (measurementBits N)).Value) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((rounds base N sameWires originalCells).execute environment Reference state)
        (fun entry _ => weight (entry.1.read (finalParameter base N))
          (entry.1.read (finalSample base N)) (entry.1.read (callerInput base N previous))
          (entry.1.read (finalResults base N)).get) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => NativeBatch.conditionalMoment
          (fun parameter sample outcomes => weight parameter sample
            (entry.1.read (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) previous))
            outcomes)
          (entry.1.read (parameter base N))
          (entry.1.read (.storage
            (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef)))
        leftRef rightRef := by
  let sample : CInputRef (sampledContext base N) (.bits (residueSamplingBits N)) :=
    .storage (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef
  let earlier := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) previous
  let joint := CInputRef.product sample earlier
  let jointWeight := fun parameter
      (value : (CShape.product (.bits (residueSamplingBits N)) previousShape).Value) outcomes =>
    weight parameter value.first value.second outcomes
  let repeated := (rounds base N sameWires originalCells).execute environment Reference state
  have repetitionLaw := RuntimeRepetition.shortDLP_runtimeRepetition_weighted_reference
    (environment := environment)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N)) 16
    (sampledContext base N) (nativeBatchReuse_sampled_wires base N sameWires)
    (parameter base N) joint (cells base N originalCells)
    (nativeBatchReuse_cells_distinct base N originalCells distinct)
    (nativeBatchReuse_cells_joint_separate base N originalCells previous separate)
    state seeded jointWeight leftRef rightRef
  have jointRefs : finalInput base N joint =
      .product (finalSample base N) (callerInput base N previous) :=
    RuntimeRepetition.liftInput_product (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      sample earlier 16
  have jointRead (store : Store (context base N)) :
      store.read (finalInput base N joint) =
        .product (store.read (finalSample base N)) (store.read (callerInput base N previous)) := by
    have readPair := congrArg (fun operand => store.read operand) jointRefs
    exact readPair
  have aligned := congrArg
    (fun observe : Store (context base N) → ℂ =>
      ExecutionState.referenceFiberSum repeated (fun entry _ => observe entry.1)
        leftRef rightRef)
    (show (fun store => weight (store.read (finalParameter base N))
        (store.read (finalSample base N)) (store.read (callerInput base N previous))
        (store.read (finalResults base N)).get) =
      (fun store => jointWeight (store.read (finalParameter base N))
        (store.read (finalInput base N joint)) (store.read (finalResults base N)).get) from by
      funext store
      exact (congrArg (fun value => jointWeight (store.read (finalParameter base N)) value
        (store.read (finalResults base N)).get) (jointRead store)).symm)
  exact aligned.trans repetitionLaw

/-- Every joint source, earlier operand and outcome weight follows the actual conditional law. -/
lemma nativeBatchReuse_source_weighted_reference (input : Input N)
    {previousShape : CShape} (previous : CInputRef base previousShape)
    (distinct : Function.Injective (fun index => (originalCells index).key))
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N state)
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value →
      previousShape.Value → (Fin 16 → (CShape.bits (measurementBits N)).Value) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base N sameWires originalCells).execute
      environment Reference state)
        (fun entry _ => weight (entry.1.read (finalParameter base N))
          (entry.1.read (finalSample base N)) (entry.1.read (callerInput base N previous))
          (entry.1.read (finalResults base N)).get) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ source : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            NativeBatch.conditionalMoment
              (fun parameter sample outcomes =>
                weight parameter sample (entry.1.read previous) outcomes)
              (parameterValue input source)
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits source)))
        leftRef rightRef := by
  have repetitionLaw := rounds_weighted_reference (environment := environment)
    base N sameWires originalCells previous
    distinct separate
    (Circuit.execute (environment := environment)
      (ShorStyle.Canonical.Sampler.Retained.circuit (model := RuntimeRound.model) base N)
      Reference state)
    (nativeBatchReuse_sampler_seedBlocks input sameWires state seeded) weight leftRef rightRef
  have sampledLaw := ShorStyle.Canonical.Sampler.Retained.samplerRetained_reference_input
    (environment := environment)
    (model := RuntimeRound.model) input.samplerInput previous state
    (fun old parameter sample => NativeBatch.conditionalMoment
      (fun p s outcomes => weight p s old outcomes) parameter sample) leftRef rightRef
  exact (Circuit.referenceFiberSum_execute_seq (environment := environment)
    (ShorStyle.Canonical.Sampler.Retained.circuit (model := RuntimeRound.model) base N)
    (rounds base N sameWires originalCells) state
    (fun store => weight (store.read (finalParameter base N))
      (store.read (finalSample base N)) (store.read (callerInput base N previous))
      (store.read (finalResults base N)).get) leftRef rightRef).trans
    (repetitionLaw.trans sampledLaw)

private lemma fixedVector_eta {count : Nat} {shape : CShape}
    (value : (CShape.fixedVector count shape).Value) : .fixedVector value.get = value := by
  cases value
  rfl

/-- The complete real output and a protected earlier operand have the original source kernel. -/
lemma nativeBatchReuse_output_weighted_reference (input : Input N)
    {previousShape : CShape} (previous : CInputRef base previousShape)
    (distinct : Function.Injective (fun index => (originalCells index).key))
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N state)
    (weight : previousShape.Value → (NativeBatch.resultShape N).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base N sameWires originalCells).execute
      environment Reference state)
        (fun entry _ => weight (entry.1.read (callerInput base N previous))
          ((run base N sameWires originalCells).output.eval entry.1)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ output : (NativeBatch.resultShape N).Value,
          ((NativeBatch.sourceDistribution input output).toReal : ℂ) *
            weight (entry.1.read previous) output) leftRef rightRef := by
  let sourceWeight := fun parameter sample old outcomes =>
    weight old (.product sample (.product parameter (.fixedVector outcomes)))
  have sourceLaw := nativeBatchReuse_source_weighted_reference (environment := environment)
    base N sameWires originalCells
    input previous distinct separate state seeded sourceWeight leftRef rightRef
  have outputRead (store : Store (context base N)) :
      (run base N sameWires originalCells).output.eval store =
        .product (store.read (finalSample base N))
          (.product (store.read (finalParameter base N))
            (store.read (finalResults base N))) := rfl
  have aligned := congrArg
    (fun observe : Store (context base N) → ℂ =>
      ExecutionState.referenceFiberSum
        ((code base N sameWires originalCells).execute environment Reference state)
        (fun entry _ => observe entry.1) leftRef rightRef)
    (show (fun store => weight (store.read (callerInput base N previous))
        ((run base N sameWires originalCells).output.eval store)) =
      (fun store => sourceWeight (store.read (finalParameter base N))
        (store.read (finalSample base N)) (store.read (callerInput base N previous))
        (store.read (finalResults base N)).get) from by
      funext store
      rw [outputRead]
      exact (congrArg (fun outcomes => weight (store.read (callerInput base N previous))
        (.product (store.read (finalSample base N))
          (.product (store.read (finalParameter base N)) outcomes)))
        (fixedVector_eta (store.read (finalResults base N)))).symm)
  have summed := congrArg
    (fun observe : Store base → ℂ =>
      ExecutionState.referenceFiberSum state (fun entry _ => observe entry.1) leftRef rightRef)
    (funext fun store => (NativeBatch.nativeBatch_sourceDistribution_weighted input
      (weight (store.read previous))).symm)
  exact aligned.trans (sourceLaw.trans summed)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse
