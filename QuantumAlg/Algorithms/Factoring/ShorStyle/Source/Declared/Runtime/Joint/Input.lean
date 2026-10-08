/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Joint
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame

/-!
# Joint source sampling with the complete parameter and earlier real operands

The conditional Born outcome carries the same actual sampled parameter and
any earlier structural input. All reference coefficients remain conditional
on that original input, allowing real persistent feedback to enter the next
round without assuming an independent or newly initialized store.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Read an earlier operand underneath this iteration's actual retained allocations. -/
def iterationInput {shape : CShape} (ctx : RuntimeCtx .quantum) (N : Nat)
    (observed : CInputRef ctx shape) : CInputRef (Iteration.context ctx N) shape :=
  Storage.liftInput (Iteration.sampledContext ctx N) N
    (Sampler.Retained.liftInput (N := N) observed)

/-- The joint original input, sampled parameter and sampled bits are all actual structural reads. -/
def iterationOperands {shape : CShape} (ctx : RuntimeCtx .quantum) (N : Nat)
    (observed : CInputRef ctx shape) :
    CInputRef (Iteration.context ctx N)
      (.product shape (.product (ParameterShape (modulusBits N))
        (.bits (residueSamplingBits N)))) :=
  .product (iterationInput ctx N observed)
    (.product (Iteration.parameterInput ctx N) (Iteration.sampleInput ctx N))

/-- The actual Born law retains original operands and the complete sampled parameter jointly. -/
theorem iteration_outcome_reference_input (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    {shape : CShape} (observed : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (weight : (CShape.product shape (.product (ParameterShape (modulusBits N))
      (.bits (residueSamplingBits N)))).Value → ℂ)
    (outcome : Fin (phaseBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Iteration.code ctx N input sameWires).execute Reference state)
      (fun entry _ => weight (entry.1.read (iterationOperands ctx N observed)) *
        (if entry.1.read (Iteration.phaseInput ctx N) = CShape.Value.bits outcome then 1 else 0))
      leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (.product (entry.1.read observed)
              (.product (parameterValue input sample) (.bits (Sampler.PackedSample.storedBits
                sample)))) * ((sourceSampleOutcomePMF input sample outcome).toReal : ℂ)))
        leftRef rightRef := by
  let sampled := (Sampler.Retained.circuit (model := executionModel input) ctx N).execute
    Reference state
  let parameter := CInputRef.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef
  let operands := CInputRef.product (Sampler.Retained.liftInput (N := N) observed)
    (.product parameter (.storage (Sampler.Retained.sampleRef ctx N).toCStorageRef))
  have sampleSeed := Sampler.Retained.samplerRetained_seeded
    (model := executionModel input) (ctx := ctx) input ctx.quantumLayout.zeroLabel state seeded
  have sequence := Circuit.referenceFiberSum_execute_seq
    (Sampler.Retained.circuit (model := executionModel input) ctx N)
    (Runtime.code (Sampler.Retained.context ctx N) N input
      ((Iteration.sampled_quantumWires ctx N).trans sameWires) parameter) state
    (fun store => weight (store.read (iterationOperands ctx N observed)) *
      (if store.read (Iteration.phaseInput ctx N) = CShape.Value.bits outcome then 1 else 0))
    leftRef rightRef
  have measured := code_outcome_weighted_reference (Sampler.Retained.context ctx N) N input
    ((Iteration.sampled_quantumWires ctx N).trans sameWires) parameter operands weight
    sampled sampleSeed outcome leftRef rightRef
  dsimp only [operands] at measured
  rw [observation_liftInput_product, observation_liftInput_product] at measured
  have sampledLaw := Sampler.Retained.samplerRetained_reference_input
    (model := executionModel input) (ctx := ctx) input observed state
    (fun old value sample => weight (.product old (.product value sample)) *
      sourceWeight N input value outcome) leftRef rightRef
  refine sequence.trans (measured.trans (sampledLaw.trans ?_))
  apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry basis
  apply Finset.sum_congr rfl
  intro sample _
  rw [sampled_sourceWeight]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
