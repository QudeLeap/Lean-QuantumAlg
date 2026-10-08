/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Joint.Input
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Readout
import all QuantumAlg.Core.Execution.Reference.Support

/-!
# Original source weights jointly with every earlier actual structural input

The full selected sampling law preserves an arbitrary earlier input jointly
with the original source outcome and every reference matrix entry. This
supplies the conditional law needed for actual persistent success feedback,
rather than assuming that matching single-round marginals imply independence.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem phase_weight_decomposition {shape : CShape} (ctx : RuntimeCtx .quantum)
    (N : Nat) (observed : CInputRef ctx shape)
    (store : Store (Iteration.context ctx N))
    (weight : shape.Value → SourceOutcome N → ℂ) :
    weight (store.read (iterationInput ctx N observed)) (sourceRead ctx N store) =
      ∑ phase : Fin (phaseBits N) → Bool,
        weight (store.read (iterationInput ctx N observed))
          ⟨sampleRead (store.read (Iteration.sampleInput ctx N)), phase⟩ *
            (if store.read (Iteration.phaseInput ctx N) = .bits phase then 1 else 0) := by
  cases measured : store.read (Iteration.phaseInput ctx N) with
  | bits phase =>
      simp only [sourceRead, measured, phaseRead, CShape.Value.bits.injEq,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The actual source law remains jointly conditional on every original real input value. -/
theorem iteration_input_source_reference (ctx : RuntimeCtx .quantum) (N : Nat)
    (input : Input N) (sameWires : ctx.quantumWires = (layout N).wires)
    {shape : CShape} (observed : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (weight : shape.Value → SourceOutcome N → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Iteration.code ctx N input sameWires).execute Reference state)
      (fun entry _ => weight (entry.1.read (iterationInput ctx N observed))
        (sourceRead ctx N entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => SourceWeights.one input (weight (entry.1.read observed))) left right := by
  let actual := (Iteration.code ctx N input sameWires).execute Reference state
  let phaseWeight := fun phase : Fin (phaseBits N) → Bool =>
    fun entry : Store (Iteration.context ctx N) ×
        ((executionModel input).HiddenState ×
          (History × (Iteration.code ctx N input sameWires).Path)) =>
      fun _ : (Iteration.context ctx N).register.Index =>
        weight (entry.1.read (iterationInput ctx N observed))
          ⟨sampleRead (entry.1.read (Iteration.sampleInput ctx N)), phase⟩ *
            (if entry.1.read (Iteration.phaseInput ctx N) = .bits phase then 1 else 0)
  have point (phase : Fin (phaseBits N) → Bool) :
      ExecutionState.referenceFiberSum actual (phaseWeight phase) left right =
        ExecutionState.referenceFiberSum state
          (fun entry _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
            (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
              (weight (entry.1.read observed) ⟨sample, phase⟩ *
                ((sourceSampleOutcomePMF input sample phase).toReal : ℂ))) left right := by
    have original := iteration_outcome_reference_input ctx N input sameWires observed state
      seeded (fun value => weight value.first ⟨sampleRead value.second.second, phase⟩)
        phase left right
    change ExecutionState.referenceFiberSum actual (phaseWeight phase) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (entry.1.read observed)
              ⟨sampleRead (.bits (Sampler.PackedSample.storedBits sample)), phase⟩ *
                ((sourceSampleOutcomePMF input sample phase).toReal : ℂ))) left right at original
    simpa only [sampleRead_stored] using original
  calc
    _ = ExecutionState.referenceFiberSum actual
        (fun entry basis => ∑ phase, phaseWeight phase entry basis) left right := by
          apply congrArg (fun observe =>
            ExecutionState.referenceFiberSum actual observe left right)
          funext entry basis
          exact phase_weight_decomposition ctx N observed entry.1 weight
    _ = ∑ phase, ExecutionState.referenceFiberSum actual (phaseWeight phase) left right :=
      ExecutionState.referenceFiberSum_sum actual phaseWeight left right
    _ = ∑ phase : Fin (phaseBits N) → Bool, ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            (weight (entry.1.read observed) ⟨sample, phase⟩ *
              ((sourceSampleOutcomePMF input sample phase).toReal : ℂ))) left right :=
      Finset.sum_congr rfl (fun phase _ => point phase)
    _ = ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ phase : Fin (phaseBits N) → Bool,
          ∑ sample : Fin (2 ^ residueSamplingBits N),
            (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
              (weight (entry.1.read observed) ⟨sample, phase⟩ *
                ((sourceSampleOutcomePMF input sample phase).toReal : ℂ))) left right :=
      (ExecutionState.referenceFiberSum_sum state _ left right).symm
    _ = _ := by
      apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe left right)
      funext entry basis
      unfold SourceWeights.one
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
