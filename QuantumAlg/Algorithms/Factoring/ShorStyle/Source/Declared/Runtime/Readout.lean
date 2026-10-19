/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Joint
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights.Probability
import all QuantumAlg.Util.Classical.OrderRecovery
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# The actual declared Shor round has the original joint source PMF

The observation reads only the actual retained sample and phase cells. It
identifies their scalar probabilities and full reference weights with the
original source distribution; it introduces no circuit operation or draw.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

local instance {N : Nat} : Fintype (SourceOutcome N) :=
  Fintype.ofEquiv (Fin (2 ^ residueSamplingBits N) × TerminalZMeasure.Outcome (phaseBits N))
    (SourceWeights.outcomeEquiv N)

/-- Purely identify the original finite source label in the actual stored convention. -/
def sampleRead {width : Nat} : (CShape.bits width).Value → Fin (2 ^ width)
  | .bits values => ClassicalAlgorithms.OrderRecovery.fullRegisterIndex values

/-- Read the actual phase bits without performing classical recovery. -/
def phaseRead {width : Nat} : (CShape.bits width).Value → (Fin width → Bool)
  | .bits values => values

/-- The original source outcome is read from the same complete actual result tuple. -/
def sourceRead (ctx : RuntimeCtx .quantum) (N : Nat)
    (store : Store (Iteration.context ctx N)) : SourceOutcome N :=
  ⟨sampleRead (store.read (Iteration.sampleInput ctx N)),
    phaseRead (store.read (Iteration.phaseInput ctx N))⟩

private lemma sampleRead_stored {width : Nat} (sample : Fin (2 ^ width)) :
    sampleRead (.bits (Sampler.PackedSample.storedBits sample)) = sample :=
  ClassicalAlgorithms.OrderRecovery.fullRegisterIndex_terminalMeasurement width sample

private lemma original_pair_weight {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (outcome : Fin (phaseBits N) → Bool) :
    (∑ chosen : Fin (2 ^ residueSamplingBits N),
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
        ((if chosen = sample then 1 else 0) *
          ((sourceSampleOutcomePMF input chosen outcome).toReal : ℂ))) =
      ((sourceOutcomePMF input ⟨sample, outcome⟩).toReal : ℂ) := by
  have original := (SourceWeights.one_eq input
    (fun value => if value = (⟨sample, outcome⟩ : SourceOutcome N) then 1 else 0)).trans
      (PMF.sum_toReal_indicator (sourceOutcomePMF input) ⟨sample, outcome⟩)
  refine Eq.trans ?_ original
  unfold SourceWeights.one
  apply Finset.sum_congr rfl
  intro chosen _
  apply congrArg (fun value : ℂ =>
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
  by_cases matching : chosen = sample
  · subst chosen
    simp only [SourceOutcome.mk.injEq, true_and, if_true,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [SourceOutcome.mk.injEq, matching, false_and, if_false,
      zero_mul, Finset.sum_const_zero]

private lemma sourceRead_indicator (ctx : RuntimeCtx .quantum) (N : Nat)
    (store : Store (Iteration.context ctx N))
    (sample : Fin (2 ^ residueSamplingBits N)) (phase : Fin (phaseBits N) → Bool) :
    (if sourceRead ctx N store = (⟨sample, phase⟩ : SourceOutcome N) then (1 : ℂ) else 0) =
      (if sampleRead (store.read (Iteration.sampleInput ctx N)) = sample then 1 else 0) *
        (if store.read (Iteration.phaseInput ctx N) = CShape.Value.bits phase then 1 else 0) := by
  unfold sourceRead
  cases sampled : store.read (Iteration.sampleInput ctx N) with
  | bits sampleBits =>
    cases measured : store.read (Iteration.phaseInput ctx N) with
    | bits phaseValues =>
      simp only [sampleRead, phaseRead, SourceOutcome.mk.injEq, CShape.Value.bits.injEq]
      by_cases selectedSample :
          ClassicalAlgorithms.OrderRecovery.fullRegisterIndex sampleBits = sample <;>
        by_cases selectedPhase : phaseValues = phase <;>
        simp [selectedSample, selectedPhase]

/-- The complete actual program has the original joint point weights. -/
lemma sampling_source_reference (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History))
    (outcome : SourceOutcome N) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Sampling.code base noQuantum N).execute (environment input) Reference state)
      (fun entry _ => if sourceRead (bankContext base noQuantum N) N entry.1 = outcome
        then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ((sourceOutcomePMF input outcome).toReal : ℂ)) leftRef rightRef := by
  cases outcome with
  | mk sample phase =>
    have actual := sampling_outcome_reference base noQuantum N input state
      (fun value => if sampleRead value = sample then 1 else 0) phase leftRef rightRef
    have coefficient :
        (∑ chosen : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            ((if sampleRead (.bits (Sampler.PackedSample.storedBits chosen)) = sample
              then 1 else 0) * ((sourceSampleOutcomePMF input chosen phase).toReal : ℂ))) =
          ((sourceOutcomePMF input ⟨sample, phase⟩).toReal : ℂ) := by
      simp only [sampleRead_stored]
      exact original_pair_weight input sample phase
    rw [coefficient] at actual
    refine Eq.trans ?_ actual
    apply congrArg (fun observe => ExecutionState.referenceFiberSum
      ((Sampling.code base noQuantum N).execute (environment input) Reference state)
      observe leftRef rightRef)
    funext entry basis
    exact sourceRead_indicator (bankContext base noQuantum N) N entry.1 sample phase

/-- The actual trace-derived source output PMF equals the original joint distribution. -/
lemma sampling_source_toPMF (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History))
    (normalized : state.IsNormalized) :
    (((Sampling.code base noQuantum N).execute (environment input) Reference state).toPMF
      (((Sampling.code base noQuantum N).execute_mass
        (environment input) Reference state).trans normalized)).map
        (fun entry => sourceRead (bankContext base noQuantum N) N entry.1) =
          sourceOutcomePMF input := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((Sampling.code base noQuantum N).execute (environment input) Reference state) normalized
    (((Sampling.code base noQuantum N).execute_mass
      (environment input) Reference state).trans normalized)
  intro outcome leftRef rightRef
  exact sampling_source_reference base noQuantum N input state outcome leftRef rightRef

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
