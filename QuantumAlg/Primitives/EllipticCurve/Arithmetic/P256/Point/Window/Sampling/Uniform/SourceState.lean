/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation.Reference
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation.Initial

/-!
# Actual original-window events on the same full paired mathematical source

The auxiliary source starts in its explicitly constructed zero ket. The
proved actual-list preparation identity and actual reference partial trace
identify the original Store event with the same positive source effect.
The complete original Store, HiddenState, History and actual Paths remain.
This statement assumes no point action, arithmetic domain or good-branch law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- The full paired source is one mathematical zero column, without a physical source bank. -/
def uniformSource {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector (SourceRegister.prod Reference) :=
  NormalizedVector.prodTensor
    ((pairedRemainingPreparation 260 0 520 (by rfl)).apply
      (NormalizedVector.ket (R := SourceRegister) (0, 0))) reference

private lemma initial_sourceFuture (index : WindowIndex) (first : index.sourceStart = 0) :
    sourceFuture index = pairedRemainingPreparation 260 0 520 (by rfl) := by
  exact (window_sourcePaired_remaining_future 260 index.sourceStart
    (index.lowerWidth + 1) index.sourceAfter index.windowIndex_sourceWidths).trans
      (window_sourcePaired_remaining_congr 260 index.sourceStart 0
        ((index.lowerWidth + 1) + index.sourceAfter) 520
        index.windowIndex_sourceWidths (by rfl) first)

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma zero_source_support {History : Type} [Fintype History]
    (decision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ∀ record actual, actual.2.1 ≠ (0, 0) →
      ((initialSourceState (S := SourceRegister) (Reference := Reference)
        decision original (NormalizedVector.ket label)
        (0, 0) reference).block record).matrix actual actual = 0 := by
  intro record actual absent
  unfold initialSourceState initialPhysicalState
  by_cases same : record = original
  · simp only [ExecutionState.ofValue_block, if_pos same, DensityOperator.ofPure_matrix,
      NormalizedVector.prodTensor_apply, NormalizedVector.ket_apply, if_neg absent,
      zero_mul, mul_zero]
  · simp only [ExecutionState.ofValue_block, if_neg same, DensityOperator.zero_matrix,
      Matrix.zero_apply]

namespace Parameters

private lemma initial_prepared_weight (parameters : Parameters ctx)
    (head : WindowIndex) (rest : List WindowIndex) (first : head.sourceStart = 0)
    (valid : SourceSuffix (head :: rest)) (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (state : State ctx (SourceRegister.prod Reference) (services.HiddenState × History))
    (sourceZero : ∀ record actual, actual.2.1 ≠ (0, 0) →
      (state.block record).matrix actual actual = 0)
    (effects : Store ctx → Effect (ctx.register.prod (SourceRegister.prod Reference))) :
    Execution.storeEffectWeight (parameters.sequence (head :: rest)) environment state effects =
      Stage.storeWeight environment (parameters.sourceStages (head :: rest) Reference)
        (state.applyUnitary (fun _ => sourcePreparationAction Reference
          (pairedRemainingPreparation 260 0 520 (by rfl)))) effects := by
  have prepared := parameters.sampling_uniform_sequence_storeWeight (head :: rest)
    Reference environment state sourceZero valid effects
  have action : remainingSourceAction (ctx := ctx) Reference (head :: rest) =
      sourcePreparationAction Reference (pairedRemainingPreparation 260 0 520 (by rfl)) :=
    congrArg (sourcePreparationAction (ctx := ctx) Reference) (initial_sourceFuture head first)
  exact prepared.trans
    (congrArg (fun operator :
        UnitaryOperator (ctx.register.prod (SourceRegister.prod Reference)) =>
      Stage.storeWeight environment (parameters.sourceStages (head :: rest) Reference)
        (state.applyUnitary (fun _ => operator)) effects) action)

/-- A complete original list starting at zero has precisely the full-source event weight. -/
lemma sampling_initial_sourceEffect_weight (parameters : Parameters ctx)
    (head : WindowIndex) (rest : List WindowIndex) (first : head.sourceStart = 0)
    (valid : SourceSuffix (head :: rest)) {Reference : Register}
    (reference : NormalizedVector Reference)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    (event : Store ctx → Bool) :
    Execution.storeEffectWeight (parameters.sequence (head :: rest)) environment
        (ExecutionState.ofValue original (DensityOperator.ofPure
          (NormalizedVector.prodTensor (NormalizedVector.ket label) reference)))
        (Execution.recordEventEffect (ctx.register.prod Reference) event) =
      (parameters.sourceEffect (head :: rest) Reference environment
        (fun record => Execution.recordEventEffect
          (ctx.register.prod (SourceRegister.prod Reference)) event record.1)
        original label).weight (DensityOperator.ofPure (uniformSource reference)) := by
  refine window_source_initial_event
    (ctx := ctx) (operations := BitWord.model) (services := services) (History := History)
    (S := SourceRegister) (Reference := Reference)
    (parameters.sequence (head :: rest)) (parameters.sourceStages (head :: rest) Reference)
    environment _ original label (0, 0) reference
    (pairedRemainingPreparation 260 0 520 (by rfl)) event ?_ ?_
  · exact parameters.sampling_sequence_referenceTraceNatural (head :: rest) environment
      Reference SourceRegister _
  · exact initial_prepared_weight parameters head rest first valid Reference environment _
      (zero_source_support _ original label reference)
      (Execution.recordEventEffect (ctx.register.prod (SourceRegister.prod Reference)) event)

end Parameters

private lemma mapped_finRange_head {Label : Type} (count : Nat)
    (family : Fin (count + 1) → Label) :
    (List.finRange (count + 1)).map family =
      family 0 :: List.ofFn (fun position : Fin count => family position.succ) :=
  (List.ofFn_eq_map (f := family)).symm.trans List.ofFn_succ

private lemma schedule_head : schedule = chronologicalIndex 0 ::
    List.ofFn (fun position : Fin 33 => chronologicalIndex position.succ) :=
  mapped_finRange_head 33 chronologicalIndex

/-- The literal actual34 sampler observes the original full paired source with no extra premise. -/
lemma sampling_circuit_sourceEffect_weight (parameters : Parameters ctx)
    {Reference : Register} (reference : NormalizedVector Reference)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    (event : Store ctx → Bool) :
    Execution.storeEffectWeight (circuit parameters) environment
        (ExecutionState.ofValue original (DensityOperator.ofPure
          (NormalizedVector.prodTensor (NormalizedVector.ket label) reference)))
        (Execution.recordEventEffect (ctx.register.prod Reference) event) =
      (parameters.sourceEffect schedule Reference environment
        (fun record => Execution.recordEventEffect
          (ctx.register.prod (SourceRegister.prod Reference)) event record.1)
        original label).weight (DensityOperator.ofPure (uniformSource reference)) := by
  have originalList : schedule = chronologicalIndex 0 ::
      List.ofFn (fun position : Fin 33 => chronologicalIndex position.succ) := schedule_head
  have valid : SourceSuffix (chronologicalIndex 0 ::
      List.ofFn (fun position : Fin 33 => chronologicalIndex position.succ)) :=
    (congrArg SourceSuffix originalList).mp sampling_schedule_sourceSuffix
  have execution := congrArg (fun indices : List WindowIndex =>
    Execution.storeEffectWeight (parameters.sequence indices) environment
      (ExecutionState.ofValue original (DensityOperator.ofPure
        (NormalizedVector.prodTensor (NormalizedVector.ket label) reference)))
      (Execution.recordEventEffect (ctx.register.prod Reference) event)) originalList
  have observation := congrArg (fun indices : List WindowIndex =>
    (parameters.sourceEffect indices Reference environment
      (fun record => Execution.recordEventEffect
        (ctx.register.prod (SourceRegister.prod Reference)) event record.1)
      original label).weight (DensityOperator.ofPure (uniformSource reference))) originalList
  exact execution.trans
    ((parameters.sampling_initial_sourceEffect_weight _ _
      sampling_chronological_source_first valid reference environment original label event).trans
        observation.symm)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
