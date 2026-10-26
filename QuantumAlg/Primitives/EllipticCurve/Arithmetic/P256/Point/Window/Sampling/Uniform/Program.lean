/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Step
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Chronology
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Prepared.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Uniform.Execution
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Remaining
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation

/-!
# Uniform-source observation of the original measured window list

The proof follows the compact original list. Actual reset establishes each
physical bank's zero support, and actual local execution preserves the
unprepared mathematical source. Consecutive original offsets discharge the
remaining preparation equalities. Complete Store and measured histories are
retained; the scalar is the literal actual execute.effectWeight. This source
identity does not assert the point action, Fourier Born law or decoder bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- Mathematical preparation remaining at the original head; empty means literal identity. -/
def remainingSourceAction (Reference : Register) :
    List WindowIndex → UnitaryOperator (ctx.register.prod (SourceRegister.prod Reference))
  | [] => 1
  | head :: _ => sourcePreparationAction Reference (sourceFuture head)

private lemma tail_source_next (first second : WindowIndex)
    (next : second.sourceStart = first.sourceEnd) :
    UnitaryOperator.reindex (sourceLabelEquiv first).symm
        (segmentTailPreparation first.sourceStart (first.lowerWidth + 1) first.sourceAfter) =
      sourceFuture second := by
  exact (window_sourcePaired_remaining_tail 260 first.sourceStart
    (first.lowerWidth + 1) first.sourceAfter first.windowIndex_sourceWidths).trans
      ((window_sourcePaired_remaining_congr 260
        (first.sourceStart + (first.lowerWidth + 1)) second.sourceStart
        first.sourceAfter ((second.lowerWidth + 1) + second.sourceAfter)
        ((Nat.add_assoc first.sourceStart (first.lowerWidth + 1)
          first.sourceAfter).trans first.windowIndex_sourceWidths)
        second.windowIndex_sourceWidths next.symm).trans
          (window_sourcePaired_remaining_future 260 second.sourceStart
            (second.lowerWidth + 1) second.sourceAfter second.windowIndex_sourceWidths).symm)

private lemma tail_source_empty (index : WindowIndex) (last : index.sourceEnd = 520) :
    UnitaryOperator.reindex (sourceLabelEquiv index).symm
        (segmentTailPreparation index.sourceStart (index.lowerWidth + 1) index.sourceAfter) =
      1 := by
  have empty : index.sourceAfter = 0 := by
    unfold WindowIndex.sourceAfter
    change 520 - index.sourceEnd = 0
    rw [last, Nat.sub_self]
  exact (window_sourcePaired_remaining_tail 260 index.sourceStart
    (index.lowerWidth + 1) index.sourceAfter index.windowIndex_sourceWidths).trans
      (window_sourcePaired_remaining_empty 260 (index.sourceStart + (index.lowerWidth + 1))
        index.sourceAfter
        ((Nat.add_assoc index.sourceStart (index.lowerWidth + 1)
          index.sourceAfter).trans index.windowIndex_sourceWidths) empty)

private lemma source_action_one (Reference : Register) :
    sourcePreparationAction (ctx := ctx) Reference (1 : UnitaryOperator SourceRegister) = 1 := by
  unfold sourcePreparationAction
  rw [window_source_identity_tensor, window_source_identity_tensor]

private lemma tail_remaining (Reference : Register) (head : WindowIndex) (rest : List WindowIndex)
    (valid : SourceSuffix (head :: rest)) :
    savedPreparation (ctx := ctx) (sourceSegments head) Reference (sourceTail head Reference) =
      remainingSourceAction Reference rest := by
  have transport : savedPreparation (ctx := ctx) (sourceSegments head) Reference
        (sourceTail head Reference) =
      sourcePreparationAction Reference
        (UnitaryOperator.reindex (sourceLabelEquiv head).symm
          (segmentTailPreparation head.sourceStart (head.lowerWidth + 1) head.sourceAfter)) :=
    window_source_segmentTail_transport (sourceLabelEquiv head) Reference
  rw [transport]
  cases rest with
  | nil => rw [tail_source_empty head valid, source_action_one]; rfl
  | cons next tail => rw [tail_source_next head next valid.1]; rfl

namespace Parameters

private lemma prepared_source_zero (parameters : Parameters ctx) (index : WindowIndex)
    (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {History : Type} [Fintype History]
    (state : State ctx (SourceRegister.prod Reference) (services.HiddenState × History))
    (sourceZero : ∀ record label, label.2.1 ≠ (0, 0) →
      (state.block record).matrix label label = 0) :
    ∀ record label, label.2.1 ≠ (0, 0) →
      (((parameters.preparedStage index Reference).runHead environment state).block record).matrix
        label label = 0 := by
  have resetSupport := parameters.sampling_reset_referenceSupported index environment
    (SourceRegister.prod Reference) (fun label => label.1 = (0, 0)) state sourceZero
  have nativeSupport : ∀ record label, label.2.1 ≠ (0, 0) →
      ((((parameters.reset index).execute environment _ state).applyUnitary (fun _ =>
        UnitaryOperator.prodTensor
          ((QuantumFourierTransform.Semiclassical.Window.preparation (index.lowerWidth + 1)
            (parameters.ports index)).matrix environment.quantum)
          (1 : UnitaryOperator (SourceRegister.prod Reference)))).block record).matrix
        label label = 0 := by
    intro record label absent
    exact window_source_localUnitary_reference_support
      ((QuantumFourierTransform.Semiclassical.Window.preparation (index.lowerWidth + 1)
        (parameters.ports index)).matrix environment.quantum)
      ((parameters.reset index).execute environment _ state)
      (fun label => label.1 = (0, 0)) resetSupport record label absent
  exact parameters.sampling_measuredMiddle_referenceSupported index environment
    (SourceRegister.prod Reference) (fun label => label.1 = (0, 0)) _ nativeSupport

/-- Every original continuous list has the same actual prepared and uniform-source states. -/
lemma sampling_uniform_sequence (parameters : Parameters ctx) (indices : List WindowIndex)
    (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {History : Type} [Fintype History]
    (state : State ctx (SourceRegister.prod Reference) (services.HiddenState × History))
    (sourceZero : ∀ record label, label.2.1 ≠ (0, 0) →
      (state.block record).matrix label label = 0) (valid : SourceSuffix indices) :
    Stage.run environment
        ((parameters.preparedStages indices Reference).map PreparedStage.stage)
        (state.applyUnitary (fun _ => remainingSourceAction Reference indices)) =
      PreparedStage.run environment (parameters.preparedStages indices Reference) state := by
  apply window_source_uniform_sequence
    (fun index => parameters.preparedStage index Reference) environment
    (remainingSourceAction Reference) rfl SourceSuffix sampling_sourceSuffix_tail
    (fun current => ∀ record label, label.2.1 ≠ (0, 0) →
      (current.block record).matrix label label = 0)
  · intro head rest suffix CurrentHistory _ current zero
    exact (parameters.sampling_uniform_step head Reference environment current zero).trans
      (congrArg (fun operator :
          UnitaryOperator (ctx.register.prod (SourceRegister.prod Reference)) =>
        ((parameters.preparedStage head Reference).runHead environment current).applyUnitary
          (fun _ => operator)) (tail_remaining Reference head rest suffix))
  · intro head rest _ CurrentHistory _ current zero
    exact parameters.prepared_source_zero head Reference environment current zero
  · exact sourceZero
  · exact valid

/-- The source identity observes precisely the same original literal actual execution. -/
lemma sampling_uniform_sequence_storeWeight (parameters : Parameters ctx)
    (indices : List WindowIndex) (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (state : State ctx (SourceRegister.prod Reference) (services.HiddenState × History))
    (sourceZero : ∀ record label, label.2.1 ≠ (0, 0) →
      (state.block record).matrix label label = 0) (valid : SourceSuffix indices)
    (effects : Store ctx → Effect (ctx.register.prod (SourceRegister.prod Reference))) :
    Execution.storeEffectWeight (parameters.sequence indices) environment state effects =
      Stage.storeWeight environment (parameters.sourceStages indices Reference)
        (state.applyUnitary (fun _ => remainingSourceAction Reference indices)) effects := by
  have uniform := (parameters.sampling_sequence_storeWeight indices Reference
    environment state effects).trans
    (congrArg (fun current : State ctx (SourceRegister.prod Reference)
        (services.HiddenState × Stage.Records
          ((parameters.preparedStages indices Reference).map PreparedStage.stage) History) =>
      current.effectWeight (fun record => effects record.1))
        (parameters.sampling_uniform_sequence indices Reference environment state
          sourceZero valid).symm)
  exact uniform.trans
    (congrArg (fun stages :
        List (Stage ctx BitWord.model services (SourceRegister.prod Reference)) =>
      Stage.storeWeight environment stages
        (state.applyUnitary (fun _ => remainingSourceAction Reference indices)) effects)
      (parameters.preparedStages_stages indices Reference))

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
