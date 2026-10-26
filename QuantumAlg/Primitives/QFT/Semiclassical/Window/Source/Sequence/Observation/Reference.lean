/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Prepared.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Uniform.Step
import all QuantumAlg.Core.Execution.State.Marginal.Reference
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# The same classical event while observing away a mathematical reference

An event observes each original complete record with its unchanged mass.
Discarding a separate reference factor preserves that scalar. A ket factor
can be introduced and observed away mathematically, without preparing,
releasing or replacing any physical system or classical record.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- Tracing the mathematical frame leaves every original record's event mass unchanged. -/
lemma window_source_recordEvent_forgetReference
    {Record : Type} [Fintype Record] {R Frame Reference : Register}
    (state : ExecutionState Record (R.prod (Frame.prod Reference))) (event : Record → Bool) :
    state.forgetReferenceFrame.effectWeight (Execution.recordEventEffect (R.prod Reference) event) =
      state.effectWeight (Execution.recordEventEffect (R.prod (Frame.prod Reference)) event) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro record _
  by_cases selected : event record = true
  · simp only [Execution.recordEventEffect, if_pos selected, Effect.weight_one]
    exact ExecutionState.forgetReferenceFrame_block_mass state record
  · simp only [Execution.recordEventEffect, if_neg selected, Effect.weight_zero]

/-- An auxiliary basis ket disappears under the same exact partial trace. -/
lemma window_source_forget_ket_frame
    {Record : Type} [Fintype Record] {R Frame Reference : Register}
    (original : Record) (localVector : NormalizedVector R) (frame : Frame.Index)
    (reference : NormalizedVector Reference) :
    (ExecutionState.ofValue original (DensityOperator.ofPure
      (NormalizedVector.prodTensor localVector
        (NormalizedVector.prodTensor (NormalizedVector.ket frame) reference)))
      ).forgetReferenceFrame =
      ExecutionState.ofValue original
        (DensityOperator.ofPure (NormalizedVector.prodTensor localVector reference)) := by
  apply ExecutionState.ext
  intro record
  apply DensityOperator.ext
  ext row column
  rw [ExecutionState.executionState_forgetReferenceFrame_entry]
  by_cases same : record = original
  · simp only [ExecutionState.ofValue_block, if_pos same, DensityOperator.ofPure_matrix,
      NormalizedVector.prodTensor_apply]
    rw [Finset.sum_eq_single frame]
    · simp only [NormalizedVector.ket_apply, if_true, one_mul]
    · intro other _ different
      simp [different]
    · simp
  · simp only [ExecutionState.ofValue_block, if_neg same, DensityOperator.zero_matrix,
      Matrix.zero_apply, Finset.sum_const_zero]

/-- Applying one named actual operator to a named pure record preserves its literal record. -/
lemma window_source_applyUnitary_pure_record
    {Record : Type} [Fintype Record] {R : Register}
    (original : Record) (vector : NormalizedVector R) (operator : UnitaryOperator R) :
    (ExecutionState.ofValue original (DensityOperator.ofPure vector)).applyUnitary
        (fun _ => operator) =
      ExecutionState.ofValue original (DensityOperator.ofPure (operator.apply vector)) := by
  apply ExecutionState.ext
  intro record
  rw [ExecutionState.applyUnitary_block, ExecutionState.ofValue_block,
    ExecutionState.ofValue_block]
  by_cases same : record = original
  · rw [if_pos same, if_pos same, DensityOperator.ofPure_apply]
  · rw [if_neg same, if_neg same]
    apply DensityOperator.ext
    simp only [DensityOperator.applyUnitary_matrix, DensityOperator.zero_matrix,
      Matrix.mul_zero, Matrix.zero_mul]

/-- Only the mathematical source factor is prepared, with the original complete record. -/
lemma window_source_prepare_pure_record
    {Record : Type} [Fintype Record] {R S Reference : Register}
    (original : Record) (localVector : NormalizedVector R) (source : NormalizedVector S)
    (reference : NormalizedVector Reference) (operator : UnitaryOperator S) :
    (ExecutionState.ofValue original (DensityOperator.ofPure
      (NormalizedVector.prodTensor localVector (NormalizedVector.prodTensor source reference)))
      ).applyUnitary (fun _ => UnitaryOperator.prodTensor (1 : UnitaryOperator R)
          (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))) =
      ExecutionState.ofValue original (DensityOperator.ofPure
        (NormalizedVector.prodTensor localVector
          (NormalizedVector.prodTensor (operator.apply source) reference))) := by
  rw [window_source_applyUnitary_pure_record]
  apply congrArg (fun vector : NormalizedVector (R.prod (S.prod Reference)) =>
    ExecutionState.ofValue original (DensityOperator.ofPure vector))
  apply NormalizedVector.ext
  intro label
  change (UnitaryOperator.prodTensor (1 : UnitaryOperator R)
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))).applyVec
      (HilbertVector.prodTensor localVector.vec
        (HilbertVector.prodTensor source.vec reference.vec)) label = _
  rw [UnitaryOperator.prodTensor_applyVec_prodTensor,
    UnitaryOperator.prodTensor_applyVec_prodTensor, UnitaryOperator.one_applyVec,
    UnitaryOperator.one_applyVec]
  rfl

/-- The original actual code observes the same Store event before or after reference tracing. -/
lemma window_source_actualStoreEvent_forget
    {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
    {services : ClassicalOracleModel} {Reference Frame : Register}
    (code : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type} [Fintype History]
    (state : State ctx (Frame.prod Reference) (services.HiddenState × History))
    (event : Store ctx → Bool)
    (natural : code.execute environment Reference state.forgetReferenceFrame =
      (code.execute environment (Frame.prod Reference) state).forgetReferenceFrame) :
    Execution.storeEffectWeight code environment state.forgetReferenceFrame
        (Execution.recordEventEffect (ctx.register.prod Reference) event) =
      Execution.storeEffectWeight code environment state
        (Execution.recordEventEffect (ctx.register.prod (Frame.prod Reference)) event) := by
  unfold Execution.storeEffectWeight
  rw [natural]
  exact window_source_recordEvent_forgetReference
    (code.execute environment (Frame.prod Reference) state) (fun record => event record.1)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
