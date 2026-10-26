/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Selection.Coordinates
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Uniform.Step

/-!
# Future factorization on the original mathematical source carrier

The symbolic before/current/after coordinates may describe an existing
source carrier. Complete source columns transport to that same carrier,
with literal physical and external identities. The factorization retains
arbitrary consumed-prefix correlations and every original classical record.
It introduces neither a physical register nor a reference-carrier change
in an actual Circuit interpreter.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open scoped Kronecker

variable {ctx : RuntimeCtx .quantum} {S : Register} {before active later : Nat}

private lemma tensor_mul {R T : Register}
    (first second : UnitaryOperator R) (third fourth : UnitaryOperator T) :
    UnitaryOperator.prodTensor first third * UnitaryOperator.prodTensor second fourth =
      UnitaryOperator.prodTensor (first * second) (third * fourth) := by
  apply Subtype.ext
  change ((first : HilbertOperator R) ⊗ₖ (third : HilbertOperator T)) *
      ((second : HilbertOperator R) ⊗ₖ (fourth : HilbertOperator T)) = _
  exact (Matrix.mul_kronecker_mul (first : HilbertOperator R) (second : HilbertOperator R)
    (third : HilbertOperator T) (fourth : HilbertOperator T)).symm

private lemma source_action_mul (Reference : Register) (first second : UnitaryOperator S) :
    sourcePreparationAction (ctx := ctx) Reference (first * second) =
      sourcePreparationAction Reference first * sourcePreparationAction Reference second := by
  unfold sourcePreparationAction
  rw [tensor_mul, tensor_mul, one_mul, one_mul]

/-- Saved-tail preparation is the same source operator in its original carrier. -/
lemma window_source_segmentTail_transport
    (coordinates : S.Index ≃ (Qubits (before + (active + later))).Index)
    (Reference : Register) :
    savedPreparation (ctx := ctx)
        (coordinates.trans (segmentPartition before active later)) Reference
        (UnitaryOperator.prodTensor
          (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits before))
            (uniformPreparation later)) (1 : UnitaryOperator Reference)) =
      sourcePreparationAction Reference
        (UnitaryOperator.reindex coordinates.symm
          (segmentTailPreparation before active later)) := by
  rw [window_source_savedPreparation_reference]
  rfl

/-- The split future is the exact current-then-saved-tail product on the same source. -/
lemma window_source_splitFuture_transport
    (coordinates : S.Index ≃ (Qubits (before + (active + later))).Index) :
    UnitaryOperator.reindex coordinates.symm (splitFuturePreparation before active later) =
      UnitaryOperator.reindex coordinates.symm (segmentTailPreparation before active later) *
        selectedUniformPreparation (coordinates.trans (segmentPartition before active later)) := by
  rw [← window_source_splitFuturePreparation_factor,
    UnitaryOperator.unitaryOperator_reindex_mul, window_source_selectedPreparation_reindex]

/-- Internally zero future support gives the same complete density after source factorization. -/
lemma window_source_future_transport_state
    (coordinates : S.Index ≃ (Qubits (before + (active + later))).Index)
    (Reference : Register) {Record : Type} [Fintype Record]
    (state : ExecutionState Record (ctx.register.prod (S.prod Reference)))
    (supported : ∀ record label, ¬futureZero before (active + later) (coordinates label.2.1) →
      (state.block record).matrix label label = 0) :
    state.applyUnitary (fun _ => sourcePreparationAction Reference
        (UnitaryOperator.reindex coordinates.symm (futurePreparation before (active + later)))) =
      (state.applyUnitary (fun _ =>
        referencePreparation (coordinates.trans (segmentPartition before active later))
          Reference)).applyUnitary
          (fun _ => savedPreparation
            (coordinates.trans (segmentPartition before active later)) Reference
              (UnitaryOperator.prodTensor
                (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits before))
                  (uniformPreparation later)) (1 : UnitaryOperator Reference))) := by
  have split : state.applyUnitary (fun _ => sourcePreparationAction Reference
        (UnitaryOperator.reindex coordinates.symm (futurePreparation before (active + later)))) =
      state.applyUnitary (fun _ => sourcePreparationAction Reference
        (UnitaryOperator.reindex coordinates.symm
          (splitFuturePreparation before active later))) := by
    apply ExecutionState.ext
    intro record
    apply DensityOperator.ext
    apply DensityOperator.conjugation_eq_on_basis_support (state.block record)
      (fun label => futureZero before (active + later) (coordinates label.2.1)) _ _
      (supported record)
    intro column zero row
    simp only [sourcePreparationAction, UnitaryOperator.unitaryOperator_prodTensor_apply]
    change (1 : HilbertOperator ctx.register) row.1 column.1 *
        (futurePreparation before (active + later) (coordinates row.2.1)
          (coordinates column.2.1) * (1 : HilbertOperator Reference) row.2.2 column.2.2) =
      (1 : HilbertOperator ctx.register) row.1 column.1 *
        (splitFuturePreparation before active later (coordinates row.2.1)
          (coordinates column.2.1) * (1 : HilbertOperator Reference) row.2.2 column.2.2)
    rw [window_source_splitFuturePreparation_zero_suffix before active later
      (coordinates row.2.1) (coordinates column.2.1) zero]
  have factor : sourcePreparationAction (ctx := ctx) Reference
        (UnitaryOperator.reindex coordinates.symm (splitFuturePreparation before active later)) =
      sourcePreparationAction Reference
        (UnitaryOperator.reindex coordinates.symm (segmentTailPreparation before active later)) *
      referencePreparation (coordinates.trans (segmentPartition before active later)) Reference :=
    (congrArg (sourcePreparationAction (ctx := ctx) Reference)
      (window_source_splitFuture_transport coordinates)).trans (source_action_mul Reference _ _)
  rw [split, factor]
  apply ExecutionState.ext
  intro record
  exact (DensityOperator.applyUnitary_mul _ _ (state.block record)).trans
    (congrArg (fun operator : UnitaryOperator (ctx.register.prod (S.prod Reference)) =>
      DensityOperator.applyUnitary operator
        (DensityOperator.applyUnitary
          (referencePreparation (coordinates.trans (segmentPartition before active later))
            Reference) (state.block record)))
      (window_source_segmentTail_transport coordinates Reference).symm)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
