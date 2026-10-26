/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments.Factor
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments.Future.Support
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Support
import all QuantumAlg.Core.Execution.Instrument.Reference.Support

/-!
# One exact uniform-source step around actual measured execution

Only the mathematical source preparation is moved. The first and last
programs remain their actual interpreters, with their complete Store,
service state, history and measured Paths. Their reference naturality and
the zero supports established by the real first program are explicit proof
premises for the later concrete consumer. No substitute point action or
physical source allocation is introduced. All widths remain symbolic.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

open scoped Kronecker

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {totalBits active beforeWidth later : Nat}

/-- Extend a mathematical source operator by literal physical and external identities. -/
def sourcePreparationAction {S : Register} (Reference : Register) (operator : UnitaryOperator S) :
    UnitaryOperator (ctx.register.prod (S.prod Reference)) :=
  UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))

private lemma tensor_product {R S : Register}
    (first second : UnitaryOperator R) (third fourth : UnitaryOperator S) :
    UnitaryOperator.prodTensor first third * UnitaryOperator.prodTensor second fourth =
      UnitaryOperator.prodTensor (first * second) (third * fourth) := by
  apply Subtype.ext
  change ((first : HilbertOperator R) ⊗ₖ (third : HilbertOperator S)) *
      ((second : HilbertOperator R) ⊗ₖ (fourth : HilbertOperator S)) = _
  exact (Matrix.mul_kronecker_mul (first : HilbertOperator R) (second : HilbertOperator R)
    (third : HilbertOperator S) (fourth : HilbertOperator S)).symm

private lemma sourceAction_mul {S : Register} (Reference : Register)
    (first second : UnitaryOperator S) :
    sourcePreparationAction (ctx := ctx) Reference (first * second) =
      sourcePreparationAction Reference first * sourcePreparationAction Reference second := by
  unfold sourcePreparationAction
  rw [tensor_product, tensor_product, one_mul, one_mul]

private lemma state_unitary_mul {Record : Type} [Fintype Record] {R : Register}
    (state : ExecutionState Record R) (first second : UnitaryOperator R) :
    state.applyUnitary (fun _ => first * second) =
      (state.applyUnitary (fun _ => second)).applyUnitary (fun _ => first) := by
  apply ExecutionState.ext
  intro record
  exact DensityOperator.applyUnitary_mul first second (state.block record)

private lemma state_unitary_commute {Record : Type} [Fintype Record] {R : Register}
    (state : ExecutionState Record R) (first second : UnitaryOperator R)
    (commute : first * second = second * first) :
    (state.applyUnitary (fun _ => first)).applyUnitary (fun _ => second) =
      (state.applyUnitary (fun _ => second)).applyUnitary (fun _ => first) := by
  exact (state_unitary_mul state second first).symm.trans
    ((congrArg (fun operator : UnitaryOperator R =>
      state.applyUnitary (fun _ => operator)) commute.symm).trans
        (state_unitary_mul state first second))

private lemma futureZero_selected (label :
    (Qubits (beforeWidth + (active + later))).Index)
    (zero : futureZero beforeWidth (active + later) label) :
    (segmentPartition beforeWidth active later label).1 = 0 := by
  change ((prodEquiv (m := active) (n := later)).symm
    ((prodEquiv (m := beforeWidth) (n := active + later)).symm label).2).1 = 0
  rw [show ((prodEquiv (m := beforeWidth) (n := active + later)).symm label).2 = 0 from zero]
  apply Fin.ext
  simp only [prodEquiv_symm_fst_val, Fin.val_zero, Nat.zero_div]

/-- A physical H or other local unitary retains every absent mathematical source label. -/
lemma window_source_localUnitary_reference_support {Local Reference : Register}
    {Record : Type} [Fintype Record] (operator : UnitaryOperator Local)
    (state : ExecutionState Record (Local.prod Reference)) (allowed : Reference.Index → Prop)
    (supported : ∀ record basis, ¬allowed basis.2 →
      (state.block record).matrix basis basis = 0)
    (record : Record) (basis : (Local.prod Reference).Index) (absent : ¬allowed basis.2) :
    (((state.applyUnitary (fun _ =>
      UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))).block record).matrix
        basis basis) = 0 := by
  have localFactor :
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference) :
        HilbertOperator (Local.prod Reference)) = Execution.Instrument.referenceLift Reference
          operator := by
    ext row column
    rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
    change operator row.1 column.1 *
      (if row.2 = column.2 then (1 : Complex) else 0) = _
    rfl
  simp only [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix]
  rw [localFactor]
  exact Execution.Instrument.local_conjugation_support (Local := Local) (Reference := Reference)
    (operator : HilbertOperator Local) (state.block record)
    allowed (supported record) basis absent

/-- Current H and the untouched later tensor factor the same full prepared density. -/
lemma window_source_future_state_factor (Reference : Register)
    {Record : Type} [Fintype Record]
    (state : ExecutionState Record
      (ctx.register.prod ((Qubits (beforeWidth + (active + later))).prod Reference)))
    (supported : ∀ record label, ¬futureZero beforeWidth (active + later) label.2.1 →
      (state.block record).matrix label label = 0) :
    state.applyUnitary (fun _ => sourcePreparationAction Reference
        (futurePreparation beforeWidth (active + later))) =
      (state.applyUnitary (fun _ => referencePreparation
        (segmentPartition beforeWidth active later) Reference)).applyUnitary
          (fun _ => sourcePreparationAction Reference
            (segmentTailPreparation beforeWidth active later)) := by
  have split := window_source_splitFuturePreparation_state ctx.register Reference
    beforeWidth active later state supported
  have factor : sourcePreparationAction (ctx := ctx) Reference
        (splitFuturePreparation beforeWidth active later) =
      sourcePreparationAction Reference (segmentTailPreparation beforeWidth active later) *
        referencePreparation (segmentPartition beforeWidth active later) Reference :=
    (congrArg (sourcePreparationAction (ctx := ctx) Reference)
      (window_source_splitFuturePreparation_factor beforeWidth active later)).symm.trans
        (sourceAction_mul Reference (segmentTailPreparation beforeWidth active later)
          (selectedUniformPreparation (segmentPartition beforeWidth active later)))
  exact split.symm.trans
    ((congrArg (fun operator :
        UnitaryOperator (ctx.register.prod
          ((Qubits (beforeWidth + (active + later))).prod Reference)) =>
      state.applyUnitary (fun _ => operator)) factor).trans
        (state_unitary_mul state _ _))

/-- The real first/last executions and all their actual records survive one hybrid replacement. -/
lemma window_source_uniform_step (ports : Ports ctx totalBits active)
    (Reference : Register)
    (first last : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment)
    {History : Type} [Fintype History]
    (state : State ctx ((Qubits (beforeWidth + (active + later))).prod Reference)
      (services.HiddenState × History))
    (firstNatural : first.execute environment _
        (state.applyUnitary (fun _ => sourcePreparationAction Reference
          (futurePreparation beforeWidth (active + later)))) =
      (first.execute environment _ state).applyUnitary (fun _ =>
        sourcePreparationAction Reference (futurePreparation beforeWidth (active + later))))
    (futureSupported : ∀ record label,
      ¬futureZero beforeWidth (active + later) label.2.1 →
        ((first.execute environment _ state).block record).matrix label label = 0)
    (bankZero : ∀ record label,
      (bankCoordinates ports.wires ports.qubits label.1).1 ≠ Partner.zeroBits active →
        ((first.execute environment _ state).block record).matrix label label = 0)
    (lastNatural : ∀ current : State ctx
        ((Qubits (beforeWidth + (active + later))).prod Reference)
        (services.HiddenState × (History × first.Path)),
      last.execute environment _ (current.applyUnitary (fun _ =>
        sourcePreparationAction Reference (segmentTailPreparation beforeWidth active later))) =
        (last.execute environment _ current).applyUnitary (fun _ =>
          sourcePreparationAction Reference
            (segmentTailPreparation beforeWidth active later))) :
    last.execute environment _
        ((first.execute environment _
          (state.applyUnitary (fun _ => sourcePreparationAction Reference
            (futurePreparation beforeWidth (active + later))))).applyUnitary
              (fun _ => selectedFeedOperator ports
                (segmentPartition beforeWidth active later) Reference)) =
      (last.execute environment _
        ((first.execute environment _ state).applyUnitary (fun _ =>
          UnitaryOperator.prodTensor ((preparation active ports).matrix environment.quantum)
            (1 : UnitaryOperator
              ((Qubits (beforeWidth + (active + later))).prod Reference))))).applyUnitary
        (fun _ => sourcePreparationAction Reference
          (segmentTailPreparation beforeWidth active later)) := by
  have doubleSupported : ∀ record label,
      ¬doubleZero ports (segmentPartition beforeWidth active later) Reference label →
        ((first.execute environment _ state).block record).matrix label label = 0 := by
    intro record label absent
    by_cases physical :
        (bankCoordinates ports.wires ports.qubits label.1).1 = Partner.zeroBits active
    · apply futureSupported record label
      intro zero
      exact absent ⟨physical, futureZero_selected label.2.1 zero⟩
    · exact bankZero record label physical
  rw [firstNatural, window_source_future_state_factor Reference _ futureSupported]
  rw [state_unitary_commute _
    (sourcePreparationAction Reference (segmentTailPreparation beforeWidth active later))
    (selectedFeedOperator ports (segmentPartition beforeWidth active later) Reference)
    (window_source_feed_segmentTail_commute ports beforeWidth later Reference).symm]
  rw [window_source_prepared_feed_state ports
    (segmentPartition beforeWidth active later) environment.quantum Reference
    (first.execute environment _ state) doubleSupported]
  exact lastNatural _

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
