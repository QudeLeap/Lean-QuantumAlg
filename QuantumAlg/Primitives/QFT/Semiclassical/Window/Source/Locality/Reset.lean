/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Core.Execution.Instrument.Reference.Support
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Recorded
import all QuantumAlg.Core.Base.Tensor.Reference

/-!
# Reference locality of actual stored-result reset

The original MZ and same-cell correction have a local Kraus product for each
real outcome. The full actual record includes the overwritten Store cell,
service state, incoming history and both instruction paths. This theorem is
independent of the original state and the surrounding register width.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution
open scoped BigOperators Kronecker

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma conditional_values {Value : Type} {proposition : Prop}
    (first second : Decidable proposition) (yes no : Value) :
    @ite Value proposition first yes no = @ite Value proposition second yes no := by
  cases first with
  | isTrue selected =>
      cases second with
      | isTrue _ => rfl
      | isFalse absent => exact False.elim (absent selected)
  | isFalse absent =>
      cases second with
      | isTrue selected => exact False.elim (absent selected)
      | isFalse _ => rfl

private lemma sum_condition_values {Original Outcome Value : Type}
    [Fintype Original] [Fintype Outcome] [AddCommMonoid Value]
    (predicate : Original → Outcome → Prop)
    (first second : ∀ original outcome, Decidable (predicate original outcome))
    (value : Original → Outcome → Value) :
    (∑ original, ∑ outcome,
      @ite Value (predicate original outcome) (first original outcome)
        (value original outcome) 0) =
    ∑ original, ∑ outcome,
      @ite Value (predicate original outcome) (second original outcome)
        (value original outcome) 0 := by
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  exact conditional_values _ _ _ _

private instance resetDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {ctx : RuntimeCtx .quantum} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

private lemma projector_tensor_reference (wire : Fin ctx.systemCount)
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) (Reference : Register) :
    ZMeasurement.projector (R := ctx.register.prod Reference) (fun basis => basis.1 wire) outcome =
      ZMeasurement.projector (R := ctx.register) (fun basis => basis wire) outcome ⊗ₖ
        (1 : HilbertOperator Reference) := by
  ext row column
  simp only [ZMeasurement.projector, Matrix.kroneckerMap_apply,
    Matrix.diagonal_apply, Matrix.one_apply]
  by_cases physical : row.1 = column.1
  · by_cases reference : row.2 = column.2
    · have same : row = column := Prod.ext physical reference
      simp only [if_pos same, if_pos physical, if_pos reference, mul_one]
    · have different : row ≠ column := fun same => reference (congrArg Prod.snd same)
      simp only [if_neg different, if_pos physical, if_neg reference, mul_zero]
  · have different : row ≠ column := fun same => physical (congrArg Prod.fst same)
    simp only [if_neg different, if_neg physical, zero_mul]

private lemma tensor_referenceLift {Local Reference : Register} (operator : HilbertOperator Local) :
    operator ⊗ₖ (1 : HilbertOperator Reference) = Execution.Instrument.referenceLift Reference
      operator := by
  ext row column
  rw [Matrix.kroneckerMap_apply]
  by_cases same : row.2 = column.2
  · simp only [Execution.Instrument.referenceLift, Matrix.one_apply, if_pos same]
  · simp only [Execution.Instrument.referenceLift, Matrix.one_apply, if_neg same]

/-- The same local correction follows the actual measured fiber projector. -/
def resetLocalOperator (wire : Fin ctx.systemCount)
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) : HilbertOperator ctx.register :=
  (QuditShift.operator ctx.quantumLayout wire (-outcome) : HilbertOperator ctx.register) *
    ZMeasurement.projector (R := ctx.register) (fun basis => basis wire) outcome

/-- The real correction and MZ projector have only identity on the complete reference. -/
lemma window_sourceReset_referenceLift (wire : Fin ctx.systemCount)
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) (Reference : Register) :
    (UnitaryOperator.prodTensor (QuditShift.operator ctx.quantumLayout wire (-outcome))
        (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference)) *
      ZMeasurement.projector (R := ctx.register.prod Reference)
        (fun basis => basis.1 wire) outcome =
      Execution.Instrument.referenceLift Reference (resetLocalOperator wire outcome) := by
  rw [unitaryOperator_prodTensor_identity, projector_tensor_reference,
    HilbertOperator.kronecker_identity_mul, tensor_referenceLift]
  rfl

/-- All original reset records, including overwrite collisions, use those same local Kraus rows. -/
lemma window_sourceReset_local_blocks (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (QuditShift.resetCircuit wire output realizations operations services false).Path))) :
    (((QuditShift.resetCircuit wire output realizations operations services false).execute
      environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          if QuditShift.Recorded.record (operations := operations) (services := services)
              wire output realizations original outcome = result then
            Execution.Instrument.referenceLift Reference (resetLocalOperator wire outcome) *
              (state.block original).matrix *
                (Execution.Instrument.referenceLift Reference (resetLocalOperator wire
                  outcome)).conjTranspose
          else 0 := by
  rw [QuditShift.Recorded.execute, ExecutionState.mapClassical_block_matrix]
  simp only [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases recorded : QuditShift.Recorded.record (operations := operations) (services := services)
      wire output realizations original outcome = result
  · simp only [if_pos recorded]
    rw [ExecutionState.measureZ_block]
    let projector : HilbertOperator (ctx.register.prod Reference) :=
      ZMeasurement.projector (R := ctx.register.prod Reference)
        (fun basis : (ctx.register.prod Reference).Index => basis.1 wire) outcome
    change (_ : HilbertOperator (ctx.register.prod Reference)) *
      (projector * (state.block original).matrix * projector.conjTranspose) * _ = _
    dsimp only [projector]
    rw [← window_sourceReset_referenceLift]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp only [if_neg recorded]

/-- The actual MZ/same-cell correction commutes with every external-reference unitary. -/
lemma window_sourceReset_reference_unitary (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (Reference : Register) (operator : UnitaryOperator Reference)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (QuditShift.resetCircuit wire output realizations operations services false).execute
        environment Reference (state.applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)) =
      ((QuditShift.resetCircuit wire output realizations operations services false).execute
        environment Reference state).applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator) := by
  exact Execution.Instrument.retained_referenceUnitary
    (fun current : State ctx Reference (services.HiddenState × History) =>
      (QuditShift.resetCircuit wire output realizations operations services false).execute
        environment Reference current)
    (QuditShift.Recorded.record (operations := operations) (services := services)
      wire output realizations)
    (fun _ outcome => resetLocalOperator wire outcome)
    (fun current selected => (window_sourceReset_local_blocks wire output realizations
      environment Reference current selected).trans (sum_condition_values _ _ _ _)) operator state

/-- Every actually absent reference coordinate remains absent after the same native reset. -/
lemma window_sourceReset_reference_support (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (Reference : Register) (allowed : Reference.Index → Prop)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ original basis, ¬allowed basis.2 →
      (state.block original).matrix basis basis = 0)
    (result : Store ctx × (services.HiddenState × (History ×
      (QuditShift.resetCircuit wire output realizations operations services false).Path)))
    (basis : (ctx.register.prod Reference).Index) (absent : ¬allowed basis.2) :
    (((QuditShift.resetCircuit wire output realizations operations services false).execute
      environment Reference state).block result).matrix basis basis = 0 := by
  exact Execution.Instrument.retained_reference_support
    (fun current : State ctx Reference (services.HiddenState × History) =>
      (QuditShift.resetCircuit wire output realizations operations services false).execute
        environment Reference current)
    (QuditShift.Recorded.record (operations := operations) (services := services)
      wire output realizations)
    (fun _ outcome => resetLocalOperator wire outcome)
    (fun current selected => (window_sourceReset_local_blocks wire output realizations
      environment Reference current selected).trans (sum_condition_values _ _ _ _))
    allowed state supported result basis absent

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
