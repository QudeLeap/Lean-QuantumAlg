/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Core.Execution.Instrument.Reference.Support
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Lift

/-!
# Reference locality of the actual recycled Fourier readout

The original stored-feedback phase and measured/reset source row factor as a
local matrix beside the reference identity on every label. Their complete
actual record equation therefore preserves reference support and commutes
with arbitrary reference unitaries, without a good-label premise.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

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

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- The literal full-layout source row, retaining every physical complement coordinate. -/
def inverseLocalOperator (ports : Ports ctx totalBits active)
    (original : Store ctx) (outcome : Bits active) : HilbertOperator ctx.register :=
  fun row column =>
    if (bankCoordinates ports.wires ports.qubits row).1 = Partner.zeroBits active ∧
        (bankCoordinates ports.wires ports.qubits row).2 =
          (bankCoordinates ports.wires ports.qubits column).2 then
      signedSourceMatrix true active outcome (bankCoordinates ports.wires ports.qubits column).1 *
        Feedback.wordScalar ports original column (List.finRange active)
    else 0

/-- The actual negative Fourier row has literal identity on its whole external reference. -/
lemma window_sourceInverse_referenceLift (ports : Ports ctx totalBits active)
    (Reference : Register) (original : Store ctx) (outcome : Bits active) :
    sourceWindowKraus ports Reference original outcome =
      Execution.Instrument.referenceLift Reference (inverseLocalOperator ports original outcome)
        := by
  ext row column
  rw [sourceWindowKraus, referenceBankCoordinates_apply, referenceBankCoordinates_apply]
  by_cases same : row.2 = column.2 <;>
    by_cases zero : (bankCoordinates ports.wires ports.qubits row.1).1 =
      Partner.zeroBits active <;>
    by_cases saved : (bankCoordinates ports.wires ports.qubits row.1).2 =
      (bankCoordinates ports.wires ports.qubits column.1).2 <;>
    simp only [Execution.Instrument.referenceLift, inverseLocalOperator, Prod.mk.injEq, same,
      zero, saved,
      and_self, and_true, and_false, if_true, if_false, mul_one, mul_zero]

/-- Complete real records of the allocating or strict actual readout use these same local rows. -/
lemma window_sourceInverse_local_blocks (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (liftedInverse (operations := operations) (services := services)
        (allowAllocation := allowAllocation) ports).Path))) :
    (((liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports).execute
      environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Bits active,
        if Execution.Instrument.retainedRecord (services := services)
            (inverseStoreRecord (operations := operations) (services := services) ports)
              original outcome = result then
          Execution.Instrument.referenceLift Reference (inverseLocalOperator ports original.1
            outcome) *
            (state.block original).matrix *
              (Execution.Instrument.referenceLift Reference
                (inverseLocalOperator ports original.1 outcome)).conjTranspose
        else 0 := by
  refine (window_liftedInverse_source_record_matrix (allowAllocation := allowAllocation)
    ports environment Reference state result).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  exact (congrArg (fun operator : HilbertOperator (ctx.register.prod Reference) =>
    if Execution.Instrument.retainedRecord (services := services)
        (inverseStoreRecord (operations := operations) (services := services) ports)
          original outcome = result then
      operator * (state.block original).matrix * operator.conjTranspose
    else 0) (window_sourceInverse_referenceLift ports Reference original.1 outcome)).trans
      (conditional_values _ _ _ _)

/-- Every actual Fourier readout commutes with any unitary on the arbitrary external reference. -/
lemma window_sourceInverse_reference_unitary (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) (operator : UnitaryOperator Reference)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports).execute environment Reference
        (state.applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)) =
      ((liftedInverse (operations := operations) (services := services)
        (allowAllocation := allowAllocation) ports).execute
        environment Reference state).applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator) := by
  exact Execution.Instrument.retained_referenceUnitary
    (fun current : State ctx Reference (services.HiddenState × History) =>
      (liftedInverse (operations := operations) (services := services)
        (allowAllocation := allowAllocation) ports).execute
      environment Reference current)
    (Execution.Instrument.retainedRecord (services := services)
      (inverseStoreRecord (operations := operations) (services := services) ports))
    (fun (original : Store ctx × (services.HiddenState × History)) (outcome : Bits active) =>
      inverseLocalOperator ports original.1 outcome)
    (fun current selected =>
      (window_sourceInverse_local_blocks (allowAllocation := allowAllocation)
        ports environment Reference current selected).trans (sum_condition_values _ _ _ _))
    operator state

/-- The same actual readout cannot populate a previously absent reference coordinate. -/
lemma window_sourceInverse_reference_support (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) (allowed : Reference.Index → Prop)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ original basis, ¬allowed basis.2 →
      (state.block original).matrix basis basis = 0)
    (result : Store ctx × (services.HiddenState × (History ×
      (liftedInverse (operations := operations) (services := services)
        (allowAllocation := allowAllocation) ports).Path)))
    (basis : (ctx.register.prod Reference).Index) (absent : ¬allowed basis.2) :
    (((liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports).execute
      environment Reference state).block result).matrix basis basis = 0 := by
  exact Execution.Instrument.retained_reference_support
    (fun current : State ctx Reference (services.HiddenState × History) =>
      (liftedInverse (operations := operations) (services := services)
        (allowAllocation := allowAllocation) ports).execute
      environment Reference current)
    (Execution.Instrument.retainedRecord (services := services)
      (inverseStoreRecord (operations := operations) (services := services) ports))
    (fun (original : Store ctx × (services.HiddenState × History)) (outcome : Bits active) =>
      inverseLocalOperator ports original.1 outcome)
    (fun current selected =>
      (window_sourceInverse_local_blocks (allowAllocation := allowAllocation)
        ports environment Reference current selected).trans (sum_condition_values _ _ _ _))
    allowed state supported
    result basis absent

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
