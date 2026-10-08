/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Runtime.Agreement
import all QuantumAlg.Core.Execution.Prepared.BasisSupport
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete supported-state correctness of actual modular-add inversion

Original unit and canonical-target support is the only local input
condition. Density positivity extends it to every external-reference
coordinate. Actual fixed preparation supplies all fresh auxiliary values,
and the proved complete native columns then give the independent target
on every joint matrix entry, including the original supplied flag.

The complete output requirement aggregates actual classical histories.
Mandatory borrowed restoration follows separately from the same real
preparation and local unitary execution.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AccumulateState

noncomputable section

open Execution AccumulateRuntime

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def preparedSupport (modulus : Nat) (basis : (after modulus.size).register.Index) : Prop :=
  ((PayloadPreparation.assembly modulus.size (modulus.size + 1)).symm basis).1 =
      (InputPreparation.preparation modulus).value ∧
    AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size
      ((PayloadPreparation.assembly modulus.size (modulus.size + 1)).symm basis).2)

/-- The original local valid-input predicate suffices for complete joint conjugation equality. -/
theorem accumulateState_prepared_conjugation (modulus : Nat) (modulusPositive : 0 < modulus)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : AccumulateTarget.valid modulus input.localState) :
    DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (AccumulateRuntime.program modulus).matrix
          (1 : UnitaryOperator Reference))
        (preparedDensity PayloadPreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (modulus.size + 1))
          (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (modulus.size + 1))
          (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal) =
      AccumulateTarget.density modulus modulusPositive Reference input := by
  apply DensityOperator.applyLocalUnitary_eq_on_basis_support _ (preparedSupport modulus)
  · intro basis outside
    apply preparedDensity_basis_support PayloadPreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (modulus.size + 1))
      (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (modulus.size + 1))
      (InputPreparation.preparation modulus).value input.state.quantumMarginal
      (fun old => AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old))
      _ basis outside
    intro old absent
    rw [← Input.localState_quantumMarginal input]
    exact valid old absent
  · intro basis allowed row
    obtain ⟨⟨fresh, old⟩, rfl⟩ :=
      (PayloadPreparation.assembly modulus.size (modulus.size + 1)).surjective basis
    have decoded : fresh = (InputPreparation.preparation modulus).value ∧
        AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old) := by
      simpa only [preparedSupport, Equiv.symm_apply_apply] using allowed
    obtain ⟨rfl, admitted⟩ := decoded
    exact AccumulateAgreement.accumulateAgreement_prepared_column modulus modulusPositive
      old admitted row

/-- Every actual complete run gives the independent full target for arbitrary valid mixed input. -/
theorem accumulateState_finalState_quantumMarginal (modulus : Nat) (modulusPositive : 0 < modulus)
    {shape : CShape} (output : Output (after modulus.size) shape)
    {Reference : Register}
    (input : OracleInput .empty (before modulus.size) Reference)
    (valid : AccumulateTarget.valid modulus input.caller.localState) :
    (({ code := AccumulateRuntime.code modulus, output := output } :
      AlgorithmRun (.quantum AlgorithmGate.model .empty)
        (before modulus.size) (after modulus.size) shape).finalState
        Reference input.state).quantumMarginal =
      AccumulateTarget.density modulus modulusPositive Reference input.caller := by
  let recorded := input.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have result := AlgorithmRun.finalState_quantumMarginal
    ({ code := AccumulateRuntime.code modulus, output := output } :
      AlgorithmRun (.quantum AlgorithmGate.model .empty)
        (before modulus.size) (after modulus.size) shape) Reference input.state
  calc
    _ = ((AccumulateRuntime.code modulus).execute Reference recorded).quantumMarginal := result
    _ = DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (AccumulateRuntime.program modulus).matrix
          (1 : UnitaryOperator Reference))
        (((PayloadPreparation.circuit modulus (modulus.size + 1)).execute
          Reference recorded).quantumMarginal) :=
      PayloadRuntime.payloadRuntime_code_quantumMarginal modulus (modulus.size + 1)
        (nativeProgram modulus) recorded
    _ = DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (AccumulateRuntime.program modulus).matrix
          (1 : UnitaryOperator Reference))
        (preparedDensity PayloadPreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size
            (modulus.size + 1))
          (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size
            (modulus.size + 1))
          (InputPreparation.preparation modulus).normalized Reference recorded.quantumMarginal) :=
      congrArg _ (PayloadPreparation.execute_preparedDensity modulus
        (modulus.size + 1) recorded)
    _ = AccumulateTarget.density modulus modulusPositive Reference input.caller := by
      rw [show recorded.quantumMarginal = input.caller.state.quantumMarginal from by
        exact (ExecutionState.mapClassical_quantumMarginal _ _).trans
          input.oracleInput_caller_quantumMarginal.symm]
      exact accumulateState_prepared_conjugation modulus modulusPositive input.caller valid

/-- The full-layout mixed promise holds after aggregating the actual unit output observation. -/
theorem accumulateState_requirement_holds (modulus : Nat) (modulusPositive : 0 < modulus)
    {shape : CShape} (output : Output (after modulus.size) shape)
    {Reference : Register}
    (input : OracleInput .empty (before modulus.size) Reference)
    (valid : AccumulateTarget.valid modulus input.caller.localState) :
    (AccumulateTarget.requirement modulus modulusPositive).Holds input.caller
      (({ code := AccumulateRuntime.code modulus, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty)
          (before modulus.size) (after modulus.size) shape).finalState
          Reference input.state) := by
  intro value
  cases value with
  | unit =>
    change (StatePromise.mixed
        (AccumulateTarget.selectedDensity modulus modulusPositive Reference input.caller)
        (AccumulateTarget.selected_normalized modulus modulusPositive Reference input.caller)).Holds
      (DensityOperator.observeSelectionWithReference (after modulus.size).quantumLayout
        Finset.univ Reference
        (((({ code := AccumulateRuntime.code modulus, output := output } :
          AlgorithmRun (.quantum AlgorithmGate.model .empty)
            (before modulus.size) (after modulus.size) shape).finalState
            Reference input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
    rw [ExecutionState.executionState_mapClassical_const_block,
      accumulateState_finalState_quantumMarginal modulus modulusPositive output input valid]
    change (AccumulateTarget.selectedDensity modulus modulusPositive
        Reference input.caller).matrix =
      ((AccumulateTarget.selectedDensity modulus modulusPositive
        Reference input.caller).mass : ℝ) •
        (AccumulateTarget.selectedDensity modulus modulusPositive
          Reference input.caller).matrix
    rw [AccumulateTarget.selected_normalized]
    simp only [one_smul]

/-- Actual preparation and complete inversion restore the mandatory joint borrowed observation. -/
theorem accumulateState_borrowedRestored (modulus : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (AccumulateRuntime.code modulus).BorrowedRestored Reference state
      ((AccumulateRuntime.code modulus).execute Reference state) := by
  apply Circuit.borrowedRestored_of_noBorrowedQuantum (AccumulateRuntime.code modulus)
  simp [before, PayloadPreparation.before]

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateState
