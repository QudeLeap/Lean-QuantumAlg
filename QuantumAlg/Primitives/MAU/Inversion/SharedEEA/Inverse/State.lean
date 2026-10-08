/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Agreement
import all QuantumAlg.Core.Execution.Prepared.BasisSupport
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete supported-state correctness of actual native inversion

Only bounded unit-residue support is assumed, for every positive modulus.
This extends the source prime domain, including modulus one. Density positivity lifts
that support to every joint reference coordinate, and actual fixed
preparation establishes the fresh-basis support internally. Exact native
columns then imply equality of the complete quantum-reference output
matrix with the independent canonical XOR target
[LYL+26, sec_EEA/sub_4phase.tex:104-128; dW19, qcnotes.tex:5381,5394,5405].

The complete Output observation aggregates all actual classical records.
Borrowed restoration is proved independently for actual preparation and
the same local unitary, retaining the external reference even though no
physical borrowed register is supplied.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseState

noncomputable section

open Execution InversePreparation

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def preparedSupport (modulus : Nat) (basis : (after modulus.size).register.Index) : Prop :=
  ((assembly modulus.size).symm basis).1 = (InputPreparation.preparation modulus).value ∧
    InverseSpecification.admissible modulus ((assembly modulus.size).symm basis).2

/-- The original local valid-input predicate suffices for complete joint conjugation equality. -/
theorem prepared_conjugation (modulus : Nat) (modulusPositive : 0 < modulus)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : InverseSpecification.valid modulus input.localState) :
    DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (InverseRuntime.program modulus).matrix
          (1 : UnitaryOperator Reference))
        (preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
          (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
          (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal) =
      InverseTarget.density modulus modulusPositive Reference input := by
  apply DensityOperator.applyLocalUnitary_eq_on_basis_support _ (preparedSupport modulus)
  · intro basis outside
    apply preparedDensity_basis_support auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
      (auxiliary_disjoint modulus.size) (InputPreparation.preparation modulus).value
      input.state.quantumMarginal (InverseSpecification.admissible modulus) _ basis outside
    intro old absent
    rw [← Input.localState_quantumMarginal input]
    exact valid old absent
  · intro basis allowed row
    obtain ⟨⟨fresh, old⟩, rfl⟩ := (assembly modulus.size).surjective basis
    have decoded : fresh = (InputPreparation.preparation modulus).value ∧
        InverseSpecification.admissible modulus old := by
      simpa only [preparedSupport, Equiv.symm_apply_apply] using allowed
    obtain ⟨rfl, admitted⟩ := decoded
    exact InverseAgreement.prepared_column modulus modulusPositive old admitted row

/-- Every actual complete run gives the independent full target for arbitrary valid mixed input. -/
theorem finalState_quantumMarginal (modulus : Nat) (modulusPositive : 0 < modulus)
    {shape : CShape} (output : Output (after modulus.size) shape)
    {Reference : Register}
    (input : OracleInput .empty (before modulus.size) Reference)
    (valid : InverseSpecification.valid modulus input.caller.localState) :
    (({ code := InverseRuntime.code modulus, output := output } :
      AlgorithmRun (.quantum AlgorithmGate.model .empty)
        (before modulus.size) (after modulus.size) shape).finalState
        Reference input.state).quantumMarginal =
      InverseTarget.density modulus modulusPositive Reference input.caller := by
  let recorded := input.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have result := AlgorithmRun.finalState_quantumMarginal
    ({ code := InverseRuntime.code modulus, output := output } :
      AlgorithmRun (.quantum AlgorithmGate.model .empty)
        (before modulus.size) (after modulus.size) shape) Reference input.state
  calc
    _ = ((InverseRuntime.code modulus).execute Reference recorded).quantumMarginal := result
    _ = DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (InverseRuntime.program modulus).matrix
          (1 : UnitaryOperator Reference))
        (((InversePreparation.circuit modulus).execute Reference recorded).quantumMarginal) :=
      InverseRuntime.code_quantumMarginal modulus recorded
    _ = DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (InverseRuntime.program modulus).matrix
          (1 : UnitaryOperator Reference))
        (preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
          (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
          (InputPreparation.preparation modulus).normalized Reference recorded.quantumMarginal) :=
      congrArg _ (InversePreparation.execute_preparedDensity modulus recorded)
    _ = InverseTarget.density modulus modulusPositive Reference input.caller := by
      rw [show recorded.quantumMarginal = input.caller.state.quantumMarginal from by
        exact (ExecutionState.mapClassical_quantumMarginal _ _).trans
          input.oracleInput_caller_quantumMarginal.symm]
      exact prepared_conjugation modulus modulusPositive input.caller valid

/-- The full-layout mixed promise holds after aggregating the actual unit output observation. -/
theorem requirement_holds (modulus : Nat) (modulusPositive : 0 < modulus)
    {shape : CShape} (output : Output (after modulus.size) shape)
    {Reference : Register}
    (input : OracleInput .empty (before modulus.size) Reference)
    (valid : InverseSpecification.valid modulus input.caller.localState) :
    (InverseTarget.requirement modulus modulusPositive).Holds input.caller
      (({ code := InverseRuntime.code modulus, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty)
          (before modulus.size) (after modulus.size) shape).finalState
          Reference input.state) := by
  intro value
  cases value with
  | unit =>
    change (StatePromise.mixed
        (InverseTarget.selectedDensity modulus modulusPositive Reference input.caller)
        (InverseTarget.selected_normalized modulus modulusPositive Reference input.caller)).Holds
      (DensityOperator.observeSelectionWithReference (after modulus.size).quantumLayout
        Finset.univ Reference
        (((({ code := InverseRuntime.code modulus, output := output } :
          AlgorithmRun (.quantum AlgorithmGate.model .empty)
            (before modulus.size) (after modulus.size) shape).finalState
            Reference input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
    rw [ExecutionState.executionState_mapClassical_const_block,
      finalState_quantumMarginal modulus modulusPositive output input valid]
    change (InverseTarget.selectedDensity modulus modulusPositive Reference input.caller).matrix =
      ((InverseTarget.selectedDensity modulus modulusPositive Reference input.caller).mass : ℝ) •
        (InverseTarget.selectedDensity modulus modulusPositive Reference input.caller).matrix
    rw [InverseTarget.selected_normalized]
    simp only [one_smul]

/-- Actual preparation and complete inversion restore the mandatory joint borrowed observation. -/
theorem borrowedRestored (modulus : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (InverseRuntime.code modulus).BorrowedRestored Reference state
      ((InverseRuntime.code modulus).execute Reference state) := by
  apply Circuit.borrowedRestored_of_noBorrowedQuantum (InverseRuntime.code modulus)
  simp [before]

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseState
