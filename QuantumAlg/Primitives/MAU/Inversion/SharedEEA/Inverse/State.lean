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
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : InverseSpecification.valid modulus input.localState) :
    (({ code := InverseRuntime.code modulus, output := output } :
      AlgorithmRun (before modulus.size) (after modulus.size) shape).finalState
        Reference input.state).quantumMarginal =
      InverseTarget.density modulus modulusPositive Reference input :=
  (preparedUnitary_finalState_quantumMarginal auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) (InputPreparation.preparation modulus)
    (InverseRuntime.program modulus) (InverseRuntime.program_physical modulus)
    output Reference input.state).trans (prepared_conjugation modulus modulusPositive input valid)

/-- The full-layout mixed promise holds after aggregating the actual unit output observation. -/
theorem requirement_holds (modulus : Nat) (modulusPositive : 0 < modulus)
    {shape : CShape} (output : Output (after modulus.size) shape)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : InverseSpecification.valid modulus input.localState) :
    (InverseTarget.requirement modulus modulusPositive).Holds input
      (({ code := InverseRuntime.code modulus, output := output } :
        AlgorithmRun (before modulus.size) (after modulus.size) shape).finalState
          Reference input.state) := by
  intro value
  cases value with
  | unit =>
    change (StatePromise.mixed
        (InverseTarget.selectedDensity modulus modulusPositive Reference input)
        (InverseTarget.selected_normalized modulus modulusPositive Reference input)).Holds
      (DensityOperator.observeSelectionWithReference (after modulus.size).quantumLayout
        Finset.univ Reference
        (((({ code := InverseRuntime.code modulus, output := output } :
          AlgorithmRun (before modulus.size) (after modulus.size) shape).finalState
            Reference input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
    rw [ExecutionState.executionState_mapClassical_const_block,
      finalState_quantumMarginal modulus modulusPositive output input valid]
    change (InverseTarget.selectedDensity modulus modulusPositive Reference input).matrix =
      ((InverseTarget.selectedDensity modulus modulusPositive Reference input).mass : ℝ) •
        (InverseTarget.selectedDensity modulus modulusPositive Reference input).matrix
    rw [InverseTarget.selected_normalized]
    simp only [one_smul]

/-- Actual preparation and complete inversion restore the mandatory joint borrowed observation. -/
theorem borrowedRestored (modulus : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference H) :
    (InverseRuntime.code modulus).BorrowedRestored Reference state
      ((InverseRuntime.code modulus).execute Reference state) :=
  Circuit.borrowedRestored_seq (InversePreparation.circuit modulus)
    (InverseRuntime.body modulus) state
    (Circuit.borrowedRestored_prepare state auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
      (auxiliary_disjoint modulus.size) (InputPreparation.preparation modulus))
    (Circuit.borrowedRestored_unitary_noBorrowed rfl rfl (InverseRuntime.program modulus)
      (InverseRuntime.program_physical modulus)
      ((InversePreparation.circuit modulus).execute Reference state))

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseState
