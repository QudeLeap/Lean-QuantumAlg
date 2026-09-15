/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.Agreement
import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.Prepared.BasisSupport
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
import all QuantumAlg.Core.Execution.Borrowed.Empty

/-!
# Complete mixed-state correctness of actual modular-add division

The local support admits every original unit denominator, canonical modular
numerator and arbitrary modular target, and either live flag value. Positivity
lifts that support to every joint reference coordinate; actual fixed preparation
supplies the fresh-basis support internally. The complete density equals the
independent mathematical target, preserving every auxiliary and source field
[LYL+26, sec_EEA/sub_regshare.tex:16-26; sec_EEA/sub_4phase.tex:104-128;
dW19, qcnotes.tex:5381,5394,5405]. General positive moduli and modular-add division
are project extensions of the source's prime-domain inversion construction.
Borrowed/reference restoration is a separate proof on the same actual code.
-/

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionTarget

noncomputable section

open Execution ExecutionLayout Inversion.SharedEEA

/-- Independent prescribed tensor and canonical arithmetic on the complete original joint state. -/
def density (modulus : Nat) (modulusPositive : 0 < modulus) (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    DensityOperator (Register.prod (after modulus.size).register Reference) :=
  DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor (operator modulus modulusPositive) (1 : UnitaryOperator Reference))
    (preparedDensity PayloadPreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
      (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth
        modulus.size)) (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size
        (payloadWidth modulus.size))
      (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal)

/-- The independent target is normalized for every normalized incoming joint state. -/
theorem divisionTarget_density_normalized (modulus : Nat) (modulusPositive : 0 < modulus)
  (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    (density modulus modulusPositive Reference input).IsNormalized := by
  change (density modulus modulusPositive Reference input).mass = 1
  have unitary := DensityOperator.applyUnitary_mass
    (R := Register.prod (after modulus.size).register Reference)
    (UnitaryOperator.prodTensor (operator modulus modulusPositive) (1 : UnitaryOperator Reference))
    (show DensityOperator (Register.prod (after modulus.size).register Reference) from
      preparedDensity PayloadPreparation.auxiliaryKey (InputPreparation.auxiliaryLayout
        modulus.size)
        (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth
          modulus.size)) (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size
          (payloadWidth modulus.size))
        (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal)
  have preparation := preparedDensity_mass PayloadPreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
      (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth
      modulus.size))
    (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (payloadWidth
      modulus.size)) (InputPreparation.preparation modulus).normalized
    Reference input.state.quantumMarginal
  exact unitary.trans (preparation.trans
    ((ExecutionState.quantumMarginal_mass input.state).trans input.normalized))

private def selectedDensity (modulus : Nat) (modulusPositive : 0 < modulus) (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    DensityOperator (Register.prod
      ((after modulus.size).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (after modulus.size).quantumLayout
    Finset.univ Reference (density modulus modulusPositive Reference input)

private theorem selected_normalized (modulus : Nat) (modulusPositive : 0 < modulus)
    (Reference : Register) (input : Input (before modulus.size) Reference) :
    (selectedDensity modulus modulusPositive Reference input).IsNormalized := by
  change (selectedDensity modulus modulusPositive Reference input).mass = 1
  rw [selectedDensity, DensityOperator.observeSelectionWithReference_mass]
  exact divisionTarget_density_normalized modulus modulusPositive Reference input

/-- Promise the complete independent joint target, aggregating every classical record. -/
def requirement (modulus : Nat) (modulusPositive : 0 < modulus) :
    StateRequirement (before modulus.size) (after modulus.size) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (selectedDensity modulus modulusPositive Reference input)
      (selected_normalized modulus modulusPositive Reference input)


end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionTarget

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionStateProof

noncomputable section

open Execution ExecutionLayout Inversion.SharedEEA

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def preparedSupport (modulus : Nat) (basis : (after modulus.size).register.Index) : Prop :=
  ((PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)).symm basis).1 =
    (InputPreparation.preparation modulus).value ∧
    ExecutionLayout.admissible modulus ((PayloadPreparation.assembly modulus.size (payloadWidth
      modulus.size)).symm basis).2

/-- The original local valid-input predicate suffices for complete joint conjugation equality. -/
theorem divisionState_prepared_conjugation (modulus : Nat) (modulusPositive : 0 < modulus)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : ExecutionLayout.valid modulus input.localState) :
    DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (ExecutionRuntime.program modulus).matrix
          (1 : UnitaryOperator Reference))
        (preparedDensity PayloadPreparation.auxiliaryKey (InputPreparation.auxiliaryLayout
          modulus.size)
          (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth
            modulus.size)) (PayloadPreparation.payloadPreparation_auxiliary_disjoint
            modulus.size (payloadWidth modulus.size))
          (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal) =
      ExecutionTarget.density modulus modulusPositive Reference input := by
  apply DensityOperator.applyLocalUnitary_eq_on_basis_support _ (preparedSupport modulus)
  · intro basis outside
    apply preparedDensity_basis_support PayloadPreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
        (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth
        modulus.size))
      (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (payloadWidth
        modulus.size)) (InputPreparation.preparation modulus).value
      input.state.quantumMarginal (ExecutionLayout.admissible modulus) _ basis outside
    intro old absent
    rw [← Input.localState_quantumMarginal input]
    exact valid old absent
  · intro basis allowed row
    obtain ⟨⟨fresh, old⟩, rfl⟩ := (PayloadPreparation.assembly modulus.size (payloadWidth
      modulus.size)).surjective basis
    have decoded : fresh = (InputPreparation.preparation modulus).value ∧
        ExecutionLayout.admissible modulus old := by
      simpa only [preparedSupport, Equiv.symm_apply_apply] using allowed
    obtain ⟨rfl, admitted⟩ := decoded
    exact ExecutionAgreement.divisionAgreement_prepared_column modulus modulusPositive old
      admitted row

/-- Every actual complete run gives the independent full target for arbitrary valid mixed input. -/
theorem divisionState_finalState_quantumMarginal (modulus : Nat) (modulusPositive : 0 < modulus)
    {shape : CShape} (output : Output (after modulus.size) shape)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : ExecutionLayout.valid modulus input.localState) :
    (({ code := ExecutionRuntime.code modulus, output := output } :
      AlgorithmRun (before modulus.size) (after modulus.size) shape).finalState
        Reference input.state).quantumMarginal =
      ExecutionTarget.density modulus modulusPositive Reference input :=
  (preparedUnitary_finalState_quantumMarginal PayloadPreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
      (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth
      modulus.size))
    (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (payloadWidth
      modulus.size)) (InputPreparation.preparation modulus)
    (ExecutionRuntime.program modulus) (ExecutionRuntime.divisionExecution_program_physical modulus)
    output Reference input.state).trans (divisionState_prepared_conjugation modulus
      modulusPositive input valid)

/-- The full-layout mixed promise holds after aggregating the actual unit output observation. -/
theorem divisionState_requirement_holds (modulus : Nat) (modulusPositive : 0 < modulus)
    {shape : CShape} (output : Output (after modulus.size) shape)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : ExecutionLayout.valid modulus input.localState) :
    (ExecutionTarget.requirement modulus modulusPositive).Holds input
      (({ code := ExecutionRuntime.code modulus, output := output } :
        AlgorithmRun (before modulus.size) (after modulus.size) shape).finalState
          Reference input.state) := by
  intro value
  cases value with
  | unit =>
    change (StatePromise.mixed
        (ExecutionTarget.selectedDensity modulus modulusPositive Reference input)
        (ExecutionTarget.selected_normalized modulus modulusPositive Reference input)).Holds
      (DensityOperator.observeSelectionWithReference (after modulus.size).quantumLayout
        Finset.univ Reference
        (((({ code := ExecutionRuntime.code modulus, output := output } :
          AlgorithmRun (before modulus.size) (after modulus.size) shape).finalState
            Reference input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
    rw [ExecutionState.executionState_mapClassical_const_block,
      divisionState_finalState_quantumMarginal modulus modulusPositive output input valid]
    change (ExecutionTarget.selectedDensity modulus modulusPositive Reference input).matrix =
      ((ExecutionTarget.selectedDensity modulus modulusPositive Reference input).mass : ℝ) •
        (ExecutionTarget.selectedDensity modulus modulusPositive Reference input).matrix
    rw [ExecutionTarget.selected_normalized]
    simp only [one_smul]

/-- Actual preparation and complete division restore the mandatory joint borrowed observation. -/
theorem divisionState_borrowedRestored (modulus : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference H) :
    (ExecutionRuntime.code modulus).BorrowedRestored Reference state
      ((ExecutionRuntime.code modulus).execute Reference state) :=
  Circuit.borrowedRestored_seq (PayloadPreparation.circuit modulus (payloadWidth modulus.size))
    (PayloadRuntime.circuit modulus.size (payloadWidth modulus.size)
      (ExecutionRuntime.nativeProgram modulus)
        (ExecutionRuntime.divisionExecution_native_within modulus)) state
    (Circuit.borrowedRestored_prepare state PayloadPreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
        (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth
        modulus.size))
      (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (payloadWidth
        modulus.size)) (InputPreparation.preparation modulus))
    (Circuit.borrowedRestored_unitary_noBorrowed rfl rfl (ExecutionRuntime.program modulus)
      (ExecutionRuntime.divisionExecution_program_physical modulus)
      ((PayloadPreparation.circuit modulus (payloadWidth modulus.size)).execute Reference state))

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionStateProof
