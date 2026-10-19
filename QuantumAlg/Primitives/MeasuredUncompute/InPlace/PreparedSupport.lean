/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Domain
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Measurement
import all QuantumAlg.Core.Execution.Prepared.BasisSupport
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual prepared support before the measured arithmetic body

The fixed auxiliary preparation and retained finite result cells are the
actual two instructions preceding the arithmetic body. Their complete
matrix has the original two-word support and the prescribed fresh basis,
with every reference coordinate retained
[LYL+26, sec_point_add/sec_point_add.tex:45-105].
No measurement result or intermediate arithmetic property is an input
assumption. Allocation of classical cells changes only the basis labels
of the same physical quantum layout.
-/

namespace QuantumAlg.MeasuredUncompute.InPlacePreparedSupport

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MAU.Inversion.SharedEEA InversePreparation

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Allowed prepared labels specify only fixed fresh bits and the original two-word domain. -/
def prepared (modulus : Nat) (basis : (after modulus.size).register.Index) : Prop :=
  ((assembly modulus.size).symm basis).1 = (InPlacePreparation.preparation modulus).value ∧
    InPlaceDomain.admissible modulus ((assembly modulus.size).symm basis).2

/-- The same support follows the exact wire correspondence after finite-cell allocation. -/
def admissible (modulus : Nat)
    (basis : (NumeratorMeasurement.context modulus.size).register.Index) : Prop :=
  prepared modulus
    ((MeasurementCells.basisEquiv (after modulus.size) 2 modulus.size).symm basis)

/-- Every allowed actual label is the fixed preparation beside two original-domain words. -/
lemma admissible_cases (modulus : Nat)
    (basis : (NumeratorMeasurement.context modulus.size).register.Index)
    (allowed : admissible modulus basis) :
    ∃ value numerator : Fin (2 ^ modulus.size),
      0 < value.val ∧ value.val < modulus ∧ numerator.val < modulus ∧
      basis = MeasurementCells.basisEquiv (after modulus.size) 2 modulus.size
        (assembly modulus.size ((InPlacePreparation.preparation modulus).value,
          (inputBasisEquiv modulus.size).symm (value, numerator))) := by
  let coordinate := (assembly modulus.size).trans
    (MeasurementCells.basisEquiv (after modulus.size) 2 modulus.size)
  obtain ⟨⟨fresh, old⟩, rfl⟩ := coordinate.surjective basis
  have decoded : fresh = (InPlacePreparation.preparation modulus).value ∧
      InPlaceDomain.admissible modulus old := by
    simpa only [admissible, prepared, coordinate, Equiv.trans_apply,
      Equiv.symm_apply_apply] using allowed
  obtain ⟨rfl, positive, bounded, numeratorBound⟩ := decoded
  refine ⟨(inputBasisEquiv modulus.size old).1, (inputBasisEquiv modulus.size old).2,
    positive, bounded, numeratorBound, ?_⟩
  exact congrArg
    (fun original => coordinate ((InPlacePreparation.preparation modulus).value, original))
    ((inputBasisEquiv modulus.size).symm_apply_apply old).symm

/-- The independent prepared density contains the fixed fresh basis and the full old state. -/
def density (modulus : Nat) (Reference : Register)
    (state : DensityOperator (Register.prod (before modulus.size).register Reference)) :
    DensityOperator (Register.prod (after modulus.size).register Reference) :=
  preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
    (InPlacePreparation.preparation modulus).normalized Reference state

/-- Local validity implies every forbidden prepared diagonal vanishes. -/
lemma prepared_diagonal (modulus : Nat) {Reference : Register}
    (input : Input (before modulus.size) Reference)
    (valid : InPlaceDomain.valid modulus input.localState)
    (basis : (after modulus.size).register.Index) (outside : ¬prepared modulus basis) :
    (density modulus Reference input.state.quantumMarginal).marginalLeft.matrix
      basis basis = 0 := by
  apply preparedDensity_basis_support auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) (InPlacePreparation.preparation modulus).value
    input.state.quantumMarginal (InPlaceDomain.admissible modulus) _ basis outside
  intro old absent
  rw [← Input.localState_quantumMarginal input]
  exact valid old absent

/-- Both actual allocations produce precisely the independent prepared full joint matrix. -/
lemma actual_density (modulus : Nat) {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((NumeratorMeasurement.allocate modulus.size).execute environment Reference
      ((InPlacePreparation.circuit modulus).execute environment Reference state)).quantumMarginal =
      (density modulus Reference state.quantumMarginal).reindex
        (MeasurementCells.jointBasisEquiv (after modulus.size) 2 modulus.size Reference) := by
  refine (MeasurementCells.allocate_quantumMarginal environment
    (model := .quantum AlgorithmGate.model .empty)
    (after modulus.size) 2 modulus.size
    ((InPlacePreparation.circuit modulus).execute environment Reference state)).trans ?_
  apply congrArg (fun value :
    DensityOperator (Register.prod (after modulus.size).register Reference) =>
      value.reindex
        (MeasurementCells.jointBasisEquiv (after modulus.size) 2 modulus.size Reference))
  exact InPlacePreparation.execute_preparedDensity modulus state

/-- The actual pre-body state has the required support in every full reference coordinate. -/
lemma actual_joint_diagonal (modulus : Nat) {Reference : Register}
    (input : Input (before modulus.size) Reference)
    (valid : InPlaceDomain.valid modulus input.localState)
    (basis : (Register.prod (NumeratorMeasurement.context modulus.size).register Reference).Index)
    (outside : ¬admissible modulus basis.1) :
    ((NumeratorMeasurement.allocate modulus.size).execute environment Reference
      ((InPlacePreparation.circuit modulus).execute environment Reference
        (input.state.mapClassical (fun stored => (stored, ((), ())))))).quantumMarginal.matrix
        basis basis = 0 := by
  rw [actual_density, ExecutionState.mapClassical_quantumMarginal]
  erw [DensityOperator.reindex_entry]
  exact DensityOperator.joint_diagonal_zero_of_marginal_diagonal_zero
    (density modulus Reference input.state.quantumMarginal) _
    (prepared_diagonal modulus input valid _ outside) basis.2

end

end QuantumAlg.MeasuredUncompute.InPlacePreparedSupport
