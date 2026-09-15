/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Specification
import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent full-state target of the prepared XOR inverse

The prescribed original auxiliary basis is tensored with the entire old
quantum-reference state. An independent mathematical permutation preserves
that auxiliary basis and the first word, and XORs the canonical modular
inverse into the second word. This project extends the prime domain of
[LYL+26, sec_EEA/sub_4phase.tex:104-128] to all positive moduli and unit residues,
including the zero inverse modulo one.

The target contains no native circuit or run. Its complete joint-reference
promise observes every live output system and aggregates the actual unit
classical observation. It includes arbitrary original target states and
all coherences, without replacing the input by a sampled basis label.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseTarget

noncomputable section

open Execution InversePreparation

/-- Extend only the independent old-word permutation, preserving every auxiliary basis value. -/
def permutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (after modulus.size).register.Index :=
  (assembly modulus.size).symm.trans
    ((Equiv.prodCongr (Equiv.refl _)
      (InverseSpecification.permutation modulus modulusPositive)).trans
      (assembly modulus.size))

/-- Exact assembly retains fresh coordinates while the independent old arithmetic acts. -/
theorem permutation_assembly (modulus : Nat) (modulusPositive : 0 < modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (old : (before modulus.size).register.Index) :
    permutation modulus modulusPositive (assembly modulus.size (fresh, old)) =
      assembly modulus.size
        (fresh, InverseSpecification.permutation modulus modulusPositive old) := by
  let update : ((InputPreparation.auxiliaryLayout modulus.size).register.Index ×
      (before modulus.size).register.Index) → (after modulus.size).register.Index :=
    fun pair => assembly modulus.size
      (pair.1, InverseSpecification.permutation modulus modulusPositive pair.2)
  change update ((assembly modulus.size).symm (assembly modulus.size (fresh, old))) =
    update (fresh, old)
  exact congrArg update ((assembly modulus.size).symm_apply_apply (fresh, old))

/-- Metadata-free mathematical unitary on exactly the live prepared output context. -/
def operator (modulus : Nat) (modulusPositive : 0 < modulus) :
    UnitaryOperator (after modulus.size).register :=
  UnitaryOperator.ofPerm (R := (after modulus.size).register)
    (permutation modulus modulusPositive).symm

/-- Every mathematical basis column has the complete exact prepared-word action. -/
theorem operator_ket (modulus : Nat) (modulusPositive : 0 < modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (old : (before modulus.size).register.Index) :
    (operator modulus modulusPositive).apply
        (NormalizedVector.ket (R := (after modulus.size).register)
          (assembly modulus.size (fresh, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (assembly modulus.size
          (fresh, InverseSpecification.permutation modulus modulusPositive old)) := by
  have actual := UnitaryOperator.ofPerm_apply_ket (R := (after modulus.size).register)
    (permutation modulus modulusPositive).symm (assembly modulus.size (fresh, old))
  exact actual.trans (congrArg (NormalizedVector.ket (R := (after modulus.size).register))
    (permutation_assembly modulus modulusPositive fresh old))

/-- Independent prescribed tensor and canonical arithmetic on the complete original joint state. -/
def density (modulus : Nat) (modulusPositive : 0 < modulus) (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    DensityOperator (Register.prod (after modulus.size).register Reference) :=
  DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor (operator modulus modulusPositive) (1 : UnitaryOperator Reference))
    (preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
      (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
      (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal)

/-- The independent target is normalized for every normalized incoming joint state. -/
theorem density_normalized (modulus : Nat) (modulusPositive : 0 < modulus) (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    (density modulus modulusPositive Reference input).IsNormalized := by
  change (density modulus modulusPositive Reference input).mass = 1
  have unitary := DensityOperator.applyUnitary_mass
    (R := Register.prod (after modulus.size).register Reference)
    (UnitaryOperator.prodTensor (operator modulus modulusPositive) (1 : UnitaryOperator Reference))
    (show DensityOperator (Register.prod (after modulus.size).register Reference) from
      preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
        (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
        (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal)
  have preparation := preparedDensity_mass auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) (InputPreparation.preparation modulus).normalized
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
  exact density_normalized modulus modulusPositive Reference input

/-- Promise the complete independent joint target, aggregating every classical record. -/
def requirement (modulus : Nat) (modulusPositive : 0 < modulus) :
    StateRequirement (before modulus.size) (after modulus.size) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (selectedDensity modulus modulusPositive Reference input)
      (selected_normalized modulus modulusPositive Reference input)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseTarget
