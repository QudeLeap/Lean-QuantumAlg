/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Runtime.Layout
import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent full-state target for modular-add inversion

The prescribed auxiliary basis accompanies the complete original joint
state. A mathematical permutation adds the canonical inverse into the
arbitrary target and preserves the original input, flag, and auxiliaries.
The target specifies every live system and every external-reference
coherence without a circuit, execution record, or resource projection.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AccumulateTarget

noncomputable section

open Execution AccumulateRuntime

/-- Original unit and canonical-target support permits every mixed state and reference extension. -/
def valid (modulus : Nat)
    (state : ExecutionState (Store (before modulus.size)) (before modulus.size).register) : Prop :=
  ∀ basis, ¬AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size basis) →
    state.quantumMarginal.matrix basis basis = 0

/-- Independent modular data arithmetic on the exact original supplied quantum basis. -/
def inputPermutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).trans
    ((AccumulateSpecification.permutation modulus modulusPositive).trans
      (inputBasisEquiv modulus.size).symm)

/-- Actual original data labels read back the same independent mathematical permutation. -/
theorem accumulateTarget_input_read (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) :
    inputBasisEquiv modulus.size (inputPermutation modulus modulusPositive old) =
      AccumulateSpecification.permutation modulus modulusPositive
        (inputBasisEquiv modulus.size old) :=
  (inputBasisEquiv modulus.size).apply_symm_apply _

/-- Modulus one preserves every original quantum label, including arbitrary flags and padding. -/
theorem accumulateTarget_input_one (old : (before (1 : Nat).size).register.Index) :
    inputPermutation 1 (by decide) old = old := by
  apply (inputBasisEquiv (1 : Nat).size).injective
  rw [accumulateTarget_input_read, AccumulateSpecification.accumulateSpecification_one]

/-- Extend only the mathematical data action and preserve every auxiliary label. -/
def permutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (after modulus.size).register.Index :=
  (PayloadPreparation.assembly modulus.size (modulus.size + 1)).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (inputPermutation modulus modulusPositive)).trans
      (PayloadPreparation.assembly modulus.size (modulus.size + 1)))

/-- Complete mathematical assembly retains every fresh coordinate and updates only original data. -/
theorem accumulateTarget_assembly (modulus : Nat) (modulusPositive : 0 < modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (old : (before modulus.size).register.Index) :
    permutation modulus modulusPositive
        (PayloadPreparation.assembly modulus.size (modulus.size + 1) (fresh, old)) =
      PayloadPreparation.assembly modulus.size (modulus.size + 1)
        (fresh, inputPermutation modulus modulusPositive old) := by
  let update := fun pair : (InputPreparation.auxiliaryLayout modulus.size).register.Index ×
      (before modulus.size).register.Index =>
    PayloadPreparation.assembly modulus.size (modulus.size + 1)
      (pair.1, inputPermutation modulus modulusPositive pair.2)
  change update ((PayloadPreparation.assembly modulus.size (modulus.size + 1)).symm
    (PayloadPreparation.assembly modulus.size (modulus.size + 1) (fresh, old))) =
      update (fresh, old)
  exact congrArg update
    ((PayloadPreparation.assembly modulus.size (modulus.size + 1)).symm_apply_apply (fresh, old))

/-- Mathematical unitary on the complete prepared context, containing no native event metadata. -/
def operator (modulus : Nat) (modulusPositive : 0 < modulus) :
    UnitaryOperator (after modulus.size).register :=
  UnitaryOperator.ofPerm (R := (after modulus.size).register)
    (permutation modulus modulusPositive).symm

/-- The exact mathematical basis action retains its full amplitude and every live field. -/
theorem accumulateTarget_ket (modulus : Nat) (modulusPositive : 0 < modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (old : (before modulus.size).register.Index) :
    (operator modulus modulusPositive).apply
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (modulus.size + 1) (fresh, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (PayloadPreparation.assembly modulus.size (modulus.size + 1)
          (fresh, inputPermutation modulus modulusPositive old)) := by
  have actual := UnitaryOperator.ofPerm_apply_ket (R := (after modulus.size).register)
    (permutation modulus modulusPositive).symm
    (PayloadPreparation.assembly modulus.size (modulus.size + 1) (fresh, old))
  exact actual.trans (congrArg (NormalizedVector.ket (R := (after modulus.size).register))
    (accumulateTarget_assembly modulus modulusPositive fresh old))

/-- Independent tensor preparation and arithmetic on the complete incoming joint state. -/
def density (modulus : Nat) (modulusPositive : 0 < modulus) (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    DensityOperator (Register.prod (after modulus.size).register Reference) :=
  DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor (operator modulus modulusPositive) (1 : UnitaryOperator Reference))
    (preparedDensity PayloadPreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
      (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (modulus.size + 1))
      (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (modulus.size + 1))
      (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal)

/-- The independently prescribed complete joint target is normalized for every normalized input. -/
theorem accumulateTarget_normalized (modulus : Nat) (modulusPositive : 0 < modulus)
    (Reference : Register) (input : Input (before modulus.size) Reference) :
    (density modulus modulusPositive Reference input).IsNormalized := by
  change (density modulus modulusPositive Reference input).mass = 1
  have unitary := DensityOperator.applyUnitary_mass
    (R := Register.prod (after modulus.size).register Reference)
    (UnitaryOperator.prodTensor (operator modulus modulusPositive) (1 : UnitaryOperator Reference))
    (show DensityOperator (Register.prod (after modulus.size).register Reference) from
      preparedDensity PayloadPreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (modulus.size + 1))
        (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (modulus.size + 1))
        (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal)
  have preparation := preparedDensity_mass PayloadPreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (modulus.size + 1))
    (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size (modulus.size + 1))
    (InputPreparation.preparation modulus).normalized Reference input.state.quantumMarginal
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
  exact accumulateTarget_normalized modulus modulusPositive Reference input

/-- Promise the complete independent joint output, aggregating actual classical records. -/
def requirement (modulus : Nat) (modulusPositive : 0 < modulus) :
    StateRequirement (before modulus.size) (after modulus.size) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (selectedDensity modulus modulusPositive Reference input)
      (selected_normalized modulus modulusPositive Reference input)

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateTarget
