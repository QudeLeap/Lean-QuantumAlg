/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Initialization

/-!
# Independent full-reference target for scalar-workspace initialization

The prescribed density tensors the fixed auxiliary basis and zero selector
with the complete original quantum-reference density, then uses the exact
physical assembly. Its definition contains no circuit execution, measurement
outcome, native arithmetic action or caller-supplied prepared-state premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredUncompute MAU.Inversion.SharedEEA

/-- Reassociate the actual local assembly while keeping the complete reference unchanged. -/
def initializedJointAssembly (modulus count : Nat) (Reference : Register) :
    (Register.prod (indexedLayout modulus.size count).register
      (Register.prod (InputPreparation.auxiliaryLayout modulus.size).register
        (Register.prod (before modulus.size count).register Reference))).Index ≃
      (Register.prod (after modulus.size count).register Reference).Index where
  toFun value :=
    (initializedAssembly modulus count (value.1, value.2.1, value.2.2.1), value.2.2.2)
  invFun value :=
    let assembled := (initializedAssembly modulus count).symm value.1
    (assembled.1, assembled.2.1, assembled.2.2, value.2)
  left_inv := by
    rintro ⟨selector, auxiliary, original, reference⟩
    dsimp only
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨assembled, reference⟩
    change (initializedAssembly modulus count ((initializedAssembly modulus count).symm assembled),
      reference) = _
    rw [Equiv.apply_symm_apply]

/-- Independently prescribed fixed factors retain every original joint density entry. -/
def initializedDensity (modulus count : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size count).register Reference)) :
    DensityOperator (Register.prod (after modulus.size count).register Reference) :=
  (prependPrepared (prependPrepared input (InPlacePreparation.preparation modulus).normalized)
    (BasisPreparation.zero (indexedLayout modulus.size count)).normalized).reindex
      (initializedJointAssembly modulus count Reference)

/-- The independent preparation target preserves the original full mass. -/
theorem initializedDensity_mass (modulus count : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size count).register Reference)) :
    (initializedDensity modulus count Reference input).mass = input.mass := by
  rw [initializedDensity, DensityOperator.reindex_mass, prependPrepared_mass, prependPrepared_mass]

/-- The mathematical target has the exact two prescribed factors and complete old coherence. -/
theorem initializedDensity_entry (modulus count : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size count).register Reference))
    (selectorRow selectorColumn : (indexedLayout modulus.size count).register.Index)
    (auxiliaryRow auxiliaryColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size count).register Reference).Index) :
    (initializedDensity modulus count Reference input).matrix
      (initializedAssembly modulus count (selectorRow, auxiliaryRow, oldRow.1), oldRow.2)
      (initializedAssembly modulus count (selectorColumn, auxiliaryColumn, oldColumn.1),
        oldColumn.2) =
      ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec selectorRow *
        star ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec
          selectorColumn)) *
      (((InPlacePreparation.preparation modulus).normalized.vec auxiliaryRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec auxiliaryColumn)) *
          input.matrix oldRow oldColumn) := by
  change (DensityOperator.reindex _ (initializedJointAssembly modulus count Reference)).matrix
    (initializedJointAssembly modulus count Reference (selectorRow, auxiliaryRow, oldRow))
    (initializedJointAssembly modulus count Reference
      (selectorColumn, auxiliaryColumn, oldColumn)) = _
  rw [DensityOperator.reindex_entry]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Actual initialization equals the independent full-reference preparation target exactly. -/
theorem initialize_density (modulus count : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (before modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((initializeWork modulus count).execute Reference state).quantumMarginal =
      initializedDensity modulus count Reference state.quantumMarginal := by
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨selectorRow, auxiliaryRow, oldRow⟩, rfl⟩ :=
    (initializedJointAssembly modulus count Reference).surjective row
  obtain ⟨⟨selectorColumn, auxiliaryColumn, oldColumn⟩, rfl⟩ :=
    (initializedJointAssembly modulus count Reference).surjective column
  exact (initialize_entry modulus count state selectorRow selectorColumn
    auxiliaryRow auxiliaryColumn oldRow oldColumn).trans
    (initializedDensity_entry modulus count Reference state.quantumMarginal
      selectorRow selectorColumn
      auxiliaryRow auxiliaryColumn oldRow oldColumn).symm

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
