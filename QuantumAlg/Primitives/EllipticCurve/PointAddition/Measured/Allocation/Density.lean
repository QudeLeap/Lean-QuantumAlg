/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Initialization

/-!
# Independent full-reference target for point-addition initialization

The prescribed density tensors the fixed auxiliary basis and zero selector
with the complete original quantum-reference density, then uses the exact
physical assembly. Its definition contains no circuit execution, measurement
outcome, native arithmetic action or caller-supplied prepared-state premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MeasuredUncompute MAU.Inversion.SharedEEA

/-- Reassociate the actual local assembly while keeping the complete reference unchanged. -/
def initializedJointAssembly (modulus : Nat) (Reference : Register) :
    (Register.prod (selectorLayout modulus.size).register
      (Register.prod (InputPreparation.auxiliaryLayout modulus.size).register
        (Register.prod (before modulus.size).register Reference))).Index ≃
      (Register.prod (after modulus.size).register Reference).Index where
  toFun value :=
    (initializedAssembly modulus (value.1, value.2.1, value.2.2.1), value.2.2.2)
  invFun value :=
    let assembled := (initializedAssembly modulus).symm value.1
    (assembled.1, assembled.2.1, assembled.2.2, value.2)
  left_inv := by
    rintro ⟨selector, auxiliary, original, reference⟩
    dsimp only
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨assembled, reference⟩
    change (initializedAssembly modulus ((initializedAssembly modulus).symm assembled),
      reference) = _
    rw [Equiv.apply_symm_apply]

/-- Independently prescribed fixed factors retain every original joint density entry. -/
def initializedDensity (modulus : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size).register Reference)) :
    DensityOperator (Register.prod (after modulus.size).register Reference) :=
  (prependPrepared (prependPrepared input (InPlacePreparation.preparation modulus).normalized)
    (BasisPreparation.zero (selectorLayout modulus.size)).normalized).reindex
      (initializedJointAssembly modulus Reference)

/-- The independent preparation target preserves the original full mass. -/
lemma initializedDensity_mass (modulus : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size).register Reference)) :
    (initializedDensity modulus Reference input).mass = input.mass := by
  rw [initializedDensity, DensityOperator.reindex_mass, prependPrepared_mass, prependPrepared_mass]

/-- The mathematical target has the exact two prescribed factors and complete old coherence. -/
lemma initializedDensity_entry (modulus : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size).register Reference))
    (selectorRow selectorColumn : (selectorLayout modulus.size).register.Index)
    (auxiliaryRow auxiliaryColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size).register Reference).Index) :
    (initializedDensity modulus Reference input).matrix
      (initializedAssembly modulus (selectorRow, auxiliaryRow, oldRow.1), oldRow.2)
      (initializedAssembly modulus (selectorColumn, auxiliaryColumn, oldColumn.1), oldColumn.2) =
      ((BasisPreparation.zero (selectorLayout modulus.size)).normalized.vec selectorRow *
        star ((BasisPreparation.zero (selectorLayout modulus.size)).normalized.vec
          selectorColumn)) *
      (((InPlacePreparation.preparation modulus).normalized.vec auxiliaryRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec auxiliaryColumn)) *
          input.matrix oldRow oldColumn) := by
  change (DensityOperator.reindex _ (initializedJointAssembly modulus Reference)).matrix
    (initializedJointAssembly modulus Reference (selectorRow, auxiliaryRow, oldRow))
    (initializedJointAssembly modulus Reference (selectorColumn, auxiliaryColumn, oldColumn)) = _
  rw [DensityOperator.reindex_entry]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Actual initialization equals the independent full-reference preparation target exactly. -/
lemma initialize_density (modulus : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((initializeWork modulus).execute environment Reference state).quantumMarginal =
      initializedDensity modulus Reference state.quantumMarginal := by
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨selectorRow, auxiliaryRow, oldRow⟩, rfl⟩ :=
    (initializedJointAssembly modulus Reference).surjective row
  obtain ⟨⟨selectorColumn, auxiliaryColumn, oldColumn⟩, rfl⟩ :=
    (initializedJointAssembly modulus Reference).surjective column
  exact (initialize_entry modulus state selectorRow selectorColumn
    auxiliaryRow auxiliaryColumn oldRow oldColumn).trans
    (initializedDensity_entry modulus Reference state.quantumMarginal selectorRow selectorColumn
      auxiliaryRow auxiliaryColumn oldRow oldColumn).symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
