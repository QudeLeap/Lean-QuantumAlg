/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Coordinates
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Density

/-!
# Original supplied inputs establish the initialized point-step domain

The original predicate mentions only the supplied words and selected exponent.
The actual fixed preparations establish every internal arithmetic and selector
condition. The density proof retains the complete arbitrary external reference
and all original coherence; it makes no input independence assumption.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredUncompute

/-- A selected first step constrains supplied affine words only when its exponent is active. -/
def inputStepAdmissible {p : Nat} (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    {count : Nat} (active : Fin count) (original : (before p.size count).register.Index) : Prop :=
  ∃ (exponent : (exponents p.size count).register.Index) (x y : Fin (2 ^ p.size)),
    original = inputLabel p.size count exponent x y ∧
      (rangeBasis p.size count exponent active = 1 → ∃ P : AffinePoint E,
        x.val = P.x.val ∧ y.val = P.y.val ∧ P ≠ Q ∧ P ≠ AffinePoint.negate Q)

/-- The actual prepared basis satisfies the internal domain using only the original input. -/
theorem initializedReadyBasis_admissible {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (original : (before p.size count).register.Index)
    (allowed : inputStepAdmissible E Q active original) :
    stepAdmissible E Q active (initializedReadyBasis p count original) := by
  obtain ⟨exponent, x, y, rfl, valid⟩ := allowed
  rw [stepAdmissible_iff]
  refine ⟨initializedReadyBasis_selector p count _, x, y,
    initializedReadyBasis_shared p count exponent x y, ?_⟩
  rw [initializedReadyBasis_exponent]
  exact valid

/-- Independent initialization puts zero mass outside every established ready-basis predicate. -/
theorem initializedDensity_support (modulus count : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size count).register Reference))
    (allowed : (before modulus.size count).register.Index → Prop)
    (prepared : (readyContext modulus.size count).register.Index → Prop)
    (establish : ∀ original, allowed original →
      prepared (initializedReadyBasis modulus count original))
    (support : ∀ original : (Register.prod (before modulus.size count).register Reference).Index,
      ¬allowed original.1 → input.matrix original original = 0) :
    ∀ output : (Register.prod (after modulus.size count).register Reference).Index,
      ¬prepared ((ContextPermutation.basis (body_entries modulus.size count)).symm output.1) →
        (initializedDensity modulus count Reference input).matrix output output = 0 := by
  classical
  rintro ⟨basis, reference⟩ outside
  obtain ⟨⟨selector, auxiliary, original⟩, rfl⟩ :=
    (initializedAssembly modulus count).surjective basis
  refine (initializedDensity_entry modulus count Reference input selector selector
    auxiliary auxiliary (original, reference) (original, reference)).trans ?_
  by_cases selectorZero :
      selector = (BasisPreparation.zero (indexedLayout modulus.size count)).value
  · subst selector
    by_cases auxiliaryFixed : auxiliary = (InPlacePreparation.preparation modulus).value
    · subst auxiliary
      have originalOutside : ¬allowed original := fun valid => outside (establish original valid)
      rw [support (original, reference) originalOutside, mul_zero, mul_zero]
    · have amplitude : (InPlacePreparation.preparation modulus).normalized.vec auxiliary = 0 := by
        simp only [BasisPreparation.normalized, NormalizedVector.ket_apply, if_neg auxiliaryFixed]
      rw [amplitude, zero_mul, zero_mul, mul_zero]
  · have amplitude :
        (BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec selector = 0 := by
      simp only [BasisPreparation.normalized, NormalizedVector.ket_apply, if_neg selectorZero]
    rw [amplitude, zero_mul, zero_mul]

/-- Actual initialization establishes a selected first step's full joint support from input. -/
theorem initialize_step_support {p : Nat} (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    {count : Nat} (active : Fin count) {Reference : Register} {History : Type} [Fintype History]
    (state : State (before p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ input : (Register.prod (before p.size count).register Reference).Index,
      ¬inputStepAdmissible E Q active input.1 → state.quantumMarginal.matrix input input = 0) :
    ∀ output : (Register.prod (after p.size count).register Reference).Index,
      ¬stepAdmissible E Q active
        ((ContextPermutation.basis (body_entries p.size count)).symm output.1) →
          ((initializeWork p count).execute Reference state).quantumMarginal.matrix
            output output = 0 := by
  rw [initialize_density]
  exact initializedDensity_support p count Reference state.quantumMarginal
    (inputStepAdmissible E Q active) (stepAdmissible E Q active)
    (initializedReadyBasis_admissible E Q active) support

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
