/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Initialization
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Domain

/-!
# Original-input support establishes the measured body's internal domain

The input predicate constrains only the supplied coordinate words when the
supplied coherent control is active. It retains the original affine point
exclusions. No arithmetic auxiliary, internal selector or measurement result
is supplied by the caller. Actual preparation establishes those internal
values before the accepted body is invoked, including on entangled inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MeasuredUncompute

/-- Only active supplied affine coordinates carry the original two point exclusions. -/
def inputAdmissible {p : Nat} (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    (original : (before p.size).register.Index) : Prop :=
  ∃ (control : Fin 2) (x y : Fin (2 ^ p.size)),
    original = inputLabel p.size control x y ∧
      (control = 1 → ∃ P : AffinePoint E,
        x.val = P.x.val ∧ y.val = P.y.val ∧ P ≠ Q ∧ P ≠ AffinePoint.negate Q)

/-- Actual initialization derives the internal prepared support from the original input domain. -/
lemma initialize_support {p : Nat} (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ input : (Register.prod (before p.size).register Reference).Index,
      ¬inputAdmissible E Q input.1 → state.quantumMarginal.matrix input input = 0) :
    ∀ output : (Register.prod (after p.size).register Reference).Index,
      ¬admissible E Q ((ContextPermutation.basis (body_entries p.size)).symm output.1) →
        ((initializeWork p).execute environment Reference state).quantumMarginal.matrix output
          output = 0 := by
  classical
  rintro ⟨basis, reference⟩ outside
  obtain ⟨⟨selector, auxiliary, original⟩, rfl⟩ :=
    (initializedAssembly p).surjective basis
  refine (initialize_entry p state selector selector auxiliary auxiliary
    (original, reference) (original, reference)).trans ?_
  by_cases selectorZero : selector = (BasisPreparation.zero (selectorLayout p.size)).value
  · subst selector
    by_cases auxiliaryFixed : auxiliary = (InPlacePreparation.preparation p).value
    · subst auxiliary
      have originalOutside : ¬inputAdmissible E Q original := by
        rintro ⟨control, x, y, rfl, allowed⟩
        apply outside
        refine ⟨control, x, y, ?_, allowed⟩
        rw [initializedAssembly_input]
        exact (ContextPermutation.basis (body_entries p.size)).symm_apply_apply _
      rw [support (original, reference) originalOutside, mul_zero, mul_zero]
    · have amplitude : (InPlacePreparation.preparation p).normalized.vec auxiliary = 0 := by
        simp only [BasisPreparation.normalized, NormalizedVector.ket_apply, if_neg auxiliaryFixed]
      rw [amplitude, zero_mul, zero_mul, mul_zero]
  · have amplitude :
        (BasisPreparation.zero (selectorLayout p.size)).normalized.vec selector = 0 := by
      simp only [BasisPreparation.normalized, NormalizedVector.ket_apply, if_neg selectorZero]
    rw [amplitude, zero_mul, zero_mul]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
