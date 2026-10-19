/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Affine

/-!
# Exact complete-basis action along the original affine trajectory

The independent cascade target maps each initialized input to the exact
initialized basis at the final affine point. All original exponent values,
prepared work and arbitrary reference labels remain in that same basis.
The equality retains phases and therefore supplies coherent columns for
subsequent full-density comparisons.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredPointAddition

/-- The complete target follows the independent word fold while retaining every other input. -/
lemma cascadeTarget_initialized_wordFold {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (exponent : (exponents p.size count).register.Index) (order : List (Fin count))
    (words : Fin (2 ^ p.size) × Fin (2 ^ p.size))
    {Reference : Register} (reference : Reference.Index) :
    (cascadeTarget E points Reference order).applyVec
      (NormalizedVector.ket (initializedReadyBasis p count
        (inputLabel p.size count exponent words.1 words.2), reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis p count
        (inputLabel p.size count exponent
          (order.foldl (fun current index =>
            wordStep E (points index) (rangeBasis p.size count exponent index) current) words).1
          (order.foldl (fun current index =>
            wordStep E (points index) (rangeBasis p.size count exponent index) current) words).2),
        reference)).vec := by
  induction order generalizing words with
  | nil =>
      rw [cascadeTarget, UnitaryOperator.one_applyVec]
      rfl
  | cons active remaining ih =>
      rw [cascadeTarget, UnitaryOperator.mul_applyVec, stepTarget_apply_ket,
        stepPermutation_initializedReadyBasis, List.foldl_cons]
      exact ih _

/-- On the original affine domain the full target has the exact final point and restored work. -/
lemma cascadeTarget_initialized_affine {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (controls : Fin count → Bool) (exponent : (exponents p.size count).register.Index)
    (encoded : rangeBasis p.size count exponent =
      fun index => BinaryLabelEncoding.bool.encode (controls index))
    (order : List (Fin count)) (initial : AffinePoint E)
    (allowed : AffineTrajectory.admissible E points controls order initial)
    {Reference : Register} (reference : Reference.Index) :
    (cascadeTarget E points Reference order).applyVec
      (NormalizedVector.ket (initializedReadyBasis p count
        (inputLabel p.size count exponent (fieldWord initial.x) (fieldWord initial.y)),
        reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis p count
        (inputLabel p.size count exponent
          (fieldWord (AffineTrajectory.path E points controls order initial).x)
          (fieldWord (AffineTrajectory.path E points controls order initial).y)),
        reference)).vec := by
  have action := cascadeTarget_initialized_wordFold E points exponent order
    (fieldWords initial) reference
  rw [encoded, wordFold_fieldWords E points controls order initial allowed] at action
  exact action

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
