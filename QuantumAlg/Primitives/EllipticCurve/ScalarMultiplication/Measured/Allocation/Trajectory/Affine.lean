/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Words
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Trajectory.Point

/-!
# Affine meaning of the initialized measured scalar trajectory

The original affine path determines the two ordinary coordinate words at every
selected step. Its active exclusions establish the complete initialized input
trajectory, including preservation of the supplied exponents and fixed work.
The path and its domain are independent of the measured execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredUncompute MeasuredPointAddition

/-- The two ordinary coordinate words of an original affine point. -/
def fieldWords {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (P : AffinePoint E) : Fin (2 ^ p.size) × Fin (2 ^ p.size) :=
  (fieldWord P.x, fieldWord P.y)

/-- On its original active domain the independent word step is the affine selected update. -/
theorem wordStep_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Bool) (P : AffinePoint E)
    (allowed : control = true → P ≠ Q ∧ P ≠ AffinePoint.negate Q) :
    wordStep E Q (BinaryLabelEncoding.bool.encode control) (fieldWords P) =
      fieldWords (AffineTrajectory.nextPoint E Q control P) := by
  cases control with
  | false =>
      rw [AffineTrajectory.nextPoint_false]
      rfl
  | true =>
      have domain := genericAddDomain_of_ne_of_ne_negate E P Q
        (allowed rfl).1 (allowed rfl).2
      rw [AffineTrajectory.nextPoint_true E Q P (allowed rfl).1 (allowed rfl).2]
      change translationWords E Q (fieldWord P.x, fieldWord P.y) = _
      rw [translationWords_fieldWords E Q P.x P.y (sub_ne_zero.mpr domain),
        fieldOutput_true E P Q domain]
      rfl

/-- Every admissible original affine path establishes the actual word trajectory condition. -/
theorem wordTrajectory_of_affine {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (order : List (Fin count)) (initial : AffinePoint E)
    (allowed : AffineTrajectory.admissible E points controls order initial) :
    wordTrajectory E points (fun index => BinaryLabelEncoding.bool.encode (controls index))
      order (fieldWords initial) := by
  induction order generalizing initial with
  | nil => trivial
  | cons active remaining ih =>
      refine ⟨?_, ?_⟩
      · intro enabled
        have activeTrue : controls active = true :=
          BinaryLabelEncoding.bool.encode_injective enabled
        exact ⟨initial, rfl, rfl, (allowed.1 activeTrue).1, (allowed.1 activeTrue).2⟩
      · rw [wordStep_fieldWords E (points active) (controls active) initial allowed.1]
        exact ih _ allowed.2

/-- The ordered word fold is exactly the independent affine path in ordinary coordinates. -/
theorem wordFold_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (order : List (Fin count)) (initial : AffinePoint E)
    (allowed : AffineTrajectory.admissible E points controls order initial) :
    order.foldl (fun words index =>
      wordStep E (points index) (BinaryLabelEncoding.bool.encode (controls index)) words)
        (fieldWords initial) =
      fieldWords (AffineTrajectory.path E points controls order initial) := by
  induction order generalizing initial with
  | nil => rfl
  | cons active remaining ih =>
      rw [List.foldl_cons, wordStep_fieldWords E (points active) (controls active) initial
        allowed.1, AffineTrajectory.path]
      exact ih _ allowed.2

/-- Original affine admissibility suffices for the complete initialized input condition. -/
theorem inputTrajectory_of_affine {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (exponent : (exponents p.size count).register.Index)
    (encoded : rangeBasis p.size count exponent =
      fun index => BinaryLabelEncoding.bool.encode (controls index))
    (order : List (Fin count)) (initial : AffinePoint E)
    (allowed : AffineTrajectory.admissible E points controls order initial) :
    inputTrajectory E points order
      (inputLabel p.size count exponent (fieldWord initial.x) (fieldWord initial.y)) := by
  rw [inputTrajectory_inputLabel_iff, encoded]
  exact wordTrajectory_of_affine E points controls order initial allowed

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
