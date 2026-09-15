/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Mathematics

/-!
# Independent affine trajectories for selected point addition

Each selected step adds its fixed point on the original generic affine
domain. Disabled steps and exceptional active inputs use the identity
fallback. The admissibility predicate checks only active exclusions along
this same mathematical trajectory, independently of any executable backend.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace AffineTrajectory

noncomputable section

open GenericPointAddition.InPlace

/-- Total selected affine update with the original identity fallback outside its generic domain. -/
def nextPoint {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Bool) (P : AffinePoint E) : AffinePoint E := by
  classical
  exact if active : control = true then
    if same : P = Q then P
    else if inverse : P = AffinePoint.negate Q then P
    else genericAddPoint E P Q (genericAddDomain_of_ne_of_ne_negate E P Q same inverse)
  else P

/-- A disabled step fixes every affine input without an exceptional-domain premise. -/
theorem nextPoint_false {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q P : AffinePoint E) : nextPoint E Q false P = P := by
  simp only [nextPoint, Bool.false_eq_true, ↓reduceDIte]

/-- An enabled original-domain input follows the independent generic affine formula. -/
theorem nextPoint_true {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q P : AffinePoint E) (different : P ≠ Q) (inverseDifferent : P ≠ AffinePoint.negate Q) :
    nextPoint E Q true P =
      genericAddPoint E P Q
        (genericAddDomain_of_ne_of_ne_negate E P Q different inverseDifferent) := by
  simp only [nextPoint, ↓reduceDIte, different, inverseDifferent]

/-- Only an active step needs affine exclusions to represent the corresponding group update. -/
theorem nextPoint_toGroupPoint {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Bool) (P : AffinePoint E)
    (allowed : control = true → P ≠ Q ∧ P ≠ AffinePoint.negate Q) :
    (nextPoint E Q control P).toGroupPoint =
      if control = true then P.toGroupPoint * Q.toGroupPoint else P.toGroupPoint := by
  cases control with
  | false => rw [nextPoint_false, if_neg Bool.false_ne_true]
  | true =>
      rw [nextPoint_true E Q P (allowed rfl).1 (allowed rfl).2, if_pos rfl]
      exact PointSemantics.genericAddPoint_toGroupPoint E P Q _

/-- Follow the prescribed list in order, using the same total selected affine update. -/
def path {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool) :
    List (Fin count) → AffinePoint E → AffinePoint E
  | [], initial => initial
  | active :: remaining, initial =>
      path E points controls remaining (nextPoint E (points active) (controls active) initial)

/-- Check the original active exclusions at each point reached by that same ordered path. -/
def admissible {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool) :
    List (Fin count) → AffinePoint E → Prop
  | [], _ => True
  | active :: remaining, initial =>
      (controls active = true →
        initial ≠ points active ∧ initial ≠ AffinePoint.negate (points active)) ∧
      admissible E points controls remaining
        (nextPoint E (points active) (controls active) initial)

/-- An admissible affine path follows precisely the selected group multiplications in order. -/
theorem path_toGroupPoint {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (order : List (Fin count)) (initial : AffinePoint E)
    (allowed : admissible E points controls order initial) :
    (path E points controls order initial).toGroupPoint =
      order.foldl (fun point active =>
        if controls active = true then point * (points active).toGroupPoint else point)
        initial.toGroupPoint := by
  induction order generalizing initial with
  | nil => rfl
  | cons active remaining ih =>
      rw [path, ih _ allowed.2, List.foldl_cons,
        nextPoint_toGroupPoint E (points active) (controls active) initial allowed.1]

end

end AffineTrajectory
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
