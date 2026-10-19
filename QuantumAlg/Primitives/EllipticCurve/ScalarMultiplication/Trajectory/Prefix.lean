/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Trajectory.Point
import all QuantumAlg.Util.ExceptionalOffsetAveraging

/-!
# Group-prefix conditions for the original affine trajectory

The original exceptional-offset predicate implies every active affine
exclusion along the same increasing-index path. Its stricter three-exclusion
variant supplies the same conclusion without changing its selected good set.
All statements concern independent point and group mathematics.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace AffineTrajectory

noncomputable section

open GenericPointAddition.InPlace

private lemma path_append {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (first second : List (Fin count)) (initial : AffinePoint E) :
    path E points controls (first ++ second) initial =
      path E points controls second (path E points controls first initial) := by
  induction first generalizing initial with
  | nil => rfl
  | cons active remaining ih =>
      simpa only [List.cons_append, path] using
        ih (nextPoint E (points active) (controls active) initial)

private lemma admissible_append {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (first second : List (Fin count)) (initial : AffinePoint E) :
    admissible E points controls (first ++ second) initial ↔
      admissible E points controls first initial ∧
        admissible E points controls second (path E points controls first initial) := by
  induction first generalizing initial with
  | nil => simp only [List.nil_append, admissible, path, true_and]
  | cons active remaining ih =>
      simp only [List.cons_append, admissible, path, ih, and_assoc]

private lemma finRange_take_succ {count : Nat} (index : Fin count) :
    (List.finRange count).take (index.val + 1) =
      (List.finRange count).take index.val ++ [index] := by
  have within : index.val < (List.finRange count).length := by
    simpa only [List.length_finRange] using index.isLt
  have value : (List.finRange count)[index.val]'within = index := by
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  simpa only [value] using
    (List.take_concat_get' (List.finRange count) index.val within).symm

/-- The independent affine point reached after the first prescribed physical-index positions. -/
def pointPrefix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (initial : AffinePoint E) (processed : Nat) : AffinePoint E :=
  path E points controls ((List.finRange count).take processed) initial

private lemma pointPrefix_succ {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (initial : AffinePoint E) (index : Fin count) :
    pointPrefix E points controls initial (index.val + 1) =
      nextPoint E (points index) (controls index)
        (pointPrefix E points controls initial index.val) := by
  rw [pointPrefix, finRange_take_succ, path_append]
  rfl

private lemma prefix_admissible_and_group {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (controls : Fin count → Bool) (initial : AffinePoint E)
    (good : ExceptionalOffsetAveraging.Admissible count
      (fun (_ : Unit) index => controls index) (fun index => (points index).toGroupPoint)
      initial.toGroupPoint ()) :
    ∀ processed : Nat, processed ≤ count →
      admissible E points controls ((List.finRange count).take processed) initial ∧
        (pointPrefix E points controls initial processed).toGroupPoint =
          initial.toGroupPoint * ExceptionalOffsetAveraging.prefixMultiplier count
            (fun (_ : Unit) index => controls index)
            (fun index => (points index).toGroupPoint) () processed := by
  intro processed within
  induction processed with
  | zero =>
      simp only [List.take_zero, admissible, pointPrefix, path,
        ExceptionalOffsetAveraging.prefixMultiplier, List.foldl_nil, mul_one, and_self]
  | succ processed ih =>
      have before := ih (Nat.le_of_succ_le within)
      let index : Fin count := ⟨processed, Nat.lt_of_succ_le within⟩
      have allowed : controls index = true →
          pointPrefix E points controls initial processed ≠ points index ∧
          pointPrefix E points controls initial processed ≠ AffinePoint.negate (points index) := by
        intro active
        have original := good index active
        constructor
        · intro same
          apply original.1
          rw [← before.2, same]
        · intro inverse
          apply original.2
          rw [← before.2, inverse, PointSemantics.negate_toGroupPoint]
      constructor
      · rw [finRange_take_succ index, admissible_append]
        refine ⟨before.1, ?_⟩
        exact ⟨allowed, trivial⟩
      · rw [pointPrefix_succ E points controls initial index,
          nextPoint_toGroupPoint E (points index) (controls index) _ allowed,
          ExceptionalOffsetAveraging.prefixMultiplier_succ count
            (fun (_ : Unit) position => controls position)
            (fun position => (points position).toGroupPoint) () processed index.isLt]
        rw [before.2]
        split_ifs <;> simp only [mul_assoc, index]

/-- Each admissible affine prefix denotes the original offset times the selected group prefix. -/
lemma pointPrefix_toGroupPoint {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (controls : Fin count → Bool)
    (initial : AffinePoint E)
    (good : ExceptionalOffsetAveraging.Admissible count
      (fun (_ : Unit) index => controls index) (fun index => (points index).toGroupPoint)
      initial.toGroupPoint ()) (processed : Nat) (within : processed ≤ count) :
    (pointPrefix E points controls initial processed).toGroupPoint =
      initial.toGroupPoint * ExceptionalOffsetAveraging.prefixMultiplier count
        (fun (_ : Unit) index => controls index)
        (fun index => (points index).toGroupPoint) () processed :=
  (prefix_admissible_and_group E points controls initial good processed within).2

/-- The original group-offset domain supplies every active affine exclusion in execution order. -/
lemma admissible_finRange_of_group {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (controls : Fin count → Bool) (initial : AffinePoint E)
    (good : ExceptionalOffsetAveraging.Admissible count
      (fun (_ : Unit) index => controls index) (fun index => (points index).toGroupPoint)
      initial.toGroupPoint ()) :
    admissible E points controls (List.finRange count) initial := by
  have actual := (prefix_admissible_and_group E points controls initial good count le_rfl).1
  simpa only [List.take_of_length_le (Nat.le_of_eq List.length_finRange)] using actual

/-- The original stricter good set implies the same affine trajectory without changing that set. -/
lemma admissible_finRange_of_strict {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (controls : Fin count → Bool) (initial : AffinePoint E)
    (strict : ExceptionalOffsetAveraging.RNSLAdmissible count
      (fun (_ : Unit) index => controls index) (fun index => (points index).toGroupPoint)
      initial.toGroupPoint ()) :
    admissible E points controls (List.finRange count) initial := by
  apply admissible_finRange_of_group E points controls initial
  intro index _
  exact ⟨(strict index).1, (strict index).2.1⟩

end

end AffineTrajectory
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
