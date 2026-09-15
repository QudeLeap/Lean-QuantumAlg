/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Dist

/-!
# Finite-dimensional integer-lattice geometry

This module contains only quantum-free geometry on integer coordinate vectors.
Algorithm-specific lattice bases and probability events belong in their
number-theoretic clients.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- An integer coordinate vector of fixed finite dimension. -/
abbrev IntegerVector (dimension : Nat) : Type := Fin dimension → Int

/-- A concrete integer point in dimension three. -/
abbrev IntegerPoint3 : Type := Int × Int × Int

/-- View a concrete triple as a three-dimensional coordinate vector. -/
def IntegerPoint3.toVector (point : IntegerPoint3) : IntegerVector 3
  | ⟨0, _⟩ => point.1
  | ⟨1, _⟩ => point.2.1
  | ⟨2, _⟩ => point.2.2

/-- Squared Euclidean norm, represented in `Nat` to avoid square roots. -/
def squaredNorm {dimension : Nat} (vector : IntegerVector dimension) : Nat :=
  ∑ index, (vector index).natAbs ^ 2

/-- Squared Euclidean distance between two integer vectors. -/
def squaredDistance {dimension : Nat}
    (left right : IntegerVector dimension) : Nat :=
  squaredNorm fun index => left index - right index

/-- Membership in an open Euclidean ball, expressed without square roots. -/
def IsInsideSquaredBall {dimension : Nat}
    (center : IntegerVector dimension) (radiusSquared : Nat)
    (point : IntegerVector dimension) : Prop :=
  squaredDistance point center < radiusSquared

/-- Two natural numbers in the same Euclidean-division block differ by less
than the positive block width. -/
theorem natDist_lt_of_div_eq {left right width : Nat}
    (hwidth : 0 < width) (hquotient : left / width = right / width) :
    Nat.dist left right < width := by
  have hleft : left = left % width + width * (left / width) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div left width).symm
  have hright : right = right % width + width * (right / width) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div right width).symm
  rw [hleft, hright, hquotient, Nat.dist_add_add_right]
  have hleftMod := Nat.mod_lt left hwidth
  have hrightMod := Nat.mod_lt right hwidth
  unfold Nat.dist
  omega

/-- On nonnegative integers, integer absolute difference agrees with natural
distance after `Int.toNat`. -/
theorem natAbs_sub_eq_natDist_toNat {left right : Int}
    (hleft : 0 ≤ left) (hright : 0 ≤ right) :
    (left - right).natAbs = Nat.dist left.toNat right.toNat := by
  by_cases hle : left ≤ right
  · have hleNat : left.toNat ≤ right.toNat := by
      rw [← Int.ofNat_le]
      simpa [Int.toNat_of_nonneg hleft, Int.toNat_of_nonneg hright]
        using hle
    rw [Nat.dist_eq_sub_of_le hleNat]
    rw [← Int.ofNat_inj]
    rw [Int.ofNat_natAbs_of_nonpos (sub_nonpos.mpr hle), Int.ofNat_sub hleNat]
    simp [Int.toNat_of_nonneg hleft, Int.toNat_of_nonneg hright]
  · have hle' : right ≤ left := le_of_lt (lt_of_not_ge hle)
    have hleNat : right.toNat ≤ left.toNat := by
      rw [← Int.ofNat_le]
      simpa [Int.toNat_of_nonneg hleft, Int.toNat_of_nonneg hright]
        using hle'
    rw [Nat.dist_eq_sub_of_le_right hleNat]
    rw [← Int.ofNat_inj]
    rw [Int.natAbs_of_nonneg (sub_nonneg.mpr hle'), Int.ofNat_sub hleNat]
    simp [Int.toNat_of_nonneg hleft, Int.toNat_of_nonneg hright]

/-- The closed axis-aligned integer cube about a three-dimensional center.
It is a finite carrier from which exact open-ball neighborhoods can be
filtered without searching over an unrelated semantic witness. -/
def integerCube3 (center : IntegerPoint3) (radius : Nat) :
    Finset IntegerPoint3 :=
  (Finset.Icc (center.1 - radius) (center.1 + radius)).product <|
    (Finset.Icc (center.2.1 - radius) (center.2.1 + radius)).product <|
      Finset.Icc (center.2.2 - radius) (center.2.2 + radius)

@[simp]
theorem mem_integerCube3 {center point : IntegerPoint3} {radius : Nat} :
    point ∈ integerCube3 center radius ↔
      center.1 - radius ≤ point.1 ∧ point.1 ≤ center.1 + radius ∧
      center.2.1 - radius ≤ point.2.1 ∧
        point.2.1 ≤ center.2.1 + radius ∧
      center.2.2 - radius ≤ point.2.2 ∧
        point.2.2 ≤ center.2.2 + radius := by
  simp [integerCube3, and_assoc]

@[simp]
theorem squaredDistance_self {dimension : Nat}
    (vector : IntegerVector dimension) :
    squaredDistance vector vector = 0 := by
  simp [squaredDistance, squaredNorm]

@[simp]
theorem squaredDistance_point3 (left right : IntegerPoint3) :
    squaredDistance left.toVector right.toVector =
      (left.1 - right.1).natAbs ^ 2 +
        (left.2.1 - right.2.1).natAbs ^ 2 +
          (left.2.2 - right.2.2).natAbs ^ 2 := by
  simp [squaredDistance, squaredNorm, Fin.sum_univ_succ,
    IntegerPoint3.toVector, add_assoc]

end NumberTheory
end QuantumAlg

end
