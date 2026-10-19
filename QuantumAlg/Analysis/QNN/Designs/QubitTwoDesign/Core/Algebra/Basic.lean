/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

meta import Mathlib.Algebra.QuadraticAlgebra.Defs
meta import Mathlib.Algebra.Quaternion
import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Interface.DoubledTwirl
import all QuantumAlg.Analysis.QNN.Algebras.SimpleDLA
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.Real.Irrational

/-!
# The single-qubit Clifford commutant-complete twirl

This file realizes the single-qubit Clifford group by its strict `48`-element binary-octahedral
lift in `SU(2)`.  Its central order-two subgroup accounts for the `24` projective Clifford gates.

Webb proves that the Clifford group is a unitary `3`-design, hence in particular a `2`-design
[Web15, `Cliffords_are_a_3-design.tex:616-619`, Theorem `thm:cliffords_are_3_design`]. The
formalized input used here is the doubled-commutant-completeness consequence needed by the
Ragone second-moment interface, together with concrete finite twirl computations. Ragone et al.
identify the second moment on `g ⊗ g` as the orthogonal projection onto the invariant carrier and,
for simple `g`, onto the split quadratic Casimir
[RBS+23, `Arxiv_Final.tex:1253-1285`, Eq. `eqn:t moment operator5`, Lemma `lem:casimir`, and
Eq. `eqn:second moment operator is 1d orth proj`].
-/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

/-- The exact coefficient ring `ℚ(√2)`, represented without floating-point arithmetic. -/
abbrev SqrtTwoRat := QuadraticAlgebra ℚ 2 0

/-- Exact Hamilton quaternions over `ℚ(√2)`. -/
abbrev ExactQuaternion := Quaternion SqrtTwoRat

private lemma exactQuaternion_re_add (p q : ExactQuaternion) :
    (p + q).re = p.re + q.re :=
  Quaternion.re_add p q

private lemma exactQuaternion_imI_add (p q : ExactQuaternion) :
    (p + q).imI = p.imI + q.imI :=
  Quaternion.imI_add p q

private lemma exactQuaternion_imJ_add (p q : ExactQuaternion) :
    (p + q).imJ = p.imJ + q.imJ :=
  Quaternion.imJ_add p q

private lemma exactQuaternion_imK_add (p q : ExactQuaternion) :
    (p + q).imK = p.imK + q.imK :=
  Quaternion.imK_add p q

private lemma exactQuaternion_re_mul (p q : ExactQuaternion) :
    (p * q).re = p.re * q.re - p.imI * q.imI - p.imJ * q.imJ - p.imK * q.imK :=
  Quaternion.re_mul p q

private lemma exactQuaternion_imI_mul (p q : ExactQuaternion) :
    (p * q).imI = p.re * q.imI + p.imI * q.re + p.imJ * q.imK - p.imK * q.imJ :=
  Quaternion.imI_mul p q

private lemma exactQuaternion_imJ_mul (p q : ExactQuaternion) :
    (p * q).imJ = p.re * q.imJ - p.imI * q.imK + p.imJ * q.re + p.imK * q.imI :=
  Quaternion.imJ_mul p q

private lemma exactQuaternion_imK_mul (p q : ExactQuaternion) :
    (p * q).imK = p.re * q.imK + p.imI * q.imJ - p.imJ * q.imI + p.imK * q.re :=
  Quaternion.imK_mul p q

instance : DecidableEq ExactQuaternion := fun a b =>
  decidable_of_iff
    (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK) <| by
      constructor
      · rintro ⟨hre, hi, hj, hk⟩
        exact QuaternionAlgebra.ext hre hi hj hk
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- Codes for the `8 + 16 + 24` unit quaternions in the binary octahedral group. -/
public inductive BinaryOctahedral where
  | axis (negative : Bool) (coordinate : Fin 4)
  | half (negative : Fin 4 → Bool)
  | edge (pair : Fin 6) (negativeLeft negativeRight : Bool)
  deriving DecidableEq, Fintype

/-- The four coordinate quaternion units `1, i, j, k`. -/
def quaternionBasis : Fin 4 → ExactQuaternion :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The six unordered pairs of quaternion coordinates. -/
def coordinatePair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Applies the sign encoded by `negative` to an exact coefficient. -/
def signed (negative : Bool) (x : SqrtTwoRat) : SqrtTwoRat :=
  if negative then -x else x

/-- The signed exact coefficient `±1/2` used by half-coordinate codes. -/
def halfCoefficient (negative : Bool) : SqrtTwoRat :=
  signed negative ⟨1 / 2, 0⟩

/-- The signed exact coefficient `±√2/2` used by edge-coordinate codes. -/
def sqrtTwoHalf (negative : Bool) : SqrtTwoRat :=
  signed negative ⟨0, 1 / 2⟩

/-- The exact unit quaternion represented by a binary-octahedral code. -/
def binaryOctahedralQuaternion : BinaryOctahedral → ExactQuaternion
  | .axis negative coordinate => signed negative 1 • quaternionBasis coordinate
  | .half negative =>
      ⟨halfCoefficient (negative 0), halfCoefficient (negative 1),
        halfCoefficient (negative 2), halfCoefficient (negative 3)⟩
  | .edge pair negativeLeft negativeRight =>
      sqrtTwoHalf negativeLeft • quaternionBasis (coordinatePair pair).1 +
        sqrtTwoHalf negativeRight • quaternionBasis (coordinatePair pair).2

/-! ## Kernel-checkable integer numerators

`decide` cannot reduce `ℚ` arithmetic in the kernel (rational normalization is not
kernel-computable), so the finite-group facts are transported from the integer numerators `2 · q`,
which live over `ℤ[√2]` where `decide` reduces (`Int` is kernel-accelerated). -/

/-- The integer coefficient ring `ℤ[√2]` (`(√2)² = 2`). -/
abbrev IntSqrtTwo := QuadraticAlgebra ℤ 2 0

instance : DecidableEq (Quaternion IntSqrtTwo) := fun a b =>
  decidable_of_iff
    (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK) <| by
      constructor
      · rintro ⟨hre, hi, hj, hk⟩
        exact QuaternionAlgebra.ext hre hi hj hk
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- The coefficient inclusion `ℤ[√2] → ℚ[√2]`. -/
def intSqrtTwoToRat : IntSqrtTwo →+* SqrtTwoRat where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Int.cast_one, Int.cast_zero]
  map_mul' x y := by
    apply QuadraticAlgebra.ext <;>
      · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
        push_cast
        ring
  map_zero' := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, Int.cast_zero]
  map_add' x y := by
    apply QuadraticAlgebra.ext <;>
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
        push_cast
        ring

@[simp] lemma intSqrtTwoToRat_re (z : IntSqrtTwo) : (intSqrtTwoToRat z).re = (z.re : ℚ) := rfl
@[simp] lemma intSqrtTwoToRat_im (z : IntSqrtTwo) : (intSqrtTwoToRat z).im = (z.im : ℚ) := rfl

@[simp] lemma intSqrtTwoToRat_ofNat (n : ℕ) [n.AtLeastTwo] :
    intSqrtTwoToRat (ofNat(n)) = ofNat(n) := map_ofNat intSqrtTwoToRat n
@[simp] lemma intSqrtTwoToRat_one : intSqrtTwoToRat 1 = 1 := map_one intSqrtTwoToRat

lemma intSqrtTwoToRat_injective : Function.Injective intSqrtTwoToRat := by
  intro x y hxy
  have hre := congrArg QuadraticAlgebra.re hxy
  have him := congrArg QuadraticAlgebra.im hxy
  simp only [intSqrtTwoToRat_re, intSqrtTwoToRat_im] at hre him
  exact QuadraticAlgebra.ext (by exact_mod_cast hre) (by exact_mod_cast him)

/-- Coordinate quaternion units over `ℤ[√2]`. -/
def quaternionBasisZ : Fin 4 → Quaternion IntSqrtTwo :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The integer numerator `2 · q` of each binary-octahedral quaternion. Its coefficients lie in
`ℤ[√2]`, so the finite-group facts below reduce under kernel `decide`. -/
def octNumerator : BinaryOctahedral → Quaternion IntSqrtTwo
  | .axis negative coordinate =>
      (if negative then (-2 : IntSqrtTwo) else 2) • quaternionBasisZ coordinate
  | .half negative =>
      ⟨if negative 0 then -1 else 1, if negative 1 then -1 else 1,
        if negative 2 then -1 else 1, if negative 3 then -1 else 1⟩
  | .edge pair negativeLeft negativeRight =>
      (if negativeLeft then -(⟨0, 1⟩ : IntSqrtTwo) else ⟨0, 1⟩) •
          quaternionBasisZ (coordinatePair pair).1 +
        (if negativeRight then -(⟨0, 1⟩ : IntSqrtTwo) else ⟨0, 1⟩) •
          quaternionBasisZ (coordinatePair pair).2

/-- The coefficientwise realization of an integer-numerator quaternion in `ℚ[√2]`. -/
def octToExact : Quaternion IntSqrtTwo →+* ExactQuaternion := by
  let toExact : Quaternion IntSqrtTwo → ExactQuaternion := fun q =>
    ⟨intSqrtTwoToRat q.re, intSqrtTwoToRat q.imI, intSqrtTwoToRat q.imJ,
      intSqrtTwoToRat q.imK⟩
  exact
    { toFun := toExact
      map_one' := by apply QuaternionAlgebra.ext <;> simp [toExact]
      map_mul' := by
        intro p q
        apply QuaternionAlgebra.ext
        · rw [exactQuaternion_re_mul]
          simp only [toExact, Quaternion.re_mul, map_sub, map_mul]
        · rw [exactQuaternion_imI_mul]
          simp only [toExact, Quaternion.imI_mul, map_add, map_sub, map_mul]
        · rw [exactQuaternion_imJ_mul]
          simp only [toExact, Quaternion.imJ_mul, map_add, map_sub, map_mul]
        · rw [exactQuaternion_imK_mul]
          simp only [toExact, Quaternion.imK_mul, map_add, map_sub, map_mul]
      map_zero' := by apply QuaternionAlgebra.ext <;> simp [toExact]
      map_add' := by
        intro p q
        apply QuaternionAlgebra.ext
        · rw [exactQuaternion_re_add]
          simp only [toExact, Quaternion.re_add, map_add]
        · rw [exactQuaternion_imI_add]
          simp only [toExact, Quaternion.imI_add, map_add]
        · rw [exactQuaternion_imJ_add]
          simp only [toExact, Quaternion.imJ_add, map_add]
        · rw [exactQuaternion_imK_add]
          simp only [toExact, Quaternion.imK_add, map_add] }

@[simp] lemma octToExact_re (q : Quaternion IntSqrtTwo) :
    (octToExact q).re = intSqrtTwoToRat q.re := rfl
@[simp] lemma octToExact_imI (q : Quaternion IntSqrtTwo) :
    (octToExact q).imI = intSqrtTwoToRat q.imI := rfl
@[simp] lemma octToExact_imJ (q : Quaternion IntSqrtTwo) :
    (octToExact q).imJ = intSqrtTwoToRat q.imJ := rfl
@[simp] lemma octToExact_imK (q : Quaternion IntSqrtTwo) :
    (octToExact q).imK = intSqrtTwoToRat q.imK := rfl

lemma octToExact_injective : Function.Injective octToExact := by
  intro p q h
  apply QuaternionAlgebra.ext <;> apply intSqrtTwoToRat_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

lemma octToExact_star (q : Quaternion IntSqrtTwo) :
    octToExact (star q) = star (octToExact q) := by
  apply QuaternionAlgebra.ext <;> simp

/-- The squared norm transports coefficientwise through `octToExact`. -/
lemma normSq_octToExact (q : Quaternion IntSqrtTwo) :
    Quaternion.normSq (octToExact q) = intSqrtTwoToRat (Quaternion.normSq q) := by
  simp only [Quaternion.normSq_def', octToExact_re, octToExact_imI, octToExact_imJ, octToExact_imK,
    map_add, map_pow]

/-- Evaluation of the exact coefficient `√2` in the real numbers. -/
noncomputable def sqrtTwoEval : SqrtTwoRat →+* ℝ :=
  ((QuadraticAlgebra.lift (R := ℚ) (A := ℝ)
    ⟨Real.sqrt 2, by norm_num [Real.sq_sqrt]⟩).toRingHom)

lemma sqrtTwoEval_apply (x : SqrtTwoRat) :
    sqrtTwoEval x = (x.re : ℝ) + (x.im : ℝ) * Real.sqrt 2 := by
  simp [sqrtTwoEval, QuadraticAlgebra.lift, Rat.smul_def]

/-- Evaluation at the irrational real root is faithful. -/
lemma sqrtTwoEval_injective : Function.Injective sqrtTwoEval := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [sqrtTwoEval_apply] at hx
  by_cases him : x.im = 0
  · apply QuadraticAlgebra.ext
    · simpa [him] using hx
    · exact him
  · exfalso
    apply irrational_sqrt_two
    refine ⟨-x.re / x.im, ?_⟩
    have himR : (x.im : ℝ) ≠ 0 := by exact_mod_cast him
    rw [Rat.cast_div, Rat.cast_neg]
    field_simp
    nlinarith

/-- Coefficientwise evaluation of an exact quaternion in the real Hamilton quaternions. -/
noncomputable def realQuaternion (q : ExactQuaternion) : Quaternion ℝ :=
  ⟨sqrtTwoEval q.re, sqrtTwoEval q.imI, sqrtTwoEval q.imJ, sqrtTwoEval q.imK⟩

lemma realQuaternion_injective : Function.Injective realQuaternion := by
  intro p q h
  apply QuaternionAlgebra.ext <;> apply sqrtTwoEval_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

/-- Additivity of the real realization (`realQuaternion` is coefficientwise `sqrtTwoEval`). -/
lemma realQuaternion_add (p q : ExactQuaternion) :
    realQuaternion (p + q) = realQuaternion p + realQuaternion q := by
  apply QuaternionAlgebra.ext
  · rw [Quaternion.re_add (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, map_add]
  · rw [Quaternion.imI_add (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, map_add]
  · rw [Quaternion.imJ_add (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, map_add]
  · rw [Quaternion.imK_add (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, map_add]

/-- Doubling is injective on `ℚ[√2]`: `√2`-evaluation is a faithful embedding into the
characteristic-zero field `ℝ`, where doubling is injective. -/
private lemma sqrtTwoRat_add_self_injective {a b : SqrtTwoRat} (h : a + a = b + b) : a = b := by
  apply sqrtTwoEval_injective
  have h' := congrArg sqrtTwoEval h
  rw [map_add, map_add] at h'
  linarith

/-- Cancellation of the doubling map on the exact quaternions, componentwise over `ℚ[√2]`. -/
private lemma exact_add_self_injective {x y : ExactQuaternion} (h : x + x = y + y) : x = y := by
  apply QuaternionAlgebra.ext <;> apply sqrtTwoRat_add_self_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

/-- Coefficientwise realization commutes with scalar multiplication after mapping the scalar. -/
private lemma octToExact_smul (s : IntSqrtTwo) (q : Quaternion IntSqrtTwo) :
    octToExact (s • q) = intSqrtTwoToRat s • octToExact q := by
  apply QuaternionAlgebra.ext
  · simp only [octToExact_re, Quaternion.re_smul, smul_eq_mul, map_mul]
  · simp only [octToExact_imI, Quaternion.imI_smul, smul_eq_mul, map_mul]
  · simp only [octToExact_imJ, Quaternion.imJ_smul, smul_eq_mul, map_mul]
  · simp only [octToExact_imK, Quaternion.imK_smul, smul_eq_mul, map_mul]

private lemma octToExact_quaternionBasisZ (coordinate : Fin 4) :
    octToExact (quaternionBasisZ coordinate) = quaternionBasis coordinate := by
  fin_cases coordinate <;> rfl

private lemma intSignToRat_eq_doubleHalf (negative : Bool) :
    intSqrtTwoToRat (if negative then -1 else 1) =
      halfCoefficient negative + halfCoefficient negative := by
  cases negative <;>
    (apply QuadraticAlgebra.ext <;>
      norm_num [intSqrtTwoToRat, halfCoefficient, signed])

private lemma intSqrtTwoSignToRat_eq_doubleHalf (negative : Bool) :
    intSqrtTwoToRat
        (if negative then -(⟨0, 1⟩ : IntSqrtTwo) else ⟨0, 1⟩) =
      sqrtTwoHalf negative + sqrtTwoHalf negative := by
  cases negative <;>
    (apply QuadraticAlgebra.ext <;>
      norm_num [intSqrtTwoToRat, sqrtTwoHalf, signed])

/-- The exact realization scaled by two equals the integer numerator's realization. -/
lemma octToExact_octNumerator (a : BinaryOctahedral) :
    octToExact (octNumerator a) =
      binaryOctahedralQuaternion a + binaryOctahedralQuaternion a := by
  cases a with
  | axis negative coordinate =>
      simp only [octNumerator, binaryOctahedralQuaternion, octToExact_smul,
        octToExact_quaternionBasisZ]
      cases negative <;> simp [signed] <;> module
  | half negative =>
      apply QuaternionAlgebra.ext
      · rw [octToExact_re, exactQuaternion_re_add]
        simpa [octNumerator, binaryOctahedralQuaternion] using
          intSignToRat_eq_doubleHalf (negative 0)
      · rw [octToExact_imI, exactQuaternion_imI_add]
        simpa [octNumerator, binaryOctahedralQuaternion] using
          intSignToRat_eq_doubleHalf (negative 1)
      · rw [octToExact_imJ, exactQuaternion_imJ_add]
        simpa [octNumerator, binaryOctahedralQuaternion] using
          intSignToRat_eq_doubleHalf (negative 2)
      · rw [octToExact_imK, exactQuaternion_imK_add]
        simpa [octNumerator, binaryOctahedralQuaternion] using
          intSignToRat_eq_doubleHalf (negative 3)
  | edge pair negativeLeft negativeRight =>
      simp only [octNumerator, map_add, octToExact_smul, octToExact_quaternionBasisZ,
        binaryOctahedralQuaternion]
      rw [intSqrtTwoSignToRat_eq_doubleHalf, intSqrtTwoSignToRat_eq_doubleHalf]
      module

end QuantumAlg.QubitTwoDesign

end
