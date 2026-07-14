/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public meta import Mathlib.Algebra.QuadraticAlgebra.Defs
public meta import Mathlib.Algebra.Quaternion
public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.DoubledTwirl
public import QuantumAlg.Primitives.QNN.Algebras.SimpleDLA
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.Real.Irrational

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

@[expose] public section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

/-- The exact coefficient ring `ℚ(√2)`, represented without floating-point arithmetic. -/
abbrev SqrtTwoRat := QuadraticAlgebra ℚ 2 0

/-- Exact Hamilton quaternions over `ℚ(√2)`. -/
abbrev ExactQuaternion := Quaternion SqrtTwoRat

instance : DecidableEq ExactQuaternion := fun a b =>
  decidable_of_iff
    (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK) <| by
      constructor
      · rintro ⟨hre, hi, hj, hk⟩
        exact QuaternionAlgebra.ext hre hi hj hk
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- Codes for the `8 + 16 + 24` unit quaternions in the binary octahedral group. -/
inductive BinaryOctahedral where
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

@[simp] theorem intSqrtTwoToRat_re (z : IntSqrtTwo) : (intSqrtTwoToRat z).re = (z.re : ℚ) := rfl
@[simp] theorem intSqrtTwoToRat_im (z : IntSqrtTwo) : (intSqrtTwoToRat z).im = (z.im : ℚ) := rfl

@[simp] theorem intSqrtTwoToRat_ofNat (n : ℕ) [n.AtLeastTwo] :
    intSqrtTwoToRat (ofNat(n)) = ofNat(n) := map_ofNat intSqrtTwoToRat n
@[simp] theorem intSqrtTwoToRat_one : intSqrtTwoToRat 1 = 1 := map_one intSqrtTwoToRat

theorem intSqrtTwoToRat_injective : Function.Injective intSqrtTwoToRat := by
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
def octToExact : Quaternion IntSqrtTwo →+* ExactQuaternion where
  toFun q := ⟨intSqrtTwoToRat q.re, intSqrtTwoToRat q.imI, intSqrtTwoToRat q.imJ,
    intSqrtTwoToRat q.imK⟩
  map_one' := by apply QuaternionAlgebra.ext <;> simp
  map_mul' p q := by
    apply QuaternionAlgebra.ext <;>
      simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
        map_add, map_sub, map_mul]
  map_zero' := by apply QuaternionAlgebra.ext <;> simp
  map_add' p q := by
    apply QuaternionAlgebra.ext <;>
      simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
        map_add]

@[simp] theorem octToExact_re (q : Quaternion IntSqrtTwo) :
    (octToExact q).re = intSqrtTwoToRat q.re := rfl
@[simp] theorem octToExact_imI (q : Quaternion IntSqrtTwo) :
    (octToExact q).imI = intSqrtTwoToRat q.imI := rfl
@[simp] theorem octToExact_imJ (q : Quaternion IntSqrtTwo) :
    (octToExact q).imJ = intSqrtTwoToRat q.imJ := rfl
@[simp] theorem octToExact_imK (q : Quaternion IntSqrtTwo) :
    (octToExact q).imK = intSqrtTwoToRat q.imK := rfl

theorem octToExact_injective : Function.Injective octToExact := by
  intro p q h
  apply QuaternionAlgebra.ext <;> apply intSqrtTwoToRat_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

theorem octToExact_star (q : Quaternion IntSqrtTwo) :
    octToExact (star q) = star (octToExact q) := by
  apply QuaternionAlgebra.ext <;> simp

/-- The squared norm transports coefficientwise through `octToExact`. -/
theorem normSq_octToExact (q : Quaternion IntSqrtTwo) :
    Quaternion.normSq (octToExact q) = intSqrtTwoToRat (Quaternion.normSq q) := by
  simp only [Quaternion.normSq_def', octToExact_re, octToExact_imI, octToExact_imJ, octToExact_imK,
    map_add, map_pow]

/-- Evaluation of the exact coefficient `√2` in the real numbers. -/
noncomputable def sqrtTwoEval : SqrtTwoRat →+* ℝ :=
  ((QuadraticAlgebra.lift (R := ℚ) (A := ℝ)
    ⟨Real.sqrt 2, by norm_num [Real.sq_sqrt]⟩).toRingHom)

theorem sqrtTwoEval_apply (x : SqrtTwoRat) :
    sqrtTwoEval x = (x.re : ℝ) + (x.im : ℝ) * Real.sqrt 2 := by
  simp [sqrtTwoEval, QuadraticAlgebra.lift, Rat.smul_def]

/-- Evaluation at the irrational real root is faithful. -/
theorem sqrtTwoEval_injective : Function.Injective sqrtTwoEval := by
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

theorem realQuaternion_injective : Function.Injective realQuaternion := by
  intro p q h
  apply QuaternionAlgebra.ext <;> apply sqrtTwoEval_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

/-- Additivity of the real realization (`realQuaternion` is coefficientwise `sqrtTwoEval`). -/
theorem realQuaternion_add (p q : ExactQuaternion) :
    realQuaternion (p + q) = realQuaternion p + realQuaternion q := by
  apply QuaternionAlgebra.ext <;> simp [realQuaternion, map_add]

/-- Doubling is injective on `ℚ[√2]`: `√2`-evaluation is a faithful embedding into the
characteristic-zero field `ℝ`, where doubling is injective. -/
private theorem sqrtTwoRat_add_self_injective {a b : SqrtTwoRat} (h : a + a = b + b) : a = b := by
  apply sqrtTwoEval_injective
  have h' := congrArg sqrtTwoEval h
  rw [map_add, map_add] at h'
  linarith

/-- Cancellation of the doubling map on the exact quaternions, componentwise over `ℚ[√2]`. -/
private theorem exact_add_self_injective {x y : ExactQuaternion} (h : x + x = y + y) : x = y := by
  apply QuaternionAlgebra.ext <;> apply sqrtTwoRat_add_self_injective
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

set_option maxHeartbeats 2000000 in
-- Expanding every binary-octahedral code family needs this local reduction budget.
/-- The exact realization scaled by two equals the integer numerator's realization. -/
theorem octToExact_octNumerator (a : BinaryOctahedral) :
    octToExact (octNumerator a) =
      binaryOctahedralQuaternion a + binaryOctahedralQuaternion a := by
  cases a with
  | axis negative coordinate =>
      fin_cases coordinate <;> cases negative <;>
        (apply QuaternionAlgebra.ext <;>
          simp only [octNumerator, binaryOctahedralQuaternion, signed, quaternionBasis,
            quaternionBasisZ, octToExact_re, octToExact_imI, octToExact_imJ, octToExact_imK,
            Quaternion.re_add,
            Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
            Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
            if_true, smul_eq_mul] <;> norm_num)
  | half negative =>
      apply QuaternionAlgebra.ext <;>
        · simp only [octNumerator, binaryOctahedralQuaternion, octToExact_re, octToExact_imI,
            octToExact_imJ, octToExact_imK, Quaternion.re_add, Quaternion.imI_add,
            Quaternion.imJ_add, Quaternion.imK_add]
          cases negative 0 <;> cases negative 1 <;> cases negative 2 <;> cases negative 3 <;>
            (apply QuadraticAlgebra.ext <;> simp [halfCoefficient, signed]; norm_num)
  | edge pair negativeLeft negativeRight =>
      fin_cases pair <;> cases negativeLeft <;> cases negativeRight <;>
        (apply QuaternionAlgebra.ext <;>
          simp only [octNumerator, binaryOctahedralQuaternion, sqrtTwoHalf, signed, coordinatePair,
            quaternionBasis, quaternionBasisZ, octToExact_re, octToExact_imI, octToExact_imJ,
            octToExact_imK, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
            Quaternion.imK_add, Quaternion.re_smul,
            Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, if_true,
            smul_eq_mul] <;>
          (apply QuadraticAlgebra.ext <;> simp <;> norm_num))

-- M-13 canary, measured 2026-07-09 with
-- `/usr/bin/time -p lake build QuantumAlg.Primitives.QNN.Designs.QubitTwoDesign`:
-- Lake reported `Built ... (186s)`; `/usr/bin/time` reported `real 188.89`.
-- A subsequent full `lake build` on the same file reported `QubitTwoDesign (274s)`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel comparison of all `48` numerator codes needs this local budget.
/-- The `48` integer numerators are pairwise distinct. -/
theorem octNumerator_injective : Function.Injective octNumerator := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive norm reduction over the `48` numerator codes needs this local budget.
/-- Every integer numerator has squared norm `4` (the unit quaternion scaled by `2`). -/
theorem octNumerator_normSq : ∀ a, Quaternion.normSq (octNumerator a) = 4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive multiplication over pairs of numerator codes needs this local budget.
/-- Multiplicative closure of the numerators: `(2a)(2b) = (2·ab) + (2·ab)`. -/
theorem octNumerator_closed :
    ∀ a b, ∃ c, octNumerator a * octNumerator b = octNumerator c + octNumerator c := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive star lookup over the numerator codes needs this local budget.
/-- Star closure of the numerators. -/
theorem octNumerator_star_closed : ∀ a, ∃ b, octNumerator b = star (octNumerator a) := by decide

/-- The exact list has `48` elements. -/
theorem binaryOctahedral_card : Fintype.card BinaryOctahedral = 48 := by
  decide

/-- Distinct codes represent distinct exact quaternions. -/
theorem binaryOctahedralQuaternion_injective :
    Function.Injective binaryOctahedralQuaternion := by
  intro a b hab
  apply octNumerator_injective
  apply octToExact_injective
  rw [octToExact_octNumerator, octToExact_octNumerator, hab]

theorem binaryOctahedralQuaternion_normSq (a : BinaryOctahedral) :
    Quaternion.normSq (binaryOctahedralQuaternion a) = 1 := by
  have hquad : (2 : SqrtTwoRat) ^ 2 * Quaternion.normSq (binaryOctahedralQuaternion a) = 4 := by
    rw [← Quaternion.normSq_smul, two_smul, ← octToExact_octNumerator, normSq_octToExact,
      octNumerator_normSq]
    simp
  apply sqrtTwoEval_injective
  have h4 := congrArg sqrtTwoEval hquad
  simp only [map_mul, map_pow, map_ofNat, map_one] at h4 ⊢
  norm_num at h4 ⊢
  linarith [h4]

theorem binaryOctahedralQuaternion_closed (a b : BinaryOctahedral) :
    ∃ c, binaryOctahedralQuaternion c =
      binaryOctahedralQuaternion a * binaryOctahedralQuaternion b := by
  obtain ⟨c, hc⟩ := octNumerator_closed a b
  refine ⟨c, ?_⟩
  have key : (binaryOctahedralQuaternion a + binaryOctahedralQuaternion a) *
      (binaryOctahedralQuaternion b + binaryOctahedralQuaternion b) =
      (binaryOctahedralQuaternion c + binaryOctahedralQuaternion c) +
      (binaryOctahedralQuaternion c + binaryOctahedralQuaternion c) := by
    rw [← octToExact_octNumerator, ← octToExact_octNumerator, ← octToExact_octNumerator,
      ← map_mul, hc, map_add]
  -- key : (x+x)(y+y) = (z+z)+(z+z), i.e. (xy + xy) + (xy + xy) = (z+z)+(z+z)
  apply exact_add_self_injective
  apply exact_add_self_injective
  rw [← key]; noncomm_ring

theorem binaryOctahedralQuaternion_star_closed (a : BinaryOctahedral) :
    ∃ b, binaryOctahedralQuaternion b = star (binaryOctahedralQuaternion a) := by
  obtain ⟨b, hb⟩ := octNumerator_star_closed a
  refine ⟨b, ?_⟩
  apply exact_add_self_injective
  rw [← octToExact_octNumerator, hb, octToExact_star, octToExact_octNumerator]
  exact star_add (binaryOctahedralQuaternion a) (binaryOctahedralQuaternion a)

noncomputable instance instMulBinaryOctahedral : Mul BinaryOctahedral where
  mul a b := Classical.choose (binaryOctahedralQuaternion_closed a b)

instance : One BinaryOctahedral := ⟨.axis false 0⟩

noncomputable instance instInvBinaryOctahedral : Inv BinaryOctahedral where
  inv a := Classical.choose (binaryOctahedralQuaternion_star_closed a)

/-- The exact quaternion realization respects multiplication. -/
theorem binaryOctahedralQuaternion_mul (a b : BinaryOctahedral) :
    binaryOctahedralQuaternion (a * b) =
      binaryOctahedralQuaternion a * binaryOctahedralQuaternion b :=
  by
    change binaryOctahedralQuaternion
      (Classical.choose (binaryOctahedralQuaternion_closed a b)) = _
    exact Classical.choose_spec (binaryOctahedralQuaternion_closed a b)

@[simp]
theorem binaryOctahedralQuaternion_one : binaryOctahedralQuaternion 1 = 1 := by
  apply exact_add_self_injective
  rw [← octToExact_octNumerator]
  change octToExact (octNumerator (.axis false 0)) = (1 : ExactQuaternion) + 1
  apply QuaternionAlgebra.ext <;>
    simp only [octNumerator, quaternionBasisZ, Matrix.cons_val_zero, octToExact_re, octToExact_imI,
      octToExact_imJ, octToExact_imK, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul] <;>
    norm_num

@[simp]
theorem binaryOctahedralQuaternion_inv (a : BinaryOctahedral) :
    binaryOctahedralQuaternion a⁻¹ = star (binaryOctahedralQuaternion a) :=
  by
    change binaryOctahedralQuaternion
      (Classical.choose (binaryOctahedralQuaternion_star_closed a)) = _
    exact Classical.choose_spec (binaryOctahedralQuaternion_star_closed a)

noncomputable instance : Group BinaryOctahedral := Group.ofLeftAxioms
  (fun a b c => binaryOctahedralQuaternion_injective <| by
    simp only [binaryOctahedralQuaternion_mul, mul_assoc])
  (fun a => binaryOctahedralQuaternion_injective <| by
    simp only [binaryOctahedralQuaternion_mul, binaryOctahedralQuaternion_one, one_mul])
  (fun a => binaryOctahedralQuaternion_injective <| by
    rw [binaryOctahedralQuaternion_mul, binaryOctahedralQuaternion_inv,
      Quaternion.star_mul_self, binaryOctahedralQuaternion_normSq]
    exact binaryOctahedralQuaternion_one.symm)

/-! ## The faithful strict `SU(2)` realization -/

theorem realQuaternion_mul (p q : ExactQuaternion) :
    realQuaternion (p * q) = realQuaternion p * realQuaternion q := by
  apply QuaternionAlgebra.ext <;>
    simp [realQuaternion, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

theorem realQuaternion_normSq (q : ExactQuaternion) :
    Quaternion.normSq (realQuaternion q) = sqrtTwoEval (Quaternion.normSq q) := by
  simp only [Quaternion.normSq_def', realQuaternion, map_pow, map_add]

/-- The standard faithful embedding of real Hamilton quaternions in complex `2 × 2` matrices. -/
noncomputable def quaternionMatrix (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + (q.imI : ℂ) * Complex.I,
      (q.imJ : ℂ) + (q.imK : ℂ) * Complex.I;
     -(q.imJ : ℂ) + (q.imK : ℂ) * Complex.I,
      (q.re : ℂ) - (q.imI : ℂ) * Complex.I]

theorem quaternionMatrix_mul (p q : Quaternion ℝ) :
    quaternionMatrix (p * q) = quaternionMatrix p * quaternionMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring

theorem quaternionMatrix_det (q : Quaternion ℝ) :
    Matrix.det (quaternionMatrix q) = Quaternion.normSq q := by
  simp [quaternionMatrix, Matrix.det_fin_two, Quaternion.normSq_def']
  ring_nf
  simp [Complex.I_sq]
  ring

theorem quaternionMatrix_star_mul (q : Quaternion ℝ) :
    (quaternionMatrix q)ᴴ * quaternionMatrix q =
      ((Quaternion.normSq q : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.smul_apply, Quaternion.normSq_def'] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem quaternionMatrix_injective : Function.Injective quaternionMatrix := by
  intro p q h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  apply QuaternionAlgebra.ext
  · simpa [quaternionMatrix] using congrArg Complex.re h00
  · simpa [quaternionMatrix] using congrArg Complex.im h00
  · simpa [quaternionMatrix] using congrArg Complex.re h01
  · simpa [quaternionMatrix] using congrArg Complex.im h01

/-- The strict single-qubit Clifford lift as complex matrices. -/
noncomputable def qubitClifford (g : BinaryOctahedral) : Matrix (Fin 2) (Fin 2) ℂ :=
  quaternionMatrix (realQuaternion (binaryOctahedralQuaternion g))

theorem qubitClifford_mul (a b : BinaryOctahedral) :
    qubitClifford (a * b) = qubitClifford a * qubitClifford b := by
  change quaternionMatrix (realQuaternion (binaryOctahedralQuaternion (a * b))) =
    quaternionMatrix (realQuaternion (binaryOctahedralQuaternion a)) *
      quaternionMatrix (realQuaternion (binaryOctahedralQuaternion b))
  rw [binaryOctahedralQuaternion_mul, realQuaternion_mul, quaternionMatrix_mul]

/-- Every strict lift has determinant one. -/
theorem qubitClifford_det (g : BinaryOctahedral) : Matrix.det (qubitClifford g) = 1 := by
  rw [qubitClifford, quaternionMatrix_det, realQuaternion_normSq,
    binaryOctahedralQuaternion_normSq, map_one]
  norm_num

/-- Every strict lift is unitary. -/
theorem qubitClifford_unitary (g : BinaryOctahedral) :
    (qubitClifford g)ᴴ * qubitClifford g = 1 := by
  have hnorm : Quaternion.normSq
      (realQuaternion (binaryOctahedralQuaternion g)) = 1 := by
    rw [realQuaternion_normSq, binaryOctahedralQuaternion_normSq, map_one]
  rw [qubitClifford, quaternionMatrix_star_mul, hnorm]
  simp

/-- The `48` strict matrices remain pairwise distinct. -/
theorem qubitClifford_injective : Function.Injective qubitClifford :=
  quaternionMatrix_injective.comp
    (realQuaternion_injective.comp binaryOctahedralQuaternion_injective)

/-! ## Raw Pauli normalizer grounding -/

/-- The signed raw, unnormalized one-qubit Pauli set `{±X, ±Y, ±Z}`. -/
def signedRawPauliSet : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {P | P = pauliX ∨ P = -pauliX ∨ P = pauliY ∨ P = -pauliY ∨
    P = pauliZ ∨ P = -pauliZ}

private theorem complex_sqrt_two_sq : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem signedRawPauliSet_neg_mem {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : P ∈ signedRawPauliSet) : -P ∈ signedRawPauliSet := by
  change P = pauliX ∨ P = -pauliX ∨ P = pauliY ∨ P = -pauliY ∨
    P = pauliZ ∨ P = -pauliZ at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [signedRawPauliSet]

local macro "pauliConjFinish" : tactic =>
  `(tactic|
    (ext i j <;> fin_cases i <;> fin_cases j <;>
      simp_all [qubitClifford, binaryOctahedralQuaternion, signed, sqrtTwoHalf,
        halfCoefficient, coordinatePair, quaternionBasis, realQuaternion, sqrtTwoEval_apply,
        quaternionMatrix, pauliX, pauliY, pauliZ, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
      try ring_nf <;>
      simp [Complex.I_sq, starRingEnd_apply, complex_sqrt_two_sq,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
      ring_nf <;>
      norm_num))

local macro "pauliMemFinish" : tactic =>
  `(tactic|
    (simp only [signedRawPauliSet, Set.mem_setOf_eq]
     first
     | left; pauliConjFinish; done
     | right; left; pauliConjFinish; done
     | right; right; left; pauliConjFinish; done
     | right; right; right; left; pauliConjFinish; done
     | right; right; right; right; left; pauliConjFinish; done
     | right; right; right; right; right; pauliConjFinish; done))

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-X conjugation over all Clifford codes needs this local budget.
private theorem qubitClifford_conj_pauliX_mem (g : BinaryOctahedral) :
    qubitClifford g * pauliX * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  cases g with
  | axis negative coordinate =>
      fin_cases coordinate <;> cases negative <;>
        pauliMemFinish
  | half negative =>
      by_cases h0 : negative 0 <;> by_cases h1 : negative 1 <;>
        by_cases h2 : negative 2 <;> by_cases h3 : negative 3 <;>
          pauliMemFinish
  | edge pair negativeLeft negativeRight =>
      fin_cases pair <;> cases negativeLeft <;> cases negativeRight <;>
        pauliMemFinish

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-Y conjugation over all Clifford codes needs this local budget.
private theorem qubitClifford_conj_pauliY_mem (g : BinaryOctahedral) :
    qubitClifford g * pauliY * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  cases g with
  | axis negative coordinate =>
      fin_cases coordinate <;> cases negative <;>
        pauliMemFinish
  | half negative =>
      by_cases h0 : negative 0 <;> by_cases h1 : negative 1 <;>
        by_cases h2 : negative 2 <;> by_cases h3 : negative 3 <;>
          pauliMemFinish
  | edge pair negativeLeft negativeRight =>
      fin_cases pair <;> cases negativeLeft <;> cases negativeRight <;>
        pauliMemFinish

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-Z conjugation over all Clifford codes needs this local budget.
private theorem qubitClifford_conj_pauliZ_mem (g : BinaryOctahedral) :
    qubitClifford g * pauliZ * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  cases g with
  | axis negative coordinate =>
      fin_cases coordinate <;> cases negative <;>
        pauliMemFinish
  | half negative =>
      by_cases h0 : negative 0 <;> by_cases h1 : negative 1 <;>
        by_cases h2 : negative 2 <;> by_cases h3 : negative 3 <;>
          pauliMemFinish
  | edge pair negativeLeft negativeRight =>
      fin_cases pair <;> cases negativeLeft <;> cases negativeRight <;>
        pauliMemFinish

/-- The strict single-qubit Clifford lift normalizes the signed raw Pauli axes. -/
theorem qubitClifford_conj_pauli_mem (g : BinaryOctahedral)
    {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ signedRawPauliSet) :
    qubitClifford g * P * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  change P = pauliX ∨ P = -pauliX ∨ P = pauliY ∨ P = -pauliY ∨
    P = pauliZ ∨ P = -pauliZ at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · exact qubitClifford_conj_pauliX_mem g
  · simpa [mul_neg, neg_mul, Matrix.mul_assoc] using
      signedRawPauliSet_neg_mem (qubitClifford_conj_pauliX_mem g)
  · exact qubitClifford_conj_pauliY_mem g
  · simpa [mul_neg, neg_mul, Matrix.mul_assoc] using
      signedRawPauliSet_neg_mem (qubitClifford_conj_pauliY_mem g)
  · exact qubitClifford_conj_pauliZ_mem g
  · simpa [mul_neg, neg_mul, Matrix.mul_assoc] using
      signedRawPauliSet_neg_mem (qubitClifford_conj_pauliZ_mem g)

/-! ## The doubled Clifford commutant -/

/-- The tensor-factor swap on two qubits. -/
def qubitSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun p q =>
  if p = (q.2, q.1) then 1 else 0

theorem kronecker_self_commute_qubitSwap (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (U ⊗ₖ U) * qubitSwap = qubitSwap * (U ⊗ₖ U) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, qubitSwap]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [mul_comm] <;> ring

theorem su2_casimir_eq_swap_sub :
    su2HermBasis.casimir = qubitSwap - (1 / 2 : ℂ) • 1 := by
  rw [DLAHermBasis.casimir]
  change (∑ j : Fin 3, su2B j ⊗ₖ su2B j) = qubitSwap - (1 / 2 : ℂ) • 1
  rw [Fin.sum_univ_three]
  have hrt : rt2inv ^ 2 = (1 / 2 : ℂ) := by simpa [pow_two] using rt2inv_mul_self
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [su2B, pauliX, pauliY, pauliZ, qubitSwap,
      Matrix.smul_apply, rt2inv_mul_self] <;> ring_nf <;>
      simp [hrt, Complex.I_sq] <;> norm_num

/-- The strict Clifford lift fixes the normalized `su(2)` Casimir pointwise. -/
theorem qubitClifford_casimir_commute (g : BinaryOctahedral) :
    (qubitClifford g ⊗ₖ qubitClifford g) * su2HermBasis.casimir =
      su2HermBasis.casimir * (qubitClifford g ⊗ₖ qubitClifford g) := by
  rw [su2_casimir_eq_swap_sub, Matrix.mul_sub, Matrix.sub_mul,
    kronecker_self_commute_qubitSwap]
  simp

/-- A finite unitary ensemble is doubled-commutant complete for `b` if every doubled-operator
commuting with the finite doubled action already lies in the Lie-algebra doubled commutant used by
the Ragone second-moment interface. This is the `2`-design property in the form consumed here. -/
def IsDoubledCommutantComplete {N : ℕ} {G : Type*}
    (u : G → Matrix (Fin N) (Fin N) ℂ)
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens) : Prop :=
  ∀ M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
    (∀ g, (u g ⊗ₖ u g) * M = M * (u g ⊗ₖ u g)) → M ∈ adCommutantGG b

private theorem qubitClifford_commutant_normal_form
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : ∀ g, (qubitClifford g ⊗ₖ qubitClifford g) * M =
      M * (qubitClifford g ⊗ₖ qubitClifford g)) :
    M = M (1, 0) (1, 0) • 1 +
      (M (0, 0) (0, 0) - M (1, 0) (1, 0)) • qubitSwap := by
  have hI := hM (.axis false 1)
  have hJ := hM (.axis false 2)
  have hH := hM (.half fun _ => false)
  have hI01 := congrFun (congrFun hI (0, 0)) (0, 1)
  have hI02 := congrFun (congrFun hI (0, 0)) (1, 0)
  have hI10 := congrFun (congrFun hI (0, 1)) (0, 0)
  have hI13 := congrFun (congrFun hI (0, 1)) (1, 1)
  have hI20 := congrFun (congrFun hI (1, 0)) (0, 0)
  have hI23 := congrFun (congrFun hI (1, 0)) (1, 1)
  have hI31 := congrFun (congrFun hI (1, 1)) (0, 1)
  have hI32 := congrFun (congrFun hI (1, 1)) (1, 0)
  have hJ03 := congrFun (congrFun hJ (0, 0)) (1, 1)
  have hJ00 := congrFun (congrFun hJ (0, 0)) (0, 0)
  have hJ11 := congrFun (congrFun hJ (0, 1)) (0, 1)
  have hJ12 := congrFun (congrFun hJ (0, 1)) (1, 0)
  have hH00 := congrFun (congrFun hH (0, 0)) (0, 0)
  have hH01 := congrFun (congrFun hH (0, 0)) (0, 1)
  simp only [qubitClifford, quaternionMatrix, realQuaternion,
    binaryOctahedralQuaternion, signed, Bool.false_eq_true, ↓reduceIte,
    quaternionBasis, Fin.isValue, cons_val_one, cons_val_zero, one_smul,
    sqrtTwoEval_apply, QuadraticAlgebra.re_zero, Rat.cast_zero,
    QuadraticAlgebra.im_zero, zero_mul, add_zero, QuadraticAlgebra.re_one,
    Rat.cast_one, QuadraticAlgebra.im_one, Complex.ofReal_zero,
    Complex.ofReal_one, one_mul, zero_add, neg_zero, zero_sub,
    Matrix.mul_apply, kroneckerMap_apply, of_apply, cons_val',
    cons_val_fin_one, Fintype.sum_prod_type, Fin.sum_univ_two, mul_zero,
    Complex.I_mul_I, neg_mul, mul_neg, Finset.sum_neg_distrib, mul_one,
    neg_neg] at hI01 hI02 hI10 hI13 hI20 hI23 hI31 hI32
  simp only [qubitClifford, quaternionMatrix, realQuaternion,
    binaryOctahedralQuaternion, signed, Bool.false_eq_true, ↓reduceIte,
    quaternionBasis, Fin.isValue, cons_val, one_smul, sqrtTwoEval_apply,
    QuadraticAlgebra.re_zero, Rat.cast_zero, QuadraticAlgebra.im_zero,
    zero_mul, add_zero, QuadraticAlgebra.re_one, Rat.cast_one,
    QuadraticAlgebra.im_one, Complex.ofReal_zero, Complex.ofReal_one,
    sub_self, Matrix.mul_apply, kroneckerMap_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, cons_val_one, Fintype.sum_prod_type,
    Fin.sum_univ_two, mul_zero, mul_one, zero_add, one_mul, mul_neg,
    Finset.sum_neg_distrib, neg_neg, neg_mul, neg_inj] at hJ03 hJ00 hJ11 hJ12
  simp only [qubitClifford, quaternionMatrix, realQuaternion,
    binaryOctahedralQuaternion, halfCoefficient, signed, Bool.false_eq_true,
    ↓reduceIte, one_div, sqrtTwoEval_apply, Rat.cast_inv, Rat.cast_ofNat,
    Rat.cast_zero, zero_mul, add_zero, Complex.ofReal_inv,
    Complex.ofReal_ofNat, Fin.isValue, Matrix.mul_apply, kroneckerMap_apply,
    of_apply, cons_val', cons_val_fin_one, cons_val_zero,
    Fintype.sum_prod_type, Fin.sum_univ_two, cons_val_one] at hH00 hH01
  have e01 : M (0, 0) (0, 1) = 0 := by linear_combination (-1 / 2 : ℂ) * hI01
  have e02 : M (0, 0) (1, 0) = 0 := by linear_combination (-1 / 2 : ℂ) * hI02
  have e10 : M (0, 1) (0, 0) = 0 := by linear_combination (1 / 2 : ℂ) * hI10
  have e13 : M (0, 1) (1, 1) = 0 := by linear_combination (1 / 2 : ℂ) * hI13
  have e20 : M (1, 0) (0, 0) = 0 := by linear_combination (1 / 2 : ℂ) * hI20
  have e23 : M (1, 0) (1, 1) = 0 := by linear_combination (1 / 2 : ℂ) * hI23
  have e31 : M (1, 1) (0, 1) = 0 := by linear_combination (-1 / 2 : ℂ) * hI31
  have e32 : M (1, 1) (1, 0) = 0 := by linear_combination (-1 / 2 : ℂ) * hI32
  have e0033 : M (0, 0) (0, 0) = M (1, 1) (1, 1) := by
    linear_combination -hJ03
  have e0312 : M (0, 0) (1, 1) = M (1, 1) (0, 0) := by
    linear_combination -hJ00
  have e1221 : M (0, 1) (1, 0) = M (1, 0) (0, 1) := by
    linear_combination -hJ11
  have e1122 : M (0, 1) (0, 1) = M (1, 0) (1, 0) := by
    linear_combination -hJ12
  simp [e01, e02, e10, e20, e0312] at hH00
  ring_nf at hH00
  simp [Complex.I_sq] at hH00
  have e30 : M (1, 1) (0, 0) = 0 := hH00.resolve_left (by norm_num)
  have e03 : M (0, 0) (1, 1) = 0 := e0312.trans e30
  simp [e01, e02, e03, e31, e1122] at hH01
  ring_nf at hH01
  rw [Complex.I_sq] at hH01
  have e12 : M (0, 1) (1, 0) =
      M (0, 0) (0, 0) - M (0, 1) (0, 1) := by
    linear_combination (-2 * Complex.I) * hH01 + e1221 + e1122 +
      (-M (0, 0) (0, 0) + M (1, 0) (0, 1) + M (1, 0) (1, 0)) * Complex.I_sq
  have e21 : M (1, 0) (0, 1) =
      M (0, 0) (0, 0) - M (0, 1) (0, 1) := e1221.symm.trans e12
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [qubitSwap, e01, e02, e03, e10, e12, e13, e20, e21, e23, e30, e31, e32,
      e0033, e1122]

theorem one_mem_su2_adCommutantGG :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∈ adCommutantGG su2HermBasis := by
  rw [adCommutantGG, Submodule.mem_iInf]
  intro j
  rw [LinearMap.mem_ker]
  simp [doubledAd]

theorem qubitSwap_mem_su2_adCommutantGG : qubitSwap ∈ adCommutantGG su2HermBasis := by
  have hswap : qubitSwap = su2HermBasis.casimir + (1 / 2 : ℂ) • 1 := by
    rw [su2_casimir_eq_swap_sub]
    module
  rw [hswap]
  exact (adCommutantGG su2HermBasis).add_mem (casimir_mem_adCommutantGG su2HermBasis)
    ((adCommutantGG su2HermBasis).smul_mem _ one_mem_su2_adCommutantGG)

/-- The strict single-qubit Clifford lift is doubled-commutant complete for `su(2)`. -/
theorem qubitClifford_isDoubledCommutantComplete :
    IsDoubledCommutantComplete qubitClifford su2HermBasis := by
  intro M hM
  rw [qubitClifford_commutant_normal_form M hM]
  exact (adCommutantGG su2HermBasis).add_mem
    ((adCommutantGG su2HermBasis).smul_mem _ one_mem_su2_adCommutantGG)
    ((adCommutantGG su2HermBasis).smul_mem _ qubitSwap_mem_su2_adCommutantGG)

/-- Commuting with the finite doubled Clifford action implies Lie-algebra doubled invariance. -/
theorem qubitClifford_bridge
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : ∀ g, (qubitClifford g ⊗ₖ qubitClifford g) * M =
      M * (qubitClifford g ⊗ₖ qubitClifford g)) :
    M ∈ adCommutantGG su2HermBasis :=
  qubitClifford_isDoubledCommutantComplete M hM

private theorem qubitClifford_commutant_scalar
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ g, qubitClifford g * M = M * qubitClifford g) :
    ∃ c : ℂ, M = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨M 0 0, ?_⟩
  have hI := hM (.axis false 1)
  have hH := hM (.half fun _ => false)
  have hI01 := congrFun (congrFun hI 0) 1
  have hI10 := congrFun (congrFun hI 1) 0
  have hH01 := congrFun (congrFun hH 0) 1
  simp only [qubitClifford, quaternionMatrix, realQuaternion,
    binaryOctahedralQuaternion, signed, Bool.false_eq_true, ↓reduceIte,
    quaternionBasis, Fin.isValue, cons_val_one, cons_val_zero, one_smul,
    sqrtTwoEval_apply, QuadraticAlgebra.re_zero, Rat.cast_zero,
    QuadraticAlgebra.im_zero, zero_mul, add_zero, QuadraticAlgebra.re_one,
    Rat.cast_one, QuadraticAlgebra.im_one, Complex.ofReal_zero,
    Complex.ofReal_one, one_mul, zero_add, neg_zero, zero_sub,
    Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one,
    Fin.sum_univ_two, mul_zero, mul_neg] at hI01
  simp only [qubitClifford, quaternionMatrix, realQuaternion,
    binaryOctahedralQuaternion, signed, Bool.false_eq_true, ↓reduceIte,
    quaternionBasis, Fin.isValue, cons_val_one, cons_val_zero, one_smul,
    sqrtTwoEval_apply, QuadraticAlgebra.re_zero, Rat.cast_zero,
    QuadraticAlgebra.im_zero, zero_mul, add_zero, QuadraticAlgebra.re_one,
    Rat.cast_one, QuadraticAlgebra.im_one, Complex.ofReal_zero,
    Complex.ofReal_one, one_mul, zero_add, neg_zero, zero_sub,
    Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one,
    Fin.sum_univ_two, neg_mul, mul_zero] at hI10
  simp only [qubitClifford, quaternionMatrix, realQuaternion,
    binaryOctahedralQuaternion, halfCoefficient, signed, Bool.false_eq_true,
    ↓reduceIte, one_div, sqrtTwoEval_apply, Rat.cast_inv, Rat.cast_ofNat,
    Rat.cast_zero, zero_mul, add_zero, Complex.ofReal_inv,
    Complex.ofReal_ofNat, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, Fin.sum_univ_two, cons_val_one] at hH01
  have hI01' : (2 * Complex.I) * M 0 1 = 0 := by
    have hsum : Complex.I * M 0 1 + M 0 1 * Complex.I = 0 := by
      rw [hI01]
      ring
    rw [← hsum]
    ring
  have e01 : M 0 1 = 0 :=
    (mul_eq_zero.mp hI01').resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hI10' : (2 * Complex.I) * M 1 0 = 0 := by
    have hsum : Complex.I * M 1 0 + M 1 0 * Complex.I = 0 := by
      linear_combination -hI10
    rw [← hsum]
    ring
  have e10 : M 1 0 = 0 :=
    (mul_eq_zero.mp hI10').resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hH01' : (2⁻¹ + 2⁻¹ * Complex.I : ℂ) * M 1 1 =
      M 0 0 * (2⁻¹ + 2⁻¹ * Complex.I : ℂ) := by
    simpa [e01, e10] using hH01
  have hcoef : (2⁻¹ + 2⁻¹ * Complex.I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have e11 : M 1 1 = M 0 0 := by
    rw [mul_comm (M 0 0)] at hH01'
    exact mul_left_cancel₀ hcoef hH01'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e01, e10, e11]

/-- The single-qubit Clifford lift has scalar first moment. -/
theorem qubitClifford_repTwirl_eq_scalar (O : Matrix (Fin 2) (Fin 2) ℂ) :
    repTwirl qubitClifford O = (O.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  repTwirl_eq_scalar qubitClifford qubitClifford_mul qubitClifford_unitary O
    qubitClifford_commutant_scalar

/-- Traceless observables have zero single-qubit Clifford first moment. -/
theorem qubitClifford_repTwirl_eq_zero_of_trace_eq_zero
    (O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    repTwirl qubitClifford O = 0 :=
  repTwirl_eq_zero_of_trace_eq_zero qubitClifford O
    (qubitClifford_repTwirl_eq_scalar O) htr

/-- The scalar Clifford first moment gives zero averaged loss for traceless observables. -/
theorem qubitClifford_loss_mean_eq_zero
    (ρ O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    (ρ * repTwirl qubitClifford O).trace = 0 :=
  repTwirl_trace_pairing_eq_zero_of_trace_eq_zero qubitClifford ρ O
    (qubitClifford_repTwirl_eq_scalar O) htr

/-- The trace pairing of `ρ` with the Clifford conjugate of `O` at the code `g`. -/
noncomputable def cliffordLoss (ρ O : Matrix (Fin 2) (Fin 2) ℂ)
    (g : BinaryOctahedral) : ℂ :=
  (ρ * (qubitClifford g * O * (qubitClifford g)ᴴ)).trace

theorem cliffordLoss_mean_eq_trace_repTwirl (ρ O : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, cliffordLoss ρ O g =
      (ρ * repTwirl qubitClifford O).trace := by
  unfold cliffordLoss repTwirl
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum, smul_eq_mul]

theorem cliffordLoss_mean_eq_zero_of_trace_eq_zero
    (ρ O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, cliffordLoss ρ O g = 0 := by
  rw [cliffordLoss_mean_eq_trace_repTwirl, qubitClifford_loss_mean_eq_zero ρ O htr]

theorem cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    (ρ O : Matrix (Fin 2) (Fin 2) ℂ) (htr : O.trace = 0) :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss ρ O g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ h, cliffordLoss ρ O h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, (cliffordLoss ρ O g) ^ 2 :=
  secondMoment_eq_centered_of_mean_zero (cliffordLoss ρ O)
    (cliffordLoss_mean_eq_zero_of_trace_eq_zero ρ O htr)

theorem trace_qubitSwap : Matrix.trace qubitSwap = 2 := by
  have hfixed : ({x : Fin 2 × Fin 2 | x = (x.2, x.1)} : Finset _).card = 2 := by
    decide
  simp [Matrix.trace, qubitSwap, hfixed]

theorem su2_casimir_hsInner_one :
    hsInner su2HermBasis.casimir (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 0 := by
  have hfixed : ({x : Fin 2 × Fin 2 | x = (x.2, x.1)} : Finset _).card = 2 := by
    decide
  simp [hsInner, su2_casimir_eq_swap_sub, qubitSwap, Matrix.trace,
    Matrix.conjTranspose_apply, hfixed]
  norm_num

theorem su2_casimir_hsInner_qubitSwap :
    hsInner su2HermBasis.casimir qubitSwap = 3 := by
  simp [hsInner, su2_casimir_eq_swap_sub, qubitSwap, Matrix.trace,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- The doubled Clifford twirl of one normalized Pauli tensor is one third Casimir. This is the
concrete single-qubit realization of the carrier and one-dimensional Casimir projections in
[RBS+23, `Arxiv_Final.tex:1253-1285`]. The finite-design input is consumed through
`qubitClifford_isDoubledCommutantComplete`. -/
theorem qubitClifford_twirl_basis_zero :
    twirl2 qubitClifford (su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0) =
      (1 / 3 : ℂ) • su2HermBasis.casimir := by
  let X := su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0
  let T := twirl2 qubitClifford X
  have hnormal : T = T (1, 0) (1, 0) • 1 +
      (T (0, 0) (0, 0) - T (1, 0) (1, 0)) • qubitSwap :=
    qubitClifford_commutant_normal_form T fun g =>
      twirl2_commute qubitClifford qubitClifford_mul qubitClifford_unitary X g
  have htrace : Matrix.trace T = 0 := by
    change Matrix.trace (twirl2 qubitClifford X) = 0
    rw [twirl2_trace qubitClifford qubitClifford_unitary X]
    change Matrix.trace ((rt2inv • pauliX) ⊗ₖ (rt2inv • pauliX)) = 0
    rw [Matrix.trace_kronecker]
    simp [pauliX, Matrix.trace_fin_two]
  have hproj : hsInner su2HermBasis.casimir T = 1 := by
    have h := twirl2_proj_orth qubitClifford qubitClifford_mul qubitClifford_unitary
      su2HermBasis qubitClifford_casimir_commute (su2HermBasis.B su2i0)
    rw [su2HermBasis.casimir_hsInner_kron (su2HermBasis.herm su2i0),
      su2HermBasis.gPurity_basis_elem] at h
    exact h.symm
  rw [hnormal, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, trace_qubitSwap] at htrace
  norm_num at htrace
  rw [hnormal, hsInner_add_right, hsInner_smul_right, hsInner_smul_right,
    su2_casimir_hsInner_one, su2_casimir_hsInner_qubitSwap] at hproj
  norm_num at hproj
  have hbeta : T (0, 0) (0, 0) - T (1, 0) (1, 0) = (1 / 3 : ℂ) := by
    linear_combination (1 / 3 : ℂ) * hproj
  have halpha : T (1, 0) (1, 0) = (-1 / 6 : ℂ) := by
    linear_combination (1 / 4 : ℂ) * htrace - (1 / 2 : ℂ) * hbeta
  change T = (1 / 3 : ℂ) • su2HermBasis.casimir
  rw [hnormal, su2_casimir_eq_swap_sub, hbeta, halpha]
  module

theorem qubitClifford_twirl_basis_zero_mem_gTensorG :
    twirl2 qubitClifford (su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0) ∈
      gTensorG su2HermBasis := by
  rw [qubitClifford_twirl_basis_zero]
  exact (gTensorG su2HermBasis).smul_mem _ (casimir_mem_gTensorG su2HermBasis)

/-- The concrete single-qubit Clifford second moment for the normalized first Pauli basis element.
The `48` strict lifts reduce to `24` projective gates, their doubled twirl is derived independently
from finite-group commutation, trace preservation, Casimir fixing, and doubled-commutant
completeness, and the result instantiates Ragone's second-moment carrier/Casimir projection
[RBS+23, `Arxiv_Final.tex:1253-1285`; Web15, `Cliffords_are_a_3-design.tex:616-619`]. -/
noncomputable def main : RagoneSecondMoment su2HermBasis
    (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) :=
  RagoneSecondMoment.ofTwoDesign su2HermBasis qubitClifford qubitClifford_mul
    qubitClifford_unitary (su2HermBasis.herm su2i0) (su2HermBasis.herm su2i0)
    su2HermBasis_schur qubitClifford_casimir_commute qubitClifford_isDoubledCommutantComplete
    qubitClifford_twirl_basis_zero_mem_gTensorG

/-- **Fully unconditional `su(2)` barren-plateau second moment.** Assembling the `SimpleSU`
reduction on the genuine second moment `main`, the `su(2)` loss second moment equals `1/3` — where
the finite twirl input is discharged by `qubitClifford_isDoubledCommutantComplete`, the Schur
identity is discharged by `su2HermBasis_schur` (H2), and there is **no** deferred hypothesis and
**no** hand-set `consistencyWitness`. The first-moment lemmas above identify the same expression
with centered loss
variance for traceless observables. -/
theorem main_variance_eq_third : (main.variance : ℂ) = 1 / 3 := by
  rw [SimpleSU.main main
      (su2HermBasis.herm su2i0) (su2HermBasis.herm su2i0) (d := 2) rfl
      su2HermBasis_dim_pos, su2HermBasis.gPurity_basis_elem su2i0]
  norm_num

theorem su2BasisZero_trace_eq_zero : (su2HermBasis.B su2i0).trace = 0 := by
  change Matrix.trace (rt2inv • pauliX) = 0
  rw [Matrix.trace_smul]
  simp [pauliX, Matrix.trace_fin_two]

theorem main_centeredLoss_eq_uncenteredLoss :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ *
            ∑ h, cliffordLoss (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) g) ^ 2 :=
  cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) su2BasisZero_trace_eq_zero

/-- A nondegenerate single-qubit `su(2)` Hermitian witness operator: a strict contraction of the
first normalized Pauli basis element. -/
noncomputable def su2NondegenerateRho : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • su2HermBasis.B su2i0

/-- A nondegenerate single-qubit `su(2)` witness observable, scaled differently from
`su2NondegenerateRho`. -/
noncomputable def su2NondegenerateO : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 3 : ℂ) • su2HermBasis.B su2i0

theorem su2NondegenerateRho_isHermitian : su2NondegenerateRhoᴴ = su2NondegenerateRho := by
  simp [su2NondegenerateRho, Matrix.conjTranspose_smul, su2HermBasis.herm su2i0]

theorem su2NondegenerateO_isHermitian : su2NondegenerateOᴴ = su2NondegenerateO := by
  simp [su2NondegenerateO, Matrix.conjTranspose_smul, su2HermBasis.herm su2i0]

private theorem su2_gPurity_smul_basis_zero (c : ℂ) :
    su2HermBasis.gPurity (c • su2HermBasis.B su2i0) = (Complex.normSq c : ℂ) := by
  rw [DLAHermBasis.gPurity]
  have hterm :
      ∀ j, (Complex.normSq (hsInner (su2HermBasis.B j) (c • su2HermBasis.B su2i0)) : ℂ)
        = if j = su2i0 then (Complex.normSq c : ℂ) else 0 := by
    intro j
    rw [hsInner_smul_right, su2HermBasis.ortho j su2i0]
    split <;> simp
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq']
  simp

theorem su2NondegenerateRho_gPurity :
    su2HermBasis.gPurity su2NondegenerateRho = (1 / 4 : ℂ) := by
  rw [su2NondegenerateRho, su2_gPurity_smul_basis_zero]
  norm_num [Complex.normSq_ratCast]

theorem su2NondegenerateO_gPurity :
    su2HermBasis.gPurity su2NondegenerateO = (1 / 9 : ℂ) := by
  rw [su2NondegenerateO, su2_gPurity_smul_basis_zero]
  norm_num [Complex.normSq_ratCast]

theorem su2NondegenerateRho_ne_O : su2NondegenerateRho ≠ su2NondegenerateO := by
  intro h
  have hp : su2HermBasis.gPurity su2NondegenerateRho =
      su2HermBasis.gPurity su2NondegenerateO := by rw [h]
  rw [su2NondegenerateRho_gPurity, su2NondegenerateO_gPurity] at hp
  norm_num at hp

private theorem su2NondegenerateO_kron :
    su2NondegenerateO ⊗ₖ su2NondegenerateO =
      (1 / 9 : ℂ) • (su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0) := by
  rw [su2NondegenerateO, Matrix.smul_kronecker, Matrix.kronecker_smul]
  module

theorem su2NondegenerateO_twirl_mem_gTensorG :
    twirl2 qubitClifford (su2NondegenerateO ⊗ₖ su2NondegenerateO) ∈
      gTensorG su2HermBasis := by
  rw [su2NondegenerateO_kron, QuantumAlg.twirl2_smul]
  exact (gTensorG su2HermBasis).smul_mem _ qubitClifford_twirl_basis_zero_mem_gTensorG

/-- The single-qubit Clifford doubled-commutant-complete second moment for the nondegenerate scaled
`su(2)` Hermitian-operator witness pair. -/
noncomputable def su2NondegenerateSecondMoment :
    RagoneSecondMoment su2HermBasis su2NondegenerateRho su2NondegenerateO :=
  RagoneSecondMoment.ofTwoDesign su2HermBasis qubitClifford qubitClifford_mul
    qubitClifford_unitary su2NondegenerateRho_isHermitian su2NondegenerateO_isHermitian
    su2HermBasis_schur qubitClifford_casimir_commute qubitClifford_isDoubledCommutantComplete
    su2NondegenerateO_twirl_mem_gTensorG

theorem su2NondegenerateSecondMoment_variance_eq_gPurity :
    (su2NondegenerateSecondMoment.variance : ℂ) =
      su2HermBasis.gPurity su2NondegenerateRho *
        su2HermBasis.gPurity su2NondegenerateO / (3 : ℂ) := by
  rw [RagoneSecondMoment.variance_eq_gPurity su2NondegenerateSecondMoment
      su2NondegenerateRho_isHermitian su2NondegenerateO_isHermitian su2HermBasis_dim_pos,
    su2HermBasis_dim_eq]
  norm_num

theorem su2NondegenerateSecondMoment_variance_eq :
    (su2NondegenerateSecondMoment.variance : ℂ) = (1 / 108 : ℂ) := by
  rw [su2NondegenerateSecondMoment_variance_eq_gPurity, su2NondegenerateRho_gPurity,
    su2NondegenerateO_gPurity]
  norm_num

/-- A concrete nondegenerate `su(2)` Hermitian-operator witness through the Clifford doubled
twirl: `ρ ≠ O`, both `g`-purities are strict contractions, and the Ragone variance law evaluates
to `P_g(ρ) P_g(O) / 3 = 1/108`, not the degenerate `1/3` value. -/
theorem su2_variance_nondegenerate_witness :
    ∃ ρ O : Matrix (Fin 2) (Fin 2) ℂ, ∃ M : RagoneSecondMoment su2HermBasis ρ O,
      ρᴴ = ρ ∧ Oᴴ = O ∧ ρ ≠ O ∧
        su2HermBasis.gPurity ρ = (1 / 4 : ℂ) ∧
        su2HermBasis.gPurity O = (1 / 9 : ℂ) ∧
        0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1 ∧
        0 < (1 / 9 : ℝ) ∧ (1 / 9 : ℝ) < 1 ∧
        (M.variance : ℂ) = su2HermBasis.gPurity ρ * su2HermBasis.gPurity O / (3 : ℂ) ∧
        (M.variance : ℂ) = (1 / 108 : ℂ) ∧
        (M.variance : ℂ) ≠ (1 / 3 : ℂ) := by
  refine ⟨su2NondegenerateRho, su2NondegenerateO, su2NondegenerateSecondMoment, ?_⟩
  exact ⟨su2NondegenerateRho_isHermitian, su2NondegenerateO_isHermitian,
    su2NondegenerateRho_ne_O, su2NondegenerateRho_gPurity, su2NondegenerateO_gPurity,
    by norm_num, by norm_num, by norm_num, by norm_num,
    su2NondegenerateSecondMoment_variance_eq_gPurity,
    su2NondegenerateSecondMoment_variance_eq,
    by rw [su2NondegenerateSecondMoment_variance_eq]; norm_num⟩

theorem su2NondegenerateO_trace_eq_zero : su2NondegenerateO.trace = 0 := by
  rw [su2NondegenerateO, Matrix.trace_smul, su2BasisZero_trace_eq_zero]
  simp

theorem su2NondegenerateSecondMoment_centeredLoss_eq_uncenteredLoss :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2NondegenerateRho su2NondegenerateO g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ *
            ∑ h, cliffordLoss su2NondegenerateRho su2NondegenerateO h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2NondegenerateRho su2NondegenerateO g) ^ 2 :=
  cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    su2NondegenerateRho su2NondegenerateO su2NondegenerateO_trace_eq_zero

/-! ### A genuine mixed-state witness -/

/-- A genuine mixed single-qubit density operator with the same `su(2)` projection as
`su2NondegenerateRho`: `ρ = 1/2 · I + 1/2 · B₀`. -/
noncomputable def su2MixedStateRho : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 / 2 : ℂ) • su2HermBasis.B su2i0

theorem su2MixedStateRho_isHermitian : su2MixedStateRhoᴴ = su2MixedStateRho := by
  simp [su2MixedStateRho, Matrix.conjTranspose_smul, su2HermBasis.herm su2i0]

theorem su2MixedStateRho_trace : su2MixedStateRho.trace = 1 := by
  rw [su2MixedStateRho, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, su2BasisZero_trace_eq_zero]
  norm_num

theorem su2MixedStateRho_eq_matrix :
    su2MixedStateRho =
      !![(1 / 2 : ℂ), (1 / 2 : ℂ) * rt2inv;
         (1 / 2 : ℂ) * rt2inv, (1 / 2 : ℂ)] := by
  change (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 / 2 : ℂ) • (rt2inv • pauliX) =
    !![(1 / 2 : ℂ), (1 / 2 : ℂ) * rt2inv;
       (1 / 2 : ℂ) * rt2inv, (1 / 2 : ℂ)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]

theorem su2MixedStateRho_posSemidef : Matrix.PosSemidef su2MixedStateRho := by
  rw [su2MixedStateRho_eq_matrix]
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![rt2inv, (1 / 2 : ℂ); 0, (1 / 2 : ℂ)]
  have hchol :
      !![(1 / 2 : ℂ), (1 / 2 : ℂ) * rt2inv;
         (1 / 2 : ℂ) * rt2inv, (1 / 2 : ℂ)] = Aᴴ * A := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, one_div, Fin.zero_eta, Fin.isValue,
        of_apply, cons_val', cons_val_zero, cons_val_fin_one]
      rw [rt2inv_conj, rt2inv_mul_self]
      norm_num
    · simp only [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, one_div, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, of_apply, cons_val', cons_val_one, cons_val_fin_one,
        cons_val_zero, star_zero]
      rw [rt2inv_conj]
      ring
    · simp [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
      norm_num [starRingEnd_apply]
    · simp [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
      norm_num [starRingEnd_apply]
  rw [hchol]
  exact Matrix.posSemidef_conjTranspose_mul_self A

private theorem su2_gPurity_add_scalar_basis_zero (c d : ℂ) :
    su2HermBasis.gPurity (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        d • su2HermBasis.B su2i0) = (Complex.normSq d : ℂ) := by
  rw [DLAHermBasis.gPurity]
  have hterm :
      ∀ j, (Complex.normSq
          (hsInner (su2HermBasis.B j)
            (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + d • su2HermBasis.B su2i0)) : ℂ)
        = if j = su2i0 then (Complex.normSq d : ℂ) else 0 := by
    intro j
    rw [hsInner_add_right, hsInner_smul_right, hsInner_smul_right,
      su2HermBasis.ortho j su2i0]
    have hone : hsInner (su2HermBasis.B j) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
      fin_cases j
      · change hsInner (rt2inv • pauliX) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0
        simp [hsInner, pauliX, Matrix.trace_fin_two]
      · change hsInner (rt2inv • pauliY) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0
        simp [hsInner, pauliY, Matrix.trace_fin_two]
      · change hsInner (rt2inv • pauliZ) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0
        simp [hsInner, pauliZ, Matrix.trace_fin_two]
    rw [hone]
    by_cases hj : j = su2i0 <;> simp [hj]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq']
  simp

theorem su2MixedStateRho_gPurity :
    su2HermBasis.gPurity su2MixedStateRho = (1 / 4 : ℂ) := by
  rw [su2MixedStateRho, su2_gPurity_add_scalar_basis_zero]
  norm_num [Complex.normSq_ratCast]

/-- The Clifford second-moment witness for `su2MixedStateRho` and `su2NondegenerateO`. -/
noncomputable def su2MixedStateSecondMoment :
    RagoneSecondMoment su2HermBasis su2MixedStateRho su2NondegenerateO :=
  RagoneSecondMoment.ofTwoDesign su2HermBasis qubitClifford qubitClifford_mul
    qubitClifford_unitary su2MixedStateRho_isHermitian su2NondegenerateO_isHermitian
    su2HermBasis_schur qubitClifford_casimir_commute qubitClifford_isDoubledCommutantComplete
    su2NondegenerateO_twirl_mem_gTensorG

theorem su2MixedStateSecondMoment_variance_eq_gPurity :
    (su2MixedStateSecondMoment.variance : ℂ) =
      su2HermBasis.gPurity su2MixedStateRho *
        su2HermBasis.gPurity su2NondegenerateO / (3 : ℂ) := by
  rw [RagoneSecondMoment.variance_eq_gPurity su2MixedStateSecondMoment
      su2MixedStateRho_isHermitian su2NondegenerateO_isHermitian su2HermBasis_dim_pos,
    su2HermBasis_dim_eq]
  norm_num

theorem su2MixedStateSecondMoment_variance_eq_uncenteredLoss :
    (su2MixedStateSecondMoment.variance : ℂ) =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g) ^ 2 := by
  rw [su2MixedStateSecondMoment.var_eq]
  change hsInner (su2MixedStateRho ⊗ₖ su2MixedStateRho)
      (twirl2 qubitClifford (su2NondegenerateO ⊗ₖ su2NondegenerateO)) =
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
      ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g) ^ 2
  exact twirl2_hsInner_eq_loss_secondMoment qubitClifford
    su2MixedStateRho su2NondegenerateO su2MixedStateRho_isHermitian

theorem su2MixedStateSecondMoment_variance_eq :
    (su2MixedStateSecondMoment.variance : ℂ) = (1 / 108 : ℂ) := by
  rw [su2MixedStateSecondMoment_variance_eq_gPurity, su2MixedStateRho_gPurity,
    su2NondegenerateO_gPurity]
  norm_num

theorem su2MixedStateSecondMoment_centeredLoss_eq_uncenteredLoss :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ *
            ∑ h, cliffordLoss su2MixedStateRho su2NondegenerateO h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g) ^ 2 :=
  cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    su2MixedStateRho su2NondegenerateO su2NondegenerateO_trace_eq_zero

theorem su2MixedStateRho_ne_O : su2MixedStateRho ≠ su2NondegenerateO := by
  intro h
  have htr := congrArg Matrix.trace h
  rw [su2MixedStateRho_trace, su2NondegenerateO_trace_eq_zero] at htr
  norm_num at htr

/-- A concrete nondegenerate `su(2)` witness through the genuine Clifford doubled twirl whose
state slot is a genuine density matrix. -/
theorem su2_variance_mixed_state_witness :
    ∃ ρ O : Matrix (Fin 2) (Fin 2) ℂ, ∃ M : RagoneSecondMoment su2HermBasis ρ O,
      ρᴴ = ρ ∧ Oᴴ = O ∧ ρ.trace = 1 ∧ Matrix.PosSemidef ρ ∧ ρ ≠ O ∧
        su2HermBasis.gPurity ρ = (1 / 4 : ℂ) ∧
        su2HermBasis.gPurity O = (1 / 9 : ℂ) ∧
        (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
          ∑ g, (cliffordLoss ρ O g -
            ((Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ h, cliffordLoss ρ O h)) ^ 2 =
          (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, (cliffordLoss ρ O g) ^ 2 ∧
        (M.variance : ℂ) =
          (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, (cliffordLoss ρ O g) ^ 2 ∧
        (M.variance : ℂ) = su2HermBasis.gPurity ρ * su2HermBasis.gPurity O / (3 : ℂ) ∧
        (M.variance : ℂ) = (1 / 108 : ℂ) ∧
        (M.variance : ℂ) ≠ (1 / 3 : ℂ) := by
  refine ⟨su2MixedStateRho, su2NondegenerateO, su2MixedStateSecondMoment, ?_⟩
  exact ⟨su2MixedStateRho_isHermitian, su2NondegenerateO_isHermitian,
    su2MixedStateRho_trace, su2MixedStateRho_posSemidef, su2MixedStateRho_ne_O,
    su2MixedStateRho_gPurity, su2NondegenerateO_gPurity,
    su2MixedStateSecondMoment_centeredLoss_eq_uncenteredLoss,
    su2MixedStateSecondMoment_variance_eq_uncenteredLoss,
    su2MixedStateSecondMoment_variance_eq_gPurity,
    su2MixedStateSecondMoment_variance_eq,
    by rw [su2MixedStateSecondMoment_variance_eq]; norm_num⟩

/-! ## The central double cover -/

/-- The nontrivial scalar element in the strict lift. -/
def binaryOctahedralNegOne : BinaryOctahedral := .axis true 0

@[simp]
theorem binaryOctahedralQuaternion_negOne :
    binaryOctahedralQuaternion binaryOctahedralNegOne = -1 := by
  apply exact_add_self_injective
  rw [← octToExact_octNumerator]
  change octToExact (octNumerator (.axis true 0)) = (-1 : ExactQuaternion) + (-1)
  apply QuaternionAlgebra.ext <;>
    simp only [octNumerator, quaternionBasisZ, Matrix.cons_val_zero, octToExact_re, octToExact_imI,
      octToExact_imJ, octToExact_imK, Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
      Quaternion.imK_neg, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, if_true, smul_eq_mul] <;>
    norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive center testing over numerator pairs needs this local reduction budget.
/-- The integer numerators commuting with all numerators are exactly the two scalar lifts. -/
private theorem octNumerator_center :
    ∀ a, (∀ b, octNumerator a * octNumerator b = octNumerator b * octNumerator a) →
      a = 1 ∨ a = binaryOctahedralNegOne := by decide

private theorem binaryOctahedral_exact_center (a : BinaryOctahedral)
    (h : ∀ b, binaryOctahedralQuaternion b * binaryOctahedralQuaternion a =
      binaryOctahedralQuaternion a * binaryOctahedralQuaternion b) :
    a = 1 ∨ a = binaryOctahedralNegOne := by
  apply octNumerator_center a
  intro b
  apply octToExact_injective
  rw [map_mul, map_mul, octToExact_octNumerator, octToExact_octNumerator]
  have hcomm : binaryOctahedralQuaternion a * binaryOctahedralQuaternion b =
      binaryOctahedralQuaternion b * binaryOctahedralQuaternion a := (h b).symm
  -- (a+a)(b+b) = (b+b)(a+a) given a*b = b*a
  linear_combination (norm := noncomm_ring) (4 : ExactQuaternion) * hcomm

theorem binaryOctahedral_mem_center_iff (a : BinaryOctahedral) :
    a ∈ Subgroup.center BinaryOctahedral ↔
      a = 1 ∨ a = binaryOctahedralNegOne := by
  constructor
  · intro ha
    apply binaryOctahedral_exact_center a
    intro b
    rw [← binaryOctahedralQuaternion_mul, ← binaryOctahedralQuaternion_mul]
    exact congrArg binaryOctahedralQuaternion (Submonoid.mem_center_iff.mp ha b)
  · rintro (rfl | rfl)
    · exact (Subgroup.center BinaryOctahedral).one_mem
    · change binaryOctahedralNegOne ∈ Set.center BinaryOctahedral
      rw [Semigroup.mem_center_iff]
      intro b
      apply binaryOctahedralQuaternion_injective
      simp only [binaryOctahedralQuaternion_mul, binaryOctahedralQuaternion_negOne]
      exact (Quaternion.coe_commutes (-1 : SqrtTwoRat)
        (binaryOctahedralQuaternion b)).symm

private theorem binaryOctahedralNegOne_ne_one : binaryOctahedralNegOne ≠ (1 : BinaryOctahedral) :=
  by decide

/-- The center consists exactly of the two scalar lifts. -/
def binaryOctahedralCenterEquivBool : Subgroup.center BinaryOctahedral ≃ Bool where
  toFun z := z.1 ≠ 1
  invFun
    | false => ⟨1, (Subgroup.center BinaryOctahedral).one_mem⟩
    | true => ⟨binaryOctahedralNegOne,
        binaryOctahedral_mem_center_iff binaryOctahedralNegOne |>.mpr (Or.inr rfl)⟩
  left_inv z := by
    rcases binaryOctahedral_mem_center_iff z.1 |>.mp z.2 with h | h
    · apply Subtype.ext
      simp [h]
    · apply Subtype.ext
      simp [h, binaryOctahedralNegOne_ne_one]
  right_inv b := by
    cases b <;> simp [binaryOctahedralNegOne_ne_one]

/-- The strict binary-octahedral lift has a center of order two. -/
theorem binaryOctahedral_center_card :
    Fintype.card (Subgroup.center BinaryOctahedral) = 2 := by
  rw [Fintype.card_congr binaryOctahedralCenterEquivBool]
  decide

/-- Quotienting the strict lift by its scalar center gives the `24` projective Clifford gates. -/
theorem projectiveQubitClifford_card :
    Fintype.card (BinaryOctahedral ⧸ Subgroup.center BinaryOctahedral) = 24 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center BinaryOctahedral)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    binaryOctahedral_card, binaryOctahedral_center_card] at h
  omega

end QuantumAlg.QubitTwoDesign
