/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.State.Basic
public import QuantumAlg.Core.Base.State.Normalized
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Real.Sqrt
import all QuantumAlg.Core.Base.Gate.Unitary
import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Modular-multiplication eigenstructure

This module isolates the cycle and residue-register eigenstructure used by
order finding.  It deliberately has no dependency on modular-arithmetic
circuits, the integrated order-finding algorithm, or its probability and
resource analyses.  The public endpoint is the source-facing residue-space
statement from Shor's modular-multiplication eigenstate construction
[CEMM98, cemm6.tex:709-795].

The modular-multiplication carrier is a metadata-free `UnitaryOperator`. The
public OTHER-class theorem stays at the raw-vector level, so physical placement
and implementation accounting do not become new statement binders.
-/

section

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace OrderFinding

/-! ## Cycle Fourier convention -/

/-- Sign convention for Fourier-style phases in modular-multiplication
eigenstates. -/
inductive FourierPhaseSign where
  | positive
  | negative
deriving DecidableEq

/-- The selected modular-eigenstate phase, index, and normalization
convention. -/
structure ModularEigenstateConvention where
  /-- Sign of the modular-multiplication eigenvalue phase. -/
  eigenvalueSign : FourierPhaseSign
  /-- Sign of the orbit coefficients' Fourier phase. -/
  coefficientSign : FourierPhaseSign
  /-- First exponent used to enumerate the modular orbit. -/
  indexStart : ℕ
  /-- Whether the orbit sum is normalized by the square root of its order. -/
  normalizedBySqrtOrder : Bool
deriving DecidableEq

/-- Positive eigenvalue phase, negative coefficient phase, zero-based orbit,
and square-root normalization. -/
def modularEigenstateConvention : ModularEigenstateConvention where
  eigenvalueSign := .positive
  coefficientSign := .negative
  indexStart := 0
  normalizedBySqrtOrder := true

/-- Eigenvalue phase for the `k`-th modular-multiplication eigenstate. -/
public def modularEigenphase (r k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * ((k : ℝ) / r) * Complex.I)

/-- Coefficient of the `j`-th orbit basis state in the `k`-th
modular-multiplication eigenstate. -/
def modularEigenCoefficient (r k j : ℕ) : ℂ :=
  (Real.sqrt (r : ℝ))⁻¹ *
    Complex.exp (-(2 * Real.pi * ((k : ℝ) * j / r)) * Complex.I)

/-- Coordinate register for one length-`r` modular-multiplication cycle. -/
public abbrev cycleRegister (r : ℕ) : Register where
  Index := Fin r
  fintype := inferInstance
  decEq := inferInstance

/-- Raw Fourier eigenvector over the coordinate labels of a length-`r`
cycle. -/
def cycleEigenstateVec (r k : ℕ) : HilbertVector (cycleRegister r) :=
  WithLp.toLp 2 fun j : Fin r => modularEigenCoefficient r k j.val

@[simp]
theorem modularEigenphase_eq (r k : ℕ) :
    modularEigenphase r k =
      Complex.exp (2 * Real.pi * ((k : ℝ) / r) * Complex.I) :=
  rfl

@[simp]
theorem modularEigenCoefficient_eq (r k j : ℕ) :
    modularEigenCoefficient r k j =
      (Real.sqrt (r : ℝ))⁻¹ *
        Complex.exp (-(2 * Real.pi * ((k : ℝ) * j / r)) * Complex.I) :=
  rfl

@[simp]
theorem cycleEigenstateVec_apply (r k : ℕ) (j : Fin r) :
    cycleEigenstateVec r k j = modularEigenCoefficient r k j.val :=
  rfl

/-- The Fourier eigenvector is normalized whenever the cycle length is
positive. The raw vector remains total at `r = 0`; this theorem is the
certification boundary for physical eigenstates. -/
theorem cycleEigenstateVec_norm_eq_one (r k : ℕ) (hr : 0 < r) :
    ‖cycleEigenstateVec r k‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hcoefficient (j : Fin r) :
      ‖modularEigenCoefficient r k j.val‖ ^ 2 = (r : ℝ)⁻¹ := by
    rw [modularEigenCoefficient, norm_mul]
    have hexp :
        ‖Complex.exp
          (-(2 * Real.pi * ((k : ℝ) * j.val / r)) * Complex.I)‖ = 1 := by
      simpa using Complex.norm_exp_ofReal_mul_I
        (-(2 * Real.pi * ((k : ℝ) * j.val / r)))
    have hnorm :
        ‖(((Real.sqrt (r : ℝ))⁻¹ : ℝ) : ℂ)‖ =
          (Real.sqrt (r : ℝ))⁻¹ := by
      rw [Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    rw [hexp, mul_one, hnorm, inv_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (r : ℝ))]
  have hsum :
      ∑ j : Fin r, ‖cycleEigenstateVec r k j‖ ^ 2 = 1 := by
    simp_rw [cycleEigenstateVec_apply, hcoefficient]
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_inv_cancel₀ hrR]
  rw [hsum, Real.sqrt_one]

/-- The conditional intrinsic carrier for a Fourier eigenstate. -/
public noncomputable def cycleEigenstate (r k : ℕ) (hr : 0 < r) :
    NormalizedVector (cycleRegister r) :=
  NormalizedVector.ofVector (cycleEigenstateVec r k)
    (cycleEigenstateVec_norm_eq_one r k hr)

@[simp]
theorem cycleEigenstate_coe (r k : ℕ) (hr : 0 < r) :
    (cycleEigenstate r k hr : HilbertVector (cycleRegister r)) =
      cycleEigenstateVec r k :=
  rfl

/-- Previous coordinate in a finite cycle. -/
def cyclePred (r : ℕ) (j : Fin r) : Fin r :=
  if h : j.val = 0 then
    ⟨r - 1, by
      have hr : 0 < r := by simpa [h] using j.isLt
      exact Nat.pred_lt hr.ne'⟩
  else
    ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩

theorem cyclePred_val (r : ℕ) (j : Fin r) :
    (cyclePred r j).val = if j.val = 0 then r - 1 else j.val - 1 := by
  unfold cyclePred
  split <;> rfl

@[simp]
theorem cyclePred_val_zero {r : ℕ} (j : Fin r) (h : j.val = 0) :
    (cyclePred r j).val = r - 1 := by
  rw [cyclePred_val, if_pos h]

@[simp]
theorem cyclePred_val_nonzero {r : ℕ} (j : Fin r) (h : j.val ≠ 0) :
    (cyclePred r j).val = j.val - 1 := by
  rw [cyclePred_val, if_neg h]

/-- Next coordinate in a finite cycle. -/
public def cycleSucc (r : ℕ) (j : Fin r) : Fin r :=
  if h : j.val + 1 < r then
    ⟨j.val + 1, h⟩
  else
    ⟨0, lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩

theorem cycleSucc_val (r : ℕ) (j : Fin r) :
    (cycleSucc r j).val = if j.val + 1 < r then j.val + 1 else 0 := by
  unfold cycleSucc
  split <;> rfl

@[simp]
theorem cycleSucc_val_of_lt {r : ℕ} (j : Fin r) (h : j.val + 1 < r) :
    (cycleSucc r j).val = j.val + 1 := by
  rw [cycleSucc_val, if_pos h]

@[simp]
theorem cycleSucc_val_of_wrap {r : ℕ} (j : Fin r) (h : ¬ j.val + 1 < r) :
    (cycleSucc r j).val = 0 := by
  rw [cycleSucc_val, if_neg h]

/-- Moving to the predecessor and then forward returns the original cycle
coordinate. -/
theorem cycleSucc_cyclePred {r : ℕ} (j : Fin r) :
    cycleSucc r (cyclePred r j) = j := by
  apply Fin.ext
  by_cases hzero : j.val = 0
  · rw [cycleSucc_val, cyclePred_val_zero j hzero, hzero]
    split <;> omega
  · rw [cycleSucc_val, cyclePred_val_nonzero j hzero]
    have hlt : j.val - 1 + 1 < r := by
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero hzero
      omega
    rw [if_pos hlt]
    omega

/-- Raw action of the forward cyclic basis shift on coordinate vectors. -/
def cycleForwardShiftVec (r : ℕ) (ψ : HilbertVector (cycleRegister r)) :
    HilbertVector (cycleRegister r) :=
  WithLp.toLp 2 fun j : Fin r => ψ (cyclePred r j)

@[simp]
theorem cycleForwardShiftVec_apply (r : ℕ) (ψ : HilbertVector (cycleRegister r))
    (j : Fin r) :
    cycleForwardShiftVec r ψ j = ψ (cyclePred r j) :=
  rfl

theorem modularEigenCoefficient_cyclePred (r k : ℕ) (hr : 0 < r) (j : Fin r) :
    modularEigenCoefficient r k (cyclePred r j).val =
      modularEigenphase r k * modularEigenCoefficient r k j.val := by
  rw [modularEigenCoefficient, modularEigenCoefficient, modularEigenphase]
  by_cases hzero : j.val = 0
  · rw [cyclePred_val_zero j hzero, hzero]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hangle :
        -(2 * (Real.pi : ℂ) * ((k : ℂ) * ((r : ℂ) - 1) / (r : ℂ)) * Complex.I) =
          2 * (Real.pi : ℂ) * ((k : ℂ) / (r : ℂ)) * Complex.I +
            -(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp [hrC]
      ring
    have hperiod :
        Complex.exp (-(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      simpa using Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
    rw [Nat.cast_sub (Nat.succ_le_of_lt hr)]
    norm_num
    rw [hangle, Complex.exp_add, hperiod, mul_one]
    ring
  · rw [cyclePred_val_nonzero j hzero]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero hzero
    have hangle :
        -(2 * (Real.pi : ℂ) * ((k : ℂ) * ((j.val : ℂ) - 1) / (r : ℂ)) * Complex.I) =
          2 * (Real.pi : ℂ) * ((k : ℂ) / (r : ℂ)) * Complex.I +
            -(2 * (Real.pi : ℂ) * ((k : ℂ) * (j.val : ℂ) / (r : ℂ)) * Complex.I) := by
      field_simp [hrC]
      ring
    rw [Nat.cast_sub (Nat.succ_le_of_lt hjpos)]
    norm_num
    rw [hangle, Complex.exp_add]
    ring

theorem cycleForwardShiftVec_eigenstateVec (r k : ℕ) (hr : 0 < r) :
    cycleForwardShiftVec r (cycleEigenstateVec r k) =
      modularEigenphase r k • cycleEigenstateVec r k := by
  apply WithLp.ofLp_injective
  funext j
  change cycleForwardShiftVec r (cycleEigenstateVec r k) j =
    (modularEigenphase r k • cycleEigenstateVec r k) j
  rw [cycleForwardShiftVec_apply, PiLp.smul_apply, cycleEigenstateVec_apply,
    cycleEigenstateVec_apply, smul_eq_mul]
  exact modularEigenCoefficient_cyclePred r k hr j

/-! ## Finite Fourier decomposition -/

/-- Positive phase root used for finite Fourier orthogonality. -/
def cyclePhaseRoot (r : ℕ) (j : Fin r) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (r : ℂ))

theorem cyclePhaseRoot_pow_card (r : ℕ) (hr : 0 < r) (j : Fin r) :
    cyclePhaseRoot r j ^ r = 1 := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cyclePhaseRoot, ← Complex.exp_nat_mul]
  have hangle :
      (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (r : ℂ)) =
        (j.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp [hrC]
  rw [hangle]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    Complex.exp_nat_mul_two_pi_mul_I j.val

theorem cyclePhaseRoot_ne_one_of_nonzero (r : ℕ) (hr : 0 < r)
    (j : Fin r) (hj : j.val ≠ 0) :
    cyclePhaseRoot r j ≠ 1 := by
  intro hroot
  have hdiv : r ∣ j.val := by
    have hiff := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
      (k := j.val) (N := r) hr.ne'
    exact hiff.mp (by
      simpa [cyclePhaseRoot, mul_assoc, mul_comm, mul_left_comm] using hroot)
  rcases hdiv with ⟨m, hm⟩
  have hm0 : m = 0 := by
    by_contra hmne
    have hmpos : 0 < m := Nat.pos_of_ne_zero hmne
    have : r ≤ j.val := by
      rw [hm]
      exact Nat.le_mul_of_pos_right r hmpos
    exact not_le_of_gt j.isLt this
  exact hj (by simp [hm, hm0])

theorem cyclePhaseRoot_inv_ne_one_of_nonzero (r : ℕ) (hr : 0 < r)
    (j : Fin r) (hj : j.val ≠ 0) :
    (cyclePhaseRoot r j)⁻¹ ≠ 1 := by
  intro hinv
  exact cyclePhaseRoot_ne_one_of_nonzero r hr j hj (inv_eq_one.mp hinv)

theorem cyclePhaseRoot_inv_pow_card (r : ℕ) (hr : 0 < r) (j : Fin r) :
    (cyclePhaseRoot r j)⁻¹ ^ r = 1 := by
  rw [inv_pow, cyclePhaseRoot_pow_card r hr j, inv_one]

theorem cyclePhaseRoot_inv_pow_eq_coefficient_phase
    (r : ℕ) (_hr : 0 < r) (j k : Fin r) :
    (cyclePhaseRoot r j)⁻¹ ^ k.val =
      Complex.exp (-(2 * Real.pi * ((k.val : ℝ) * j.val / r)) * Complex.I) := by
  rw [cyclePhaseRoot, ← Complex.exp_neg, ← Complex.exp_nat_mul]
  have hangle :
      (k.val : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (r : ℂ))) =
        -(2 * (Real.pi : ℂ) * ((k.val : ℂ) * (j.val : ℂ) / (r : ℂ)) * Complex.I) := by
    ring
  rw [hangle]
  congr 1
  push_cast
  ring_nf

theorem sum_cyclePhaseRoot_inv_pow (r : ℕ) (hr : 0 < r) (j : Fin r) :
    ∑ k : Fin r, (cyclePhaseRoot r j)⁻¹ ^ k.val =
      if j.val = 0 then (r : ℂ) else 0 := by
  by_cases hj : j.val = 0
  · rw [if_pos hj]
    have hterm : ∀ k : Fin r, (cyclePhaseRoot r j)⁻¹ ^ k.val = (1 : ℂ) := by
      intro k
      rw [cyclePhaseRoot, hj]
      norm_num
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  · rw [if_neg hj]
    rw [Fin.sum_univ_eq_sum_range fun k => (cyclePhaseRoot r j)⁻¹ ^ k]
    have hne : (cyclePhaseRoot r j)⁻¹ ≠ 1 :=
      cyclePhaseRoot_inv_ne_one_of_nonzero r hr j hj
    have hpow : (cyclePhaseRoot r j)⁻¹ ^ r = 1 :=
      cyclePhaseRoot_inv_pow_card r hr j
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

theorem sum_modularEigenCoefficient_over_modes (r : ℕ) (hr : 0 < r) (j : Fin r) :
    ∑ k : Fin r, modularEigenCoefficient r k.val j.val =
      if j.val = 0 then (Real.sqrt (r : ℝ) : ℂ) else 0 := by
  calc
    ∑ k : Fin r, modularEigenCoefficient r k.val j.val =
        (Real.sqrt (r : ℝ))⁻¹ *
          ∑ k : Fin r, (cyclePhaseRoot r j)⁻¹ ^ k.val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [cyclePhaseRoot_inv_pow_eq_coefficient_phase r hr j k,
        modularEigenCoefficient]
    _ = if j.val = 0 then (Real.sqrt (r : ℝ) : ℂ) else 0 := by
      rw [sum_cyclePhaseRoot_inv_pow r hr j]
      by_cases hj : j.val = 0
      · simp only [hj, if_true]
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
        congr 1
        rw [inv_mul_eq_div,
          div_eq_iff (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr))]
        exact (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (r : ℝ))).symm
      · rw [if_neg hj, if_neg hj, mul_zero]

/-- The first cycle basis state is the uniform average of all Fourier
eigenvectors. -/
theorem cycleBasisZero_eq_eigenstate_average (r : ℕ) (hr : 0 < r) :
    (NormalizedVector.ket (R := cycleRegister r) ⟨0, hr⟩ : HilbertVector (cycleRegister r)) =
      (Real.sqrt (r : ℝ))⁻¹ • ∑ k : Fin r, cycleEigenstateVec r k := by
  apply WithLp.ofLp_injective
  funext (j : Fin r)
  rw [show (((Real.sqrt (r : ℝ))⁻¹ • ∑ k : Fin r, cycleEigenstateVec r k) :
      HilbertVector (cycleRegister r)).ofLp j =
        (Real.sqrt (r : ℝ))⁻¹ * (∑ k : Fin r, cycleEigenstateVec r k).ofLp j from rfl]
  rw [show (∑ k : Fin r, cycleEigenstateVec r k).ofLp j =
      ∑ k : Fin r, (cycleEigenstateVec r k).ofLp j by simp]
  change (NormalizedVector.ket (R := cycleRegister r) (⟨0, hr⟩ : Fin r) :
      HilbertVector (cycleRegister r)) (j : Fin r) =
    (Real.sqrt (r : ℝ))⁻¹ *
      ∑ k : Fin r, modularEigenCoefficient r k.val j.val
  rw [sum_modularEigenCoefficient_over_modes r hr j]
  by_cases hj : j.val = 0
  · have hj_eq : j = ⟨0, hr⟩ := Fin.ext hj
    rw [if_pos hj, hj_eq, NormalizedVector.ket_apply, if_pos rfl]
    rw [← Complex.ofReal_mul]
    have hsqrt_ne : Real.sqrt (r : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr)
    rw [inv_mul_cancel₀ hsqrt_ne]
    norm_num
  · have hj_ne : j ≠ ⟨0, hr⟩ := fun h => hj (Fin.ext_iff.mp h)
    rw [if_neg hj, NormalizedVector.ket_apply, if_neg hj_ne, mul_zero]

/-! ## Residue-register realization -/

/-- The source-facing `N`-dimensional residue register. -/
@[implicit_reducible, expose]
public noncomputable def residueRegister (N : ℕ) [NeZero N] : Register :=
  { Index := ZMod N
    fintype := inferInstance
    decEq := inferInstance }

/-- Multiplication by a unit on the full residue ring. -/
def residueMultiplicationPerm {N : ℕ} (u : (ZMod N)ˣ) : Equiv.Perm (ZMod N) where
  toFun := fun x => (u : ZMod N) * x
  invFun := fun x => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x
  left_inv x := by simp
  right_inv x := by simp

@[simp]
theorem residueMultiplicationPerm_apply {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    residueMultiplicationPerm u x = (u : ZMod N) * x :=
  rfl

@[simp]
theorem residueMultiplicationPerm_symm_apply {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    (residueMultiplicationPerm u).symm x =
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x :=
  rfl

/-- The metadata-free residue-register modular-multiplication operator. The inverse
permutation is supplied because `UnitaryOperator.ofPerm sigma` sends `|x>` to
`|sigma⁻¹ x>`. -/
public noncomputable def residueMultiplicationOp {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) : UnitaryOperator (residueRegister N) :=
  UnitaryOperator.ofPerm (residueMultiplicationPerm u).symm

/-- Intrinsically normalized basis action of the residue multiplication
operator. -/
theorem residueMultiplicationOp_apply_ket {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (x : ZMod N) :
    (residueMultiplicationOp u).apply
        (NormalizedVector.ket (R := residueRegister N) x) =
      NormalizedVector.ket (R := residueRegister N) ((u : ZMod N) * x) := by
  rw [residueMultiplicationOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

theorem residueMultiplicationOp_applyVec {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (ψ : HilbertVector (residueRegister N)) (x : ZMod N) :
    (residueMultiplicationOp u).applyVec ψ x =
      ψ (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x) := by
  rw [residueMultiplicationOp, UnitaryOperator.ofPerm_applyVec]
  rfl

/-- Orbit label `u^j` in the public residue register. -/
public def residueOrbitLabel {N r : ℕ} (u : (ZMod N)ˣ) (j : Fin r) : ZMod N :=
  (u ^ j.val : (ZMod N)ˣ)

/-- Residue-register orbit labels are injective over one order cycle. -/
theorem residueOrbitLabel_injective_of_order {N r : ℕ}
    (u : (ZMod N)ˣ) (horder : orderOf u = r) :
    Function.Injective (residueOrbitLabel (N := N) u : Fin r → ZMod N) := by
  intro i j h
  have hunit : u ^ i.val = u ^ j.val := by
    ext
    exact h
  have hmod : i.val ≡ j.val [MOD orderOf u] := by
    exact pow_eq_pow_iff_modEq.mp hunit
  rw [horder] at hmod
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
  exact Fin.ext hmod

/-- Linear embedding of a cycle-coordinate vector into the public residue
register along the generated orbit labels. -/
noncomputable def residueOrbitLiftVec {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (ψ : HilbertVector (cycleRegister r)) :
    HilbertVector (residueRegister N) :=
  WithLp.toLp 2 fun x : (residueRegister N).Index =>
    ∑ j : Fin r,
      ψ j * if x = residueOrbitLabel u j then (1 : ℂ) else 0

/-- On generated residue-orbit labels, the residue lift recovers the original
cycle-coordinate amplitude. -/
theorem residueOrbitLiftVec_apply_orbit {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (horder : orderOf u = r)
    (ψ : HilbertVector (cycleRegister r)) (j : Fin r) :
    residueOrbitLiftVec u ψ (residueOrbitLabel u j) = ψ j := by
  classical
  unfold residueOrbitLiftVec
  change
    (∑ k : Fin r,
      ψ k *
        (if residueOrbitLabel u j = residueOrbitLabel u k then (1 : ℂ) else 0)) =
      ψ j
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro k _ hk
    have hlabel : residueOrbitLabel u j ≠ residueOrbitLabel u k := by
      intro h
      exact hk ((residueOrbitLabel_injective_of_order u horder) h.symm)
    simp [hlabel]

/-- The residue lift is zero away from the generated residue orbit. -/
theorem residueOrbitLiftVec_apply_not_mem_orbit {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (ψ : HilbertVector (cycleRegister r)) {x : ZMod N}
    (hnot :
      x ∉ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)) :
    residueOrbitLiftVec u ψ x = 0 := by
  classical
  unfold residueOrbitLiftVec
  change
    (∑ j : Fin r,
      ψ j * if x = residueOrbitLabel u j then (1 : ℂ) else 0) = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  have hne : x ≠ residueOrbitLabel u j := by
    intro h
    exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩)
  simp [hne]

/-- Lifting along one injectively labelled order cycle preserves the Hilbert
space norm. -/
theorem residueOrbitLiftVec_norm_eq {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (horder : orderOf u = r)
    (ψ : HilbertVector (cycleRegister r)) :
    ‖residueOrbitLiftVec u ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    ∑ x : ZMod N, ‖residueOrbitLiftVec u ψ x‖ ^ 2 =
        ((Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)).sum
          (fun x => ‖residueOrbitLiftVec u ψ x‖ ^ 2) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro x _hx hnot
      rw [residueOrbitLiftVec_apply_not_mem_orbit u ψ hnot]
      norm_num
    _ = ∑ j : Fin r, ‖ψ j‖ ^ 2 := by
      rw [Finset.sum_image
        (residueOrbitLabel_injective_of_order u horder).injOn]
      refine Finset.sum_congr rfl fun j _hj => ?_
      rw [residueOrbitLiftVec_apply_orbit u horder]

/-- The intrinsic normalized residue-register eigenstate. Positivity and the
exact order witness are explicit because the raw formula is total outside the
physical domain. -/
public noncomputable def residueEigenstate {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (k : ℕ)
    (hr : 0 < r) (horder : orderOf u = r) :
    NormalizedVector (residueRegister N) :=
  NormalizedVector.ofVector
    (residueOrbitLiftVec u (cycleEigenstateVec r k))
    ((residueOrbitLiftVec_norm_eq u horder _).trans
      (cycleEigenstateVec_norm_eq_one r k hr))

@[simp]
theorem residueEigenstate_coe {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (k : ℕ)
    (hr : 0 < r) (horder : orderOf u = r) :
    (residueEigenstate u k hr horder : HilbertVector (residueRegister N)) =
      residueOrbitLiftVec u (cycleEigenstateVec r k) :=
  rfl

/-- Multiplication by the generating unit advances the residue-orbit label by
one cycle coordinate. -/
theorem residueMultiplication_residueOrbitLabel_cycleSucc {N r : ℕ}
    (u : (ZMod N)ˣ) (horder : orderOf u = r) (j : Fin r) :
    (u : ZMod N) * residueOrbitLabel u j =
      residueOrbitLabel u (cycleSucc r j) := by
  unfold residueOrbitLabel
  change ((u * u ^ j.val : (ZMod N)ˣ) : ZMod N) =
    ((u ^ (cycleSucc r j).val : (ZMod N)ˣ) : ZMod N)
  apply congrArg (fun v : (ZMod N)ˣ => (v : ZMod N))
  by_cases hlt : j.val + 1 < r
  · rw [cycleSucc_val_of_lt j hlt]
    rw [pow_succ']
  · rw [cycleSucc_val_of_wrap j hlt]
    have hsucc : j.val + 1 = r := by omega
    rw [← pow_succ', hsucc, ← horder, pow_orderOf_eq_one]
    simp

/-- Multiplication by the inverse unit preserves the complement of the
residue orbit. -/
theorem residueMultiplication_inv_notMem_residueOrbitLabel_image_of_notMem
    {N r : ℕ} (u : (ZMod N)ˣ) (horder : orderOf u = r) {x : ZMod N}
    (hnot : x ∉ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)) :
    ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x ∉
      (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨j, _hj, hj⟩
  have hx : x = residueOrbitLabel u (cycleSucc r j) := by
    calc
      x = (u : ZMod N) * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x) := by
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel]
        simp
      _ = (u : ZMod N) * residueOrbitLabel u j := by rw [← hj]
      _ = residueOrbitLabel u (cycleSucc r j) :=
        residueMultiplication_residueOrbitLabel_cycleSucc u horder j
  exact hnot (Finset.mem_image.mpr ⟨cycleSucc r j, Finset.mem_univ _, hx.symm⟩)

/-- Multiplication by the inverse generating unit moves one step backward on
the public residue orbit. -/
theorem residueMultiplication_inv_residueOrbitLabel_cyclePred {N r : ℕ}
    (u : (ZMod N)ˣ) (horder : orderOf u = r) (j : Fin r) :
    ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * residueOrbitLabel u j =
      residueOrbitLabel u (cyclePred r j) := by
  have hfwd :
      (u : ZMod N) * residueOrbitLabel u (cyclePred r j) =
        residueOrbitLabel u j := by
    rw [residueMultiplication_residueOrbitLabel_cycleSucc u horder,
      cycleSucc_cyclePred]
  calc
    ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * residueOrbitLabel u j =
        ((u⁻¹ : (ZMod N)ˣ) : ZMod N) *
          ((u : ZMod N) * residueOrbitLabel u (cyclePred r j)) := by
            rw [hfwd]
    _ = residueOrbitLabel u (cyclePred r j) := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel]
      simp

/-- Orbit-local residue-register eigenvalue calculation. -/
theorem residueMultiplicationOp_applyVec_residueOrbitLiftEigenstateVec_orbit
    {N r k : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (hr : 0 < r) (horder : orderOf u = r) (j : Fin r) :
    (residueMultiplicationOp u).applyVec
        (residueOrbitLiftVec u (cycleEigenstateVec r k))
        (residueOrbitLabel u j) =
      (modularEigenphase r k •
        residueOrbitLiftVec u (cycleEigenstateVec r k))
        (residueOrbitLabel u j) := by
  rw [residueMultiplicationOp_applyVec]
  rw [residueMultiplication_inv_residueOrbitLabel_cyclePred u horder]
  rw [residueOrbitLiftVec_apply_orbit u horder]
  change modularEigenCoefficient r k (cyclePred r j).val =
    modularEigenphase r k *
      residueOrbitLiftVec u (cycleEigenstateVec r k) (residueOrbitLabel u j)
  rw [residueOrbitLiftVec_apply_orbit u horder]
  change modularEigenCoefficient r k (cyclePred r j).val =
    modularEigenphase r k * modularEigenCoefficient r k j.val
  exact modularEigenCoefficient_cyclePred r k hr j

/-- Full residue-register lifted eigenvector relation. -/
theorem residueMultiplicationOp_applyVec_residueOrbitLiftEigenstateVec
    {N r k : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (hr : 0 < r) (horder : orderOf u = r) :
    (residueMultiplicationOp u).applyVec
        (residueOrbitLiftVec u (cycleEigenstateVec r k)) =
      modularEigenphase r k •
        residueOrbitLiftVec u (cycleEigenstateVec r k) := by
  apply WithLp.ofLp_injective
  funext (x : ZMod N)
  by_cases hmem :
      (x : ZMod N) ∈ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)
  · rcases Finset.mem_image.mp hmem with ⟨j, _hj, hx⟩
    subst hx
    exact residueMultiplicationOp_applyVec_residueOrbitLiftEigenstateVec_orbit
      u hr horder j
  · rw [residueMultiplicationOp_applyVec]
    have hpre :
        ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (x : ZMod N) ∉
          (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u) :=
      residueMultiplication_inv_notMem_residueOrbitLabel_image_of_notMem
        u horder hmem
    rw [residueOrbitLiftVec_apply_not_mem_orbit u _ hpre]
    change 0 =
      modularEigenphase r k *
        residueOrbitLiftVec u (cycleEigenstateVec r k) (x : ZMod N)
    rw [residueOrbitLiftVec_apply_not_mem_orbit u _ hmem]
    simp

/-- In the public residue register, `|1>` is the uniform average of the lifted
Fourier eigenvectors. -/
theorem residueBasisOne_eq_lifted_eigenstate_average {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (hr : 0 < r) (horder : orderOf u = r) :
    (NormalizedVector.ket (R := residueRegister N) (1 : ZMod N) :
      HilbertVector (residueRegister N)) =
      (Real.sqrt (r : ℝ))⁻¹ •
        ∑ k : Fin r, residueOrbitLiftVec u (cycleEigenstateVec r k) := by
  apply WithLp.ofLp_injective
  funext x
  by_cases hmem :
      (x : ZMod N) ∈ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)
  · rcases Finset.mem_image.mp hmem with ⟨j, _hj, hx⟩
    subst hx
    rw [show (((Real.sqrt (r : ℝ))⁻¹ •
        ∑ k : Fin r, residueOrbitLiftVec u (cycleEigenstateVec r k)) :
          HilbertVector (residueRegister N)).ofLp (residueOrbitLabel u j) =
        (Real.sqrt (r : ℝ))⁻¹ *
          (∑ k : Fin r,
            residueOrbitLiftVec u (cycleEigenstateVec r k)
              (residueOrbitLabel u j)) by simp]
    rw [show (∑ k : Fin r,
        residueOrbitLiftVec u (cycleEigenstateVec r k)
          (residueOrbitLabel u j)) =
        ∑ k : Fin r, cycleEigenstateVec r k j by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [residueOrbitLiftVec_apply_orbit u horder]]
    change (NormalizedVector.ket (R := residueRegister N) (1 : ZMod N))
        (residueOrbitLabel u j) =
      (Real.sqrt (r : ℝ))⁻¹ *
        ∑ k : Fin r, modularEigenCoefficient r k.val j.val
    rw [NormalizedVector.ket_apply, sum_modularEigenCoefficient_over_modes r hr j]
    change (if (residueOrbitLabel u j : ZMod N) = (1 : ZMod N) then (1 : ℂ) else 0) =
      (Real.sqrt (r : ℝ))⁻¹ *
        if j.val = 0 then (Real.sqrt (r : ℝ) : ℂ) else 0
    by_cases hj : j.val = 0
    · have hj_eq : j = ⟨0, hr⟩ := Fin.ext hj
      have hlabel : residueOrbitLabel u j = (1 : ZMod N) := by
        rw [hj_eq]
        simp [residueOrbitLabel]
      rw [if_pos hlabel, if_pos hj]
      rw [← Complex.ofReal_mul]
      have hsqrt_ne : Real.sqrt (r : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr)
      rw [inv_mul_cancel₀ hsqrt_ne]
      norm_num
    · have hlabel : residueOrbitLabel u j ≠ (1 : ZMod N) := by
        intro h
        have hzero :
            residueOrbitLabel u (⟨0, hr⟩ : Fin r) = (1 : ZMod N) := by
          simp [residueOrbitLabel]
        have hsame :
            residueOrbitLabel u j =
              residueOrbitLabel u (⟨0, hr⟩ : Fin r) := by
          rw [h, hzero]
        have hj0 := (residueOrbitLabel_injective_of_order u horder) hsame
        exact hj (Fin.ext_iff.mp hj0)
      rw [if_neg hlabel, if_neg hj, mul_zero]
  · rw [NormalizedVector.ket_apply]
    have hx_ne : x ≠ (1 : ZMod N) := by
      intro hx
      apply hmem
      refine Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, ?_⟩
      change residueOrbitLabel u (⟨0, hr⟩ : Fin r) = (x : ZMod N)
      rw [hx]
      simp [residueOrbitLabel]
    rw [if_neg hx_ne]
    rw [show (((Real.sqrt (r : ℝ))⁻¹ •
        ∑ k : Fin r, residueOrbitLiftVec u (cycleEigenstateVec r k)) :
          HilbertVector (residueRegister N)).ofLp x =
        (Real.sqrt (r : ℝ))⁻¹ *
          (∑ k : Fin r,
            residueOrbitLiftVec u (cycleEigenstateVec r k) (x : ZMod N)) by simp]
    change 0 = (Real.sqrt (r : ℝ))⁻¹ *
      (∑ k : Fin r,
        residueOrbitLiftVec u (cycleEigenstateVec r k) (x : ZMod N))
    rw [Finset.sum_eq_zero]
    · simp
    · intro k _hk
      exact residueOrbitLiftVec_apply_not_mem_orbit u _ hmem

/-! ## Public OTHER-class endpoint -/

/-- Residue-register modular-multiplication eigenstructure matching the
accepted public theorem shape. -/
public structure ResidueRegisterEigenstructure {N : ℕ} [NeZero N]
    (a : ℕ) (ha : Nat.Coprime a N) (r : ℕ) : Prop where
  order_pos : 0 < r
  order_eq : orderOf (ZMod.unitOfCoprime a ha) = r
  basisAction :
    ∀ j : Fin r,
      (residueMultiplicationOp (ZMod.unitOfCoprime a ha)).apply
          (NormalizedVector.ket (R := residueRegister N)
            (residueOrbitLabel (ZMod.unitOfCoprime a ha) j)) =
        NormalizedVector.ket (R := residueRegister N)
          (residueOrbitLabel (ZMod.unitOfCoprime a ha) (cycleSucc r j))
  liftedEigenvectorRelation :
    ∀ k : ℕ,
      ((residueMultiplicationOp (ZMod.unitOfCoprime a ha)).apply
          (residueEigenstate (ZMod.unitOfCoprime a ha) k order_pos order_eq) :
            HilbertVector (residueRegister N)) =
        modularEigenphase r k •
          (residueEigenstate (ZMod.unitOfCoprime a ha) k order_pos order_eq :
            HilbertVector (residueRegister N))
  basisOneLabel_eq :
    residueOrbitLabel (ZMod.unitOfCoprime a ha) ⟨0, order_pos⟩ = (1 : ZMod N)
  residueBasisOneDecomposition :
    (NormalizedVector.ket (R := residueRegister N) (1 : ZMod N) :
      HilbertVector (residueRegister N)) =
      (Real.sqrt (r : ℝ))⁻¹ •
        ∑ mode : Fin r,
          (residueEigenstate (ZMod.unitOfCoprime a ha) mode order_pos order_eq :
            HilbertVector (residueRegister N))
  cycleBasisZeroDecomposition :
    (NormalizedVector.ket (R := cycleRegister r) ⟨0, order_pos⟩ :
      HilbertVector (cycleRegister r)) =
      (Real.sqrt (r : ℝ))⁻¹ •
        ∑ mode : Fin r,
          (cycleEigenstate r mode order_pos : HilbertVector (cycleRegister r))

/-- Construct the source-facing residue-register eigenstructure from
coprimality and the exact multiplicative order. -/
public theorem ResidueRegisterEigenstructure.main {N a r : ℕ} [NeZero N]
    (ha : Nat.Coprime a N) (hr : 0 < r)
    (horder : orderOf (ZMod.unitOfCoprime a ha) = r) :
    ResidueRegisterEigenstructure a ha r where
  order_pos := hr
  order_eq := horder
  basisAction := by
    intro j
    rw [residueMultiplicationOp_apply_ket]
    rw [residueMultiplication_residueOrbitLabel_cycleSucc
      (ZMod.unitOfCoprime a ha) horder]
  liftedEigenvectorRelation := by
    intro k
    simpa only [UnitaryOperator.apply_coe, residueEigenstate_coe] using
      residueMultiplicationOp_applyVec_residueOrbitLiftEigenstateVec
        (ZMod.unitOfCoprime a ha) hr horder
  basisOneLabel_eq := by
    simp [residueOrbitLabel]
  residueBasisOneDecomposition :=
    by
      simpa only [residueEigenstate_coe] using
        residueBasisOne_eq_lifted_eigenstate_average
          (ZMod.unitOfCoprime a ha) hr horder
  cycleBasisZeroDecomposition :=
    by
      simpa only [cycleEigenstate_coe] using
        cycleBasisZero_eq_eigenstate_average r hr

end OrderFinding
end
end QuantumAlg

end
