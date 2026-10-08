/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Kets
import all QuantumAlg.Util.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Fourier matrix mathematics

The original positive-phase Fourier matrix, its normalization and unitarity
are independent of the native language used to implement the transform.
The original scalar lemmas also support phase-estimation analysis.
-/

namespace QuantumAlg

open NormalizedVector

noncomputable section

/-! ### Root of unity -/

/-- Primitive `2^n`-th root of unity: `ω_n = e^{2πi/2^n}`
[dW19, qcnotes.tex:1690].
Forward-transform sign convention (`+2πi`, not `−2πi`). -/
public def ω (n : ℕ) : ℂ :=
  Complex.exp (↑(2 * Real.pi / (2 : ℝ) ^ n) * Complex.I)
-- [dW19, qcnotes.tex:1690]: ω_N = e^{2πi/N}

/-- `ω_n ^ (2^n) = 1`: the root has exact period `2^n`. -/
theorem omega_pow_eq_one (n : ℕ) : ω n ^ (2 ^ n) = 1 := by
  rw [ω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨1, ?_⟩
  push_cast
  have h : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (pow_pos two_pos n)
  field_simp

/-- `‖ω_n‖ = 1`: roots of unity lie on the unit circle. -/
@[simp]
theorem norm_omega (n : ℕ) : ‖ω n‖ = 1 := by
  rw [ω]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `omega n` equals the form used by Mathlib's `isPrimitiveRoot_exp`. -/
private theorem omega_eq_exp_div (n : ℕ) :
    ω n = Complex.exp (2 * ↑Real.pi * Complex.I / ↑(2 ^ n : ℕ)) := by
  simp only [ω]; congr 1; push_cast; ring

/-- `omega n` is a primitive `2^n`-th root of unity. -/
theorem omega_isPrimitiveRoot (n : ℕ) : IsPrimitiveRoot (ω n) (2 ^ n) := by
  rw [omega_eq_exp_div]
  exact Complex.isPrimitiveRoot_exp (2 ^ n) (by positivity)

/-! ### Normalization -/

/-- QFT normalization factor: `1/√(2^n)`, generalizing `NormalizedVector.invSqrt2`. -/
public def invSqrtN (n : ℕ) : ℂ := (↑(Real.sqrt ((2 : ℝ) ^ n)))⁻¹

@[simp]
theorem star_invSqrtN (n : ℕ) : star (invSqrtN n) = invSqrtN n := by
  rw [invSqrtN, star_inv₀, Complex.star_def, Complex.conj_ofReal]

private theorem invSqrtN_ne_zero (n : ℕ) : invSqrtN n ≠ 0 :=
  inv_ne_zero <| Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (pow_pos two_pos n)

theorem norm_invSqrtN (n : ℕ) :
    ‖invSqrtN n‖ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
  rw [invSqrtN, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- Squared QFT normalization is the reciprocal basis cardinality. -/
theorem norm_sq_invSqrtN (n : ℕ) :
    ‖invSqrtN n‖ ^ 2 = (((2 : ℝ) ^ n))⁻¹ := by
  rw [norm_invSqrtN, inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]

@[simp]
theorem invSqrtN_mul_self (n : ℕ) :
    invSqrtN n * invSqrtN n = (↑((2 : ℝ) ^ n))⁻¹ := by
  rw [invSqrtN, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (le_of_lt (pow_pos two_pos n))]

/-- Recursive normalization of the Fourier transform. -/
theorem invSqrtN_succ (n : Nat) :
    invSqrtN (n + 1) = invSqrt2 * invSqrtN n := by
  rw [invSqrtN, invSqrtN, invSqrt2, pow_succ,
    Real.sqrt_mul (by positivity : 0 ≤ (2 : Real) ^ n)]
  push_cast
  rw [mul_inv_rev]

/-- The root for an `n`-qubit transform is the square of the root for the
next larger transform. -/
theorem omega_succ_sq (n : Nat) : ω (n + 1) ^ 2 = ω n := by
  rw [ω, ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

/-- Raising the primitive `2^(low+extra)`-th root by `2^extra` yields the
primitive `2^low`-th root, uniformly for every natural exponent. -/
theorem omega_add_pow_two_pow_mul (low extra exponent : Nat) :
    ω (low + extra) ^ (2 ^ extra * exponent) =
      ω low ^ exponent := by
  rw [ω, ω, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- The halfway power of the `(n+1)`-qubit Fourier root is minus one. -/
theorem omega_succ_pow_half (n : Nat) :
    ω (n + 1) ^ (2 ^ n) = -1 := by
  rw [ω, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  push_cast
  rw [pow_succ]
  field_simp

@[simp]
theorem omega_succ_pow_period_mul (n multiplier : Nat) :
    ω (n + 1) ^ (2 ^ (n + 1) * multiplier) = 1 := by
  rw [pow_mul, omega_pow_eq_one, one_pow]

/-- Algebraic recurrence of the Fourier phase under the leading-bit/tail
split. -/
theorem qftOmega_pair_recurrence (n reversedTail inputTail : Nat)
    (outputHead inputHead : Fin 2) :
    ω n ^ (reversedTail * inputTail) *
        (if outputHead = 1 then ω (n + 1) ^ inputTail else 1) *
        (if outputHead = 1 ∧ inputHead = 1 then -1 else 1) =
      ω (n + 1) ^
        ((2 * reversedTail + outputHead.val) *
          (inputTail + 2 ^ n * inputHead.val)) := by
  fin_cases outputHead <;> fin_cases inputHead
  · simp only [Fin.ext_iff, Fin.val_one, zero_ne_one, false_and, if_false,
      add_zero, mul_one]
    rw [← omega_succ_sq, ← pow_mul]
    congr 1
    ring
  · simp only [Fin.ext_iff, Fin.val_one, zero_ne_one,
      false_and, if_false, mul_one, add_zero]
    rw [← omega_succ_sq, ← pow_mul]
    have hexponent :
        (2 * reversedTail) * (inputTail + 2 ^ n) =
          2 * (reversedTail * inputTail) +
            2 ^ (n + 1) * reversedTail := by
      rw [pow_succ]
      ring
    rw [hexponent, pow_add, omega_succ_pow_period_mul, mul_one]
  · simp only [Fin.ext_iff, Fin.val_one, zero_ne_one, and_false, if_true,
      if_false, mul_one]
    rw [← omega_succ_sq, ← pow_mul, ← pow_add]
    congr 1
    ring
  · simp only [Fin.ext_iff, Fin.val_one, true_and, if_true, mul_one]
    rw [← omega_succ_sq, ← pow_mul, ← omega_succ_pow_half]
    rw [← pow_add, ← pow_add]
    have hexponent :
        (2 * reversedTail + 1) * (inputTail + 2 ^ n) =
          (2 * (reversedTail * inputTail) + inputTail + 2 ^ n) +
            2 ^ (n + 1) * reversedTail := by
      rw [pow_succ]
      ring
    have hperiod :
        ω (n + 1) ^
            (2 * (reversedTail * inputTail) + inputTail + 2 ^ n +
              2 ^ (n + 1) * reversedTail) =
          ω (n + 1) ^
            (2 * (reversedTail * inputTail) + inputTail + 2 ^ n) := by
      rw [show
          2 * (reversedTail * inputTail) + inputTail + 2 ^ n +
              2 ^ (n + 1) * reversedTail =
            (2 * (reversedTail * inputTail) + inputTail + 2 ^ n) +
              2 ^ (n + 1) * reversedTail by ring,
        pow_add, omega_succ_pow_period_mul, mul_one]
    rw [hexponent, hperiod, pow_add]

/-! ### QFT operator -/

theorem omega_ne_zero (n : ℕ) : ω n ≠ 0 :=
  Complex.exp_ne_zero _

/-- `star ω_n = ω_n⁻¹`: conjugation inverts a point on the unit circle. -/
@[simp]
theorem star_omega (n : ℕ) : star (ω n) = (ω n)⁻¹ := by
  rw [Complex.star_def, ← RCLike.inv_eq_conj (norm_omega n)]

/-- Conjugating a natural power of a Fourier root negates its exponent. -/
theorem star_omega_pow (n exponent : ℕ) :
    star (ω n ^ exponent) = ω n ^ (-(exponent : ℤ)) := by
  rw [star_pow, star_omega, ← zpow_natCast, inv_zpow']

/-- Integer-exponent form of root scaling across additional qubits. -/
theorem omega_add_pow_two_zpow_mul (low extra : Nat) (exponent : Int) :
    ω (low + extra) ^ (((2 ^ extra : Nat) : Int) * exponent) =
      ω low ^ exponent := by
  have hroot : ω (low + extra) ^ (2 ^ extra) = ω low := by
    simpa using omega_add_pow_two_pow_mul low extra 1
  rw [zpow_mul, zpow_natCast, hroot]

/-- Integer powers of the Fourier root as an explicit real phase ratio. -/
theorem omega_zpow_eq_exp_ratio (n : Nat) (exponent : Int) :
    ω n ^ exponent =
      Complex.exp (2 * Real.pi *
        (((exponent : Real) / (2 : Real) ^ n : Real) : Complex) * Complex.I) := by
  rw [ω, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- A closed interval of powers of a Fourier root is a global starting phase
times a geometric progression indexed from zero. -/
theorem sum_Icc_omega_zpow_eq_shifted_range {n width : Nat}
    (frequency : Int) (lower upper : Fin width) (hlower : lower ≤ upper) :
    ∑ index ∈ Finset.Icc lower upper,
        ω n ^ ((index.val : Int) * frequency) =
      ω n ^ ((lower.val : Int) * frequency) *
        ∑ offset ∈ Finset.range (upper.val + 1 - lower.val),
          ω n ^ ((offset : Int) * frequency) := by
  classical
  calc
    (∑ index ∈ Finset.Icc lower upper,
        ω n ^ ((index.val : Int) * frequency)) =
      ∑ offset ∈ Finset.range (upper.val + 1 - lower.val),
        ω n ^ (((lower.val + offset : Nat) : Int) * frequency) := by
      refine Finset.sum_bij (fun index _ => index.val - lower.val) ?_ ?_ ?_ ?_
      · intro index hindex
        have hbounds := Finset.mem_Icc.mp hindex
        simp only [Finset.mem_range]
        omega
      · intro left hleft right hright heq
        have hleftLower := (Finset.mem_Icc.mp hleft).1
        have hrightLower := (Finset.mem_Icc.mp hright).1
        apply Fin.ext
        omega
      · intro offset hoffset
        have hoffsetLt := Finset.mem_range.mp hoffset
        have hvalueLt : lower.val + offset < width := by
          omega
        let index : Fin width := ⟨lower.val + offset, hvalueLt⟩
        refine ⟨index, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          constructor
          · change lower.val ≤ lower.val + offset
            omega
          · change lower.val + offset ≤ upper.val
            omega
        · change lower.val + offset - lower.val = offset
          omega
      · intro index hindex
        have hindexLower := (Finset.mem_Icc.mp hindex).1
        congr 2
        push_cast
        omega
    _ = ω n ^ ((lower.val : Int) * frequency) *
        ∑ offset ∈ Finset.range (upper.val + 1 - lower.val),
          ω n ^ ((offset : Int) * frequency) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro offset _hoffset
      rw [← zpow_add₀ (omega_ne_zero n)]
      congr 2
      push_cast
      ring

/-- Principal-frequency upper bound for a finite Fourier-root progression.
The estimate is independent of the progression length and is the discrete
form of the unit-circle chord bound. -/
theorem norm_sum_range_omega_zpow_mul_le (n m : Nat) (frequency : Int)
    (hprincipal : 2 * frequency.natAbs ≤ 2 ^ n)
    (hfrequency : frequency ≠ 0) :
    ‖∑ offset ∈ Finset.range m,
        ω n ^ ((offset : Int) * frequency)‖ ≤
      ((2 ^ n : Nat) : Real) /
        (2 * (frequency.natAbs : Real)) := by
  let θ : Real := (frequency : Real) / (2 : Real) ^ n
  have hperiodPos : 0 < (2 : Real) ^ n := pow_pos (by norm_num) _
  have habsFrequency :
      |(frequency : Real)| = (frequency.natAbs : Real) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hprincipalReal :
      2 * (frequency.natAbs : Real) ≤ (2 : Real) ^ n := by
    exact_mod_cast hprincipal
  have hthetaPrincipal : |θ| ≤ 1 / 2 := by
    rw [abs_div, habsFrequency, abs_of_pos hperiodPos]
    rw [div_le_iff₀ hperiodPos]
    nlinarith
  have hnatAbsPos : 0 < (frequency.natAbs : Real) := by
    exact_mod_cast (Int.natAbs_pos.mpr hfrequency)
  have hthetaPos : 0 < |θ| := by
    rw [abs_div, habsFrequency, abs_of_pos hperiodPos]
    exact div_pos hnatAbsPos hperiodPos
  have hsum :
      (∑ offset ∈ Finset.range m,
          ω n ^ ((offset : Int) * frequency)) =
        ∑ offset ∈ Finset.range m,
          Complex.exp (2 * Real.pi *
            (((offset : Real) * θ : Real) : Complex) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro offset _hoffset
    rw [omega_zpow_eq_exp_ratio]
    have hratio :
        ((((offset : Int) * frequency : Int) : Real) / (2 : Real) ^ n) =
          (offset : Real) * θ := by
      push_cast
      dsimp [θ]
      ring
    rw [hratio]
  rw [hsum]
  calc
    ‖∑ offset ∈ Finset.range m,
        Complex.exp (2 * Real.pi *
          (((offset : Real) * θ : Real) : Complex) * Complex.I)‖ ≤
      1 / (2 * |θ|) :=
        norm_sum_range_exp_two_pi_mul_nat_mul_I_le
          hthetaPrincipal hthetaPos
    _ = ((2 ^ n : Nat) : Real) /
        (2 * (frequency.natAbs : Real)) := by
      dsimp [θ]
      rw [abs_div, habsFrequency, abs_of_pos hperiodPos]
      norm_num
      field_simp [ne_of_gt hperiodPos, ne_of_gt hnatAbsPos]

/-- A finite Fourier-root progression whose complete real phase span is at
most `π/4` has norm at least its length times the corresponding secant slope.
The statement also covers the degenerate root-one progression. -/
theorem norm_sum_range_omega_zpow_mul_ge_of_angle_le
    (n m : Nat) (frequency : Int)
    (hangle : Real.pi *
      ((m : Real) * (|(frequency : Real)| / (2 : Real) ^ n)) ≤
        Real.pi / 4) :
    (m : Real) * (Real.sin (Real.pi / 4) / (Real.pi / 4)) ≤
      ‖∑ offset ∈ Finset.range m,
        ω n ^ ((offset : Int) * frequency)‖ := by
  let θ : Real := (frequency : Real) / (2 : Real) ^ n
  have hperiodPos : 0 < (2 : Real) ^ n := by positivity
  have hthetaAngle :
      Real.pi * ((m : Real) * |θ|) ≤ Real.pi / 4 := by
    dsimp [θ]
    rw [abs_div, abs_of_pos hperiodPos]
    exact hangle
  have hsum :
      (∑ offset ∈ Finset.range m,
          ω n ^ ((offset : Int) * frequency)) =
        ∑ offset ∈ Finset.range m,
          Complex.exp (2 * Real.pi *
            (((offset : Real) * θ : Real) : Complex) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro offset _hoffset
    rw [omega_zpow_eq_exp_ratio]
    have hratio :
        ((((offset : Int) * frequency : Int) : Real) / (2 : Real) ^ n) =
          (offset : Real) * θ := by
      push_cast
      dsimp [θ]
      ring
    rw [hratio]
  rw [hsum]
  by_cases hbase : Complex.exp (2 * Real.pi * θ * Complex.I) = 1
  · rw [sum_range_exp_two_pi_mul_nat_mul_I_eq_natCast_of_base_eq_one hbase]
    simp only [norm_natCast]
    have hquarterPos : 0 < Real.pi / 4 := by positivity
    have hfactorLe :
        Real.sin (Real.pi / 4) / (Real.pi / 4) ≤ 1 := by
      rw [div_le_one hquarterPos]
      exact Real.sin_le hquarterPos.le
    exact mul_le_of_le_one_right (Nat.cast_nonneg m) hfactorLe
  · have hquarterLe : Real.pi / 4 ≤ Real.pi := by
      calc
        Real.pi / 4 = Real.pi * (1 / 4 : Real) := by ring
        _ ≤ Real.pi * 1 := by
          exact mul_le_mul_of_nonneg_left (by norm_num) Real.pi_pos.le
        _ = Real.pi := mul_one _
    rw [sum_range_exp_two_pi_mul_nat_mul_I_eq_geom_closed hbase, norm_div]
    exact geometric_phase_norm_ratio_lower_bound_of_angle_le
      (θ := θ) (A := Real.pi / 4) (m := m)
      (div_pos Real.pi_pos (by norm_num)) hquarterLe hthetaAngle hbase

/-- Integer-power version of periodicity: `ω_n ^ d = 1` iff `2^n ∣ d`. -/
theorem omega_zpow_eq_one_iff (n : ℕ) (d : ℤ) :
    ω n ^ d = 1 ↔ ((2 ^ n : ℕ) : ℤ) ∣ d :=
  (omega_isPrimitiveRoot n).zpow_eq_one_iff_dvd d

/-- Column orthogonality [dW19, qcnotes.tex:1698]: the full-period geometric
sum `∑_{l<2^n} ω^{l·d}` vanishes when `2^n ∤ d`. -/
theorem sum_omega_zpow_eq_zero (n : ℕ) {d : ℤ}
    (hd : ¬ ((2 ^ n : ℕ) : ℤ) ∣ d) :
    ∑ l : Fin (2 ^ n), ω n ^ ((l.val : ℤ) * d) = 0 := by
  have hsum : ∀ l : Fin (2 ^ n),
      ω n ^ ((l.val : ℤ) * d) = (ω n ^ d) ^ l.val := fun l => by
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp only [hsum]
  rw [Fin.sum_univ_eq_sum_range fun i => (ω n ^ d) ^ i]
  have hne1 : ω n ^ d ≠ 1 := fun h => hd ((omega_zpow_eq_one_iff n d).mp h)
  have hN : (ω n ^ d) ^ (2 ^ n) = 1 := by
    rw [← zpow_natCast (ω n ^ d) (2 ^ n), ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, omega_pow_eq_one, one_zpow]
  rw [geom_sum_eq hne1, hN, sub_self, zero_div]

/-- The certified, metadata-free quantum Fourier transform on `n` qubits
[dW19, qcnotes.tex:1692]. Its matrix entry `(j, k)` is
`invSqrtN n * ω_n^{j·k}`. Unitarity follows from column orthogonality
[dW19, qcnotes.tex:1696]. -/
@[expose] public def QFTOperator (n : ℕ) : UnitaryOperator (Qubits n) :=
  let qftMatrix : HilbertOperator (Qubits n) :=
    Matrix.of fun (j k : Fin (2 ^ n)) =>
      invSqrtN n * ω n ^ (j.val * k.val)
  UnitaryOperator.ofMatrix qftMatrix (by
    rw [Matrix.mem_unitaryGroup_iff']
    ext j k
    have hterm : ∀ l : Fin (2 ^ n),
        star qftMatrix j l * qftMatrix l k =
          (↑((2 : ℝ) ^ n))⁻¹ *
            ω n ^ ((l.val : ℤ) * ((k.val : ℤ) - (j.val : ℤ))) := by
      intro l
      simp only [Matrix.star_apply, qftMatrix, Matrix.of_apply, star_mul',
        star_pow, star_omega, star_invSqrtN]
      rw [mul_mul_mul_comm, invSqrtN_mul_self]
      congr 1
      rw [inv_pow, ← zpow_natCast (ω n) (l.val * j.val),
        ← zpow_natCast (ω n) (l.val * k.val), ← zpow_neg,
        ← zpow_add₀ (omega_ne_zero n)]
      congr 1
      push_cast
      ring
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hterm]
    rw [← Finset.mul_sum]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have h0 : ∀ l : Fin (2 ^ n),
          ω n ^ ((l.val : ℤ) * ((j.val : ℤ) - (j.val : ℤ))) = (1 : ℂ) :=
        fun l => by rw [sub_self, mul_zero, zpow_zero]
      simp only [h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      push_cast
      exact inv_mul_cancel₀ (pow_ne_zero n two_ne_zero)
    · rw [if_neg hjk]
      have hd : ¬ ((2 ^ n : ℕ) : ℤ) ∣ ((k.val : ℤ) - (j.val : ℤ)) := by
        intro hdvd
        have h0 : (k.val : ℤ) - (j.val : ℤ) = 0 :=
          Int.eq_zero_of_abs_lt_dvd hdvd (Int.abs_sub_lt_of_lt_lt j.isLt k.isLt)
        exact hjk (Fin.val_injective
          (by exact_mod_cast sub_eq_zero.mp h0 : k.val = j.val)).symm
      rw [sum_omega_zpow_eq_zero n hd, mul_zero])

/-- Matrix-entry formula exposed through the certified QFT carrier. -/
@[simp]
public theorem QFTOperator_entry (n : ℕ) (j k : Fin (2 ^ n)) :
    QFTOperator n j k = invSqrtN n * ω n ^ (j.val * k.val) := rfl

/-- Matrix-entry formula for the inverse certified QFT.  The inverse changes
the Fourier phase sign while preserving the same normalization. -/
theorem invQFTOperator_entry (n : Nat) (j k : Fin (2 ^ n)) :
    ((QFTOperator n)⁻¹ : UnitaryOperator (Qubits n)) j k =
      invSqrtN n * ω n ^ (-((k.val : Int) * (j.val : Int))) := by
  change star (QFTOperator n k j) = _
  rw [QFTOperator_entry, star_mul', star_invSqrtN, star_omega_pow]
  congr 1

end

end QuantumAlg
