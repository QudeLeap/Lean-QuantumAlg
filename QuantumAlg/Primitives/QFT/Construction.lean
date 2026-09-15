/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Util.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Quantum Fourier Transform

The quantum Fourier transform (QFT) on `n` qubits is the `2^n × 2^n` unitary
matrix mapping computational basis states to Fourier basis states
[dW19, qcnotes.tex:1692; Lin22, phaseestimation.tex:351]:

  `QFT |x⟩ = (1/√N) Σ_{y=0}^{N-1} ω^{xy} |y⟩`

where `N = 2^n` and `ω = e^{2πi/N}` is the primitive `N`-th root of unity.

## Conventions

- **Sign**: forward transform uses `ω = e^{+2πi/N}` (standard physics sign
  convention, matching [dW19, qcnotes.tex:1690] and
  [Lin22, phaseestimation.tex:349]).
- **Normalization**: `1/√N` prefactor makes the transform unitary.
- **Endianness**: big-endian, matching `QuantumAlg.NormalizedVector`.

## Main definitions

- `QuantumAlg.omega n` — primitive `2^n`-th root of unity `e^{2πi/2^n}`.
- `QuantumAlg.invSqrtN n` — normalization factor `1/√(2^n)`.
- `QuantumAlg.QFT n` — the QFT gate on `n` qubits.

## Main results

- `QuantumAlg.omega_pow_eq_one` — `ω^(2^n) = 1`.
- `QuantumAlg.norm_omega` — `‖ω‖ = 1`.
- `QuantumAlg.QFT_apply_ket` — component formula for `QFT |x⟩`.
- `QuantumAlg.sum_omega_zpow_eq_zero` — full-period geometric sums of
  nontrivial powers of `ω` vanish (column orthogonality).
- `QuantumAlg.QuantumFourierTransform.basisAction_gateCounts` — the QFT basis action together
  with the exact gate counts of the same typed circuit.

Pinned Mathlib API: `Complex.exp`, `Complex.exp_nat_mul`, `Complex.exp_eq_one_iff`,
`Complex.norm_exp_ofReal_mul_I`, `Complex.isPrimitiveRoot_exp`,
`Matrix.of_apply`, `Real.mul_self_sqrt`, `RCLike.inv_eq_conj`,
`IsPrimitiveRoot.zpow_eq_one_iff_dvd`, `geom_sum_eq`,
`Fin.sum_univ_eq_sum_range`, `Int.eq_zero_of_abs_lt_dvd`,
`Int.abs_sub_lt_of_lt_lt`, `Matrix.mem_unitaryGroup_iff'`.
-/

section

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
def QFTOperator (n : ℕ) : UnitaryOperator (Qubits n) :=
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
theorem QFTOperator_entry (n : ℕ) (j k : Fin (2 ^ n)) :
    QFTOperator n j k = invSqrtN n * ω n ^ (j.val * k.val) := rfl

/-- Matrix-entry formula for the inverse certified QFT.  The inverse changes
the Fourier phase sign while preserving the same normalization. -/
theorem invQFTOperator_entry (n : Nat) (j k : Fin (2 ^ n)) :
    ((QFTOperator n)⁻¹ : UnitaryOperator (Qubits n)) j k =
      invSqrtN n * ω n ^ (-((k.val : Int) * (j.val : Int))) := by
  change star (QFTOperator n k j) = _
  rw [QFTOperator_entry, star_mul', star_invSqrtN, star_omega_pow]
  congr 1

/-! ### Typed circuit and decomposition resources -/



/-- Strict event coordinate of one addressed QFT controlled phase. -/
def qftControlledPhaseEvent : Resource.Event .quantum :=
  .gate qftControlledPhaseLabel

/-- Strict event coordinate of one QFT Hadamard. -/
def qftHadamardEvent : Resource.Event .quantum :=
  Gate.atomicEvent (.builtin "hadamard")

/-- Strict event coordinate of one addressed QFT swap. -/
def qftSwapEvent : Resource.Event .quantum :=
  Gate.atomicEvent (.builtin "swap")



/-! ### Sealed QFT primitives -/

@[simp]
theorem qftControlledPhaseOperator_applyVec_ket {n : Nat}
    (control target : Fin n) (angle : Real) (basis : Fin (2 ^ n)) :
    (qftControlledPhaseOperator control target angle).applyVec
        (NormalizedVector.ket (R := Qubits n) basis : HilbertVector (Qubits n)) =
      qftControlledPhaseFactor control target angle basis •
        (NormalizedVector.ket (R := Qubits n) basis : HilbertVector (Qubits n)) := by
  ext i
  rw [UnitaryOperator.applyVec_apply]
  simp only [qftControlledPhaseOperator, UnitaryOperator.coe_ofMatrix,
    NormalizedVector.ket_apply]
  rw [Finset.sum_eq_single basis]
  · by_cases hib : i = basis
    · subst i
      simp
    · simp [hib]
  · intro k _ hk
    simp [hk]
  · simp

/-- Reverse the `n` significant bits of a computational-basis label. -/
def qftReverseBits (n : Nat) (label : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨Nat.ofBits (fun bit : Fin n => label.val.testBit (Fin.rev bit).val),
    Nat.ofBits_lt_two_pow _⟩

@[simp]
theorem qftReverseBits_testBit (n : Nat) (label : Fin (2 ^ n))
    (bit : Fin n) :
    (qftReverseBits n label).val.testBit bit.val =
      label.val.testBit (Fin.rev bit).val := by
  unfold qftReverseBits
  rw [Nat.testBit_ofBits_lt]

@[simp]
theorem qftReverseBits_involutive (n : Nat) (label : Fin (2 ^ n)) :
    qftReverseBits n (qftReverseBits n label) = label := by
  apply Fin.val_injective
  change Nat.ofBits
      (fun bit : Fin n =>
        (qftReverseBits n label).val.testBit (Fin.rev bit).val) = label.val
  have hfun :
      (fun bit : Fin n =>
        (qftReverseBits n label).val.testBit (Fin.rev bit).val) =
        fun bit : Fin n => label.val.testBit bit.val := by
    funext bit
    rw [qftReverseBits_testBit]
    simp
  rw [hfun, Nat.ofBits_testBit, Nat.mod_eq_of_lt label.isLt]

/-- Bit reversal as a self-inverse basis-label permutation. -/
def qftReverseBitsPerm (n : Nat) : Equiv.Perm (Fin (2 ^ n)) where
  toFun := qftReverseBits n
  invFun := qftReverseBits n
  left_inv := qftReverseBits_involutive n
  right_inv := qftReverseBits_involutive n

/-- Basis-label action of the usual three-CNOT addressed SWAP. -/
def qftSwapLabel {n : Nat} (left right : Fin n)
    (label : Fin (2 ^ n)) : Fin (2 ^ n) :=
  WireAddress.cnotMap left right
    (WireAddress.cnotMap right left
      (WireAddress.cnotMap left right label))

@[simp]
theorem qftSwapLabel_left {n : Nat} (left right : Fin n)
    (hne : left ≠ right) (label : Fin (2 ^ n)) :
    (qftSwapLabel left right label).val.testBit
        (WireAddress.bitIndex left).val =
      label.val.testBit (WireAddress.bitIndex right).val := by
  unfold qftSwapLabel WireAddress.cnotMap
  by_cases hl : label.val.testBit (WireAddress.bitIndex left).val <;>
    by_cases hr : label.val.testBit (WireAddress.bitIndex right).val <;>
      simp [hl, hr, WireAddress.bit_flipBit_self,
        WireAddress.bit_flipBit_of_ne (Ne.symm hne)]

@[simp]
theorem qftSwapLabel_right {n : Nat} (left right : Fin n)
    (hne : left ≠ right) (label : Fin (2 ^ n)) :
    (qftSwapLabel left right label).val.testBit
        (WireAddress.bitIndex right).val =
      label.val.testBit (WireAddress.bitIndex left).val := by
  unfold qftSwapLabel WireAddress.cnotMap
  by_cases hl : label.val.testBit (WireAddress.bitIndex left).val <;>
    by_cases hr : label.val.testBit (WireAddress.bitIndex right).val <;>
      simp [hl, hr, WireAddress.bit_flipBit_self,
        WireAddress.bit_flipBit_of_ne (Ne.symm hne),
        WireAddress.bit_flipBit_of_ne hne]

@[simp]
theorem qftSwapLabel_of_ne {n : Nat} (left right bit : Fin n)
    (hne : left ≠ right) (hleft : bit ≠ left) (hright : bit ≠ right)
    (label : Fin (2 ^ n)) :
    (qftSwapLabel left right label).val.testBit
        (WireAddress.bitIndex bit).val =
      label.val.testBit (WireAddress.bitIndex bit).val := by
  unfold qftSwapLabel WireAddress.cnotMap
  by_cases hl : label.val.testBit (WireAddress.bitIndex left).val <;>
    by_cases hr : label.val.testBit (WireAddress.bitIndex right).val <;>
      simp [hl, hr, WireAddress.bit_flipBit_self,
        WireAddress.bit_flipBit_of_ne (Ne.symm hne),
        WireAddress.bit_flipBit_of_ne (Ne.symm hleft),
        WireAddress.bit_flipBit_of_ne (Ne.symm hright)]

@[simp]
theorem qftSwapOperator_applyVec_ket {n : Nat} (left right : Fin n)
    (hne : left ≠ right) (label : Fin (2 ^ n)) :
    (qftSwapOperator left right hne).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n) (qftSwapLabel left right label) :
        HilbertVector (Qubits n)) := by
  change
    (((QubitPrimitive.operator (.cnot left right hne)) *
        (QubitPrimitive.operator (.cnot right left hne.symm)) *
          (QubitPrimitive.operator (.cnot left right hne))).applyVec
        (NormalizedVector.ket (R := Qubits n) label :
          HilbertVector (Qubits n))) = _
  rw [UnitaryOperator.mul_applyVec,
    UnitaryOperator.mul_applyVec]
  change
    ((((QubitPrimitive.operator (.cnot left right hne)).apply
        ((QubitPrimitive.operator (.cnot right left hne.symm)).apply
          ((QubitPrimitive.operator (.cnot left right hne)).apply
            (NormalizedVector.ket (R := Qubits n) label)))) :
        NormalizedVector (Qubits n)) : HilbertVector (Qubits n)) = _
  rw [QubitPrimitive.operator_apply_ket,
    QubitPrimitive.operator_apply_ket,
    QubitPrimitive.operator_apply_ket]
  rfl

/-- The only non-Hadamard primitive kinds used by the recursive QFT circuit. -/
inductive QFTPrimitive (n : Nat) where
  /-- One addressed controlled phase with its semantic angle. -/
  | controlledPhase (control target : Fin n) (angle : Real)
      (hne : control ≠ target)
  /-- One addressed wire swap. -/
  | swap (left right : Fin n) (hne : left ≠ right)

namespace QFTPrimitive

/-- Certified operator denoted by one QFT primitive. -/
def operator {n : Nat} : QFTPrimitive n → UnitaryOperator (Qubits n)
  | .controlledPhase control target angle _ =>
      qftControlledPhaseOperator control target angle
  | .swap left right hne => qftSwapOperator left right hne

/-- Physical footprint of one QFT primitive. -/
def systemIdx {n : Nat} : QFTPrimitive n → List Nat
  | .controlledPhase control target _ _ => [control.val, target.val]
  | .swap left right _ => [left.val, right.val]

/-- The strict gate coordinate fixed by each primitive kind. -/
def gateLabel {n : Nat} : QFTPrimitive n → Resource.GateLabel
  | .controlledPhase _ _ _ _ => qftControlledPhaseLabel
  | .swap _ _ _ => .builtin "swap"

/-- Strict execution event selected by one QFT primitive. -/
def event {n : Nat} (primitive : QFTPrimitive n) : Resource.Event .quantum :=
  .gate primitive.gateLabel

/-- One sealed leaf selected from the reusable Components declarations. -/
def leaf {n : Nat} : QFTPrimitive n → UnitaryLeaf (Qubits n)
  | .controlledPhase control target angle _ =>
      qftControlledPhaseLeafAt control target angle [control.val, target.val]
  | .swap left right hne =>
      qftSwapLeafAt left right hne [left.val, right.val]

@[simp]
theorem qftLeaf_systemIdx {n : Nat} (primitive : QFTPrimitive n) :
    primitive.leaf.systemIdx = primitive.systemIdx := by
  cases primitive <;> rfl

@[simp]
theorem qftLeaf_event {n : Nat} (primitive : QFTPrimitive n) :
    primitive.leaf.event = primitive.event := by
  cases primitive <;> rfl



/-- Distinct addressed wires give duplicate-free primitive footprints. -/
theorem systemIdx_nodup {n : Nat} (primitive : QFTPrimitive n) :
    primitive.systemIdx.Nodup := by
  cases primitive with
  | controlledPhase control target angle hne =>
      have hval : control.val ≠ target.val := fun h => hne (Fin.ext h)
      simp [systemIdx, hval]
  | swap left right hne =>
      have hval : left.val ≠ right.val := fun h => hne (Fin.ext h)
      simp [systemIdx, hval]

end QFTPrimitive

/-- Lift one QFT primitive into the structural circuit language. -/
def qftPrimitiveCircuit {n : Nat} (primitive : QFTPrimitive n) :
    UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf primitive.leaf (by
    rw [QFTPrimitive.qftLeaf_systemIdx]
    exact primitive.systemIdx_nodup)

/-- Advertise the complete canonical register footprint while retaining the
smaller addressed footprint on the primitive leaf itself. -/
def qftPrimitiveCircuitAt {n : Nat} (primitive : QFTPrimitive n) :
    UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeafAt (List.range n) primitive.leaf
    List.nodup_range (by
      rw [QFTPrimitive.qftLeaf_systemIdx]
      exact primitive.systemIdx_nodup) (by
      rw [QFTPrimitive.qftLeaf_systemIdx]
      cases primitive with
      | controlledPhase control target angle hne =>
          simp [QFTPrimitive.systemIdx, control.isLt, target.isLt]
      | swap left right hne =>
          simp [QFTPrimitive.systemIdx, left.isLt, right.isLt])

@[simp]
theorem qftPrimitiveCircuitAt_physical_idx {n : Nat}
    (primitive : QFTPrimitive n) :
    (qftPrimitiveCircuitAt primitive).physical_idx = List.range n :=
  rfl

/-- The full-footprint wrapper retains the primitive's single ordered strict
event. -/
@[simp]
theorem qftPrimitiveCircuitAt_eventTrace {n : Nat}
    (primitive : QFTPrimitive n) :
    (qftPrimitiveCircuitAt primitive).eventTrace = [primitive.event] := by
  change [primitive.leaf.event] = [primitive.event]
  rw [QFTPrimitive.qftLeaf_event]

/-- The full-footprint wrapper retains exactly one occurrence of the primitive
event. -/
@[simp]
theorem qftPrimitiveCircuitAt_eventCost {n : Nat}
    (primitive : QFTPrimitive n) :
    (qftPrimitiveCircuitAt primitive).eventCost =
      ResourcePool.singleton primitive.event := by
  change ResourcePool.singleton primitive.leaf.event =
    ResourcePool.singleton primitive.event
  rw [QFTPrimitive.qftLeaf_event]

/-- The full-footprint wrapper retains the primitive event as one depth atom. -/
@[simp]
theorem qftPrimitiveCircuitAt_eventDepth {n : Nat}
    (primitive : QFTPrimitive n) :
    (qftPrimitiveCircuitAt primitive).eventDepth = .atom primitive.event := by
  change DepthExpr.atom primitive.leaf.event = DepthExpr.atom primitive.event
  rw [QFTPrimitive.qftLeaf_event]

/-- Each sealed QFT primitive occurs exactly once at its own strict event
coordinate. -/
theorem qftPrimitiveCircuitAt_event_count {n : Nat}
    (primitive : QFTPrimitive n) :
    ResourcePool.count primitive.event
        (qftPrimitiveCircuitAt primitive).eventCost = 1 := by
  rw [qftPrimitiveCircuitAt_eventCost]
  simp

/-- Linearizing a sealed QFT primitive's event-depth atom recovers its event
pool. -/
theorem qftPrimitiveCircuitAt_resourcesFromEventDepth {n : Nat}
    (primitive : QFTPrimitive n) :
    (qftPrimitiveCircuitAt primitive).resourcesFromEventDepth =
      ResourcePool.singleton primitive.event := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    qftPrimitiveCircuitAt_eventCost]



/-- Rotation angle used between the leading wire and the `(offset+1)`st wire
of one recursive QFT stage. -/
def qftPhaseAngle (offset : Nat) : Real :=
  2 * Real.pi / (2 : Real) ^ (offset + 2)

/-- The `offset`th controlled phase in the leading recursive QFT stage. -/
def qftPhasePrimitive (n : Nat) (offset : Fin n) : QFTPrimitive (n + 1) :=
  let target : Fin (n + 1) :=
    ⟨offset.val + 1, Nat.succ_lt_succ offset.isLt⟩
  .controlledPhase 0 target (qftPhaseAngle offset.val) (by
    intro h
    have hval := congrArg Fin.val h
    simp [target] at hval)

/-- One full-footprint controlled-phase leaf in the leading QFT stage. -/
def qftPhaseStep (n : Nat) (offset : Fin n) : UnitaryCircuit (Qubits (n + 1)) :=
  qftPrimitiveCircuitAt (qftPhasePrimitive n offset)

@[simp]
theorem qftPhaseStep_applyVec_ket (n : Nat) (offset : Fin n)
    (label : Fin (2 ^ (n + 1))) :
    (qftPhaseStep n offset).applyVec
        (NormalizedVector.ket (R := Qubits (n + 1)) label :
          HilbertVector (Qubits (n + 1))) =
      qftControlledPhaseFactor 0
          ⟨offset.val + 1, Nat.succ_lt_succ offset.isLt⟩
          (qftPhaseAngle offset.val) label •
        (NormalizedVector.ket (R := Qubits (n + 1)) label :
          HilbertVector (Qubits (n + 1))) := by
  change
    (qftControlledPhaseOperator 0
      ⟨offset.val + 1, Nat.succ_lt_succ offset.isLt⟩
      (qftPhaseAngle offset.val)).applyVec
        (NormalizedVector.ket (R := Qubits (n + 1)) label :
          HilbertVector (Qubits (n + 1))) = _
  exact qftControlledPhaseOperator_applyVec_ket _ _ _ label

/-- Big-endian splitting of an `(n+1)`-qubit basis label into its leading bit
and lower `n`-bit tail. -/
def qftPairEquiv (n : Nat) :
    Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  (prodEquiv (m := 1) (n := n)).trans
    (finCongr (by rw [Nat.add_comm 1 n]))

@[simp]
theorem qftPairEquiv_apply_val (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftPairEquiv n (head, tail)).val = tail.val + 2 ^ n * head.val :=
  rfl

/-- Reindexing a raw tensor circuit by the QFT pair equivalence exposes the
expected leading-bit/tail matrix entry without dependent casts. -/
theorem qftReindexTensor_matrix_apply_pair (n : Nat)
    (left : UnitaryCircuit (Qubits 1)) (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx)
    (outputHead inputHead : Fin 2)
    (outputTail inputTail : Fin (2 ^ n)) :
    (UnitaryCircuit.reindex
        (R := Register.prod (Qubits 1) (Qubits n))
        (S := Qubits (n + 1))
        (qftPairEquiv n) (UnitaryCircuit.tensor left right layout)).matrix
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      left.matrix outputHead inputHead *
        right.matrix outputTail inputTail := by
  rw [UnitaryCircuit.reindex_matrix]
  rw [UnitaryOperator.coe_reindex]
  change
    (UnitaryCircuit.tensor left right layout).matrix
        ((qftPairEquiv n).symm
          (qftPairEquiv n (outputHead, outputTail)))
        ((qftPairEquiv n).symm
          (qftPairEquiv n (inputHead, inputTail))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change
    (UnitaryCircuit.tensor left right layout).matrix
        (outputHead, outputTail) (inputHead, inputTail) = _
  rw [UnitaryCircuit.tensor_matrix]
  rfl

/-- The leading Hadamard layer, built from the sealed one-qubit component and
an explicit identity circuit on the lower wires. -/
def qftLeadingHadamard (n : Nat) : UnitaryCircuit (Qubits (n + 1)) := by
  let rest := UnitaryCircuit.identity (Qubits n) (List.range' 1 n) List.nodup_range'
  let layout : PhysicalLayout.DisjointMerge Gate.H.physical_idx rest.physical_idx :=
    { left_nodup := Gate.H.physical_idx_nodup
      right_nodup := rest.physical_idx_nodup
      disjoint := by
        change [0].Disjoint (List.range' 1 n)
        simp }
  exact UnitaryCircuit.reindex (qftPairEquiv n)
    (UnitaryCircuit.tensor Gate.H rest layout)

@[simp]
theorem qftLeadingHadamard_physical_idx (n : Nat) :
    (qftLeadingHadamard n).physical_idx = List.range (n + 1) := by
  unfold qftLeadingHadamard
  change 0 :: List.range' 1 n = List.range (n + 1)
  rw [List.range'_eq_map_range, List.range_succ_eq_map]
  simp only [Nat.one_add]



/-- The leading QFT stage emits exactly one Hadamard event. -/
@[simp]
theorem qftLeadingHadamard_eventCost (n : Nat) :
    (qftLeadingHadamard n).eventCost =
      ResourcePool.singleton qftHadamardEvent := by
  simp [qftLeadingHadamard, qftHadamardEvent, Gate.atomicEventCost]

/-- The leading QFT stage keeps the Hadamard atom in parallel with an empty
tail path. -/
@[simp]
theorem qftLeadingHadamard_eventDepth (n : Nat) :
    (qftLeadingHadamard n).eventDepth =
      .tensor (.atom qftHadamardEvent) .id := by
  simp [qftLeadingHadamard, qftHadamardEvent, Gate.atomicEventDepth]

/-- Any strict event assignment giving the Hadamard event unit duration makes
the leading QFT stage one layer deep. -/
@[simp]
theorem qftLeadingHadamard_evaluatedEventDepth (n : Nat)
    (assign : Resource.Event .quantum → Nat)
    (hHadamard : assign qftHadamardEvent = 1) :
    (qftLeadingHadamard n).evaluatedEventDepth assign = 1 := by
  simp [UnitaryCircuit.evaluatedEventDepth, qftLeadingHadamard_eventDepth, hHadamard]

/-- Unit strict-event duration gives the leading Hadamard stage depth one. -/
theorem qftLeadingHadamard_evaluatedEventDepth_of_one (n : Nat) :
    (qftLeadingHadamard n).evaluatedEventDepth (fun _event => 1) = 1 :=
  qftLeadingHadamard_evaluatedEventDepth n (fun _event => 1) rfl

@[simp]
theorem HOp_apply_fin_two (output input : Fin 2) :
    Gate.HOp output input =
      invSqrt2 * (if output = 1 ∧ input = 1 then -1 else 1) := by
  fin_cases output <;> fin_cases input <;> simp [Gate.HOp]

@[simp]
theorem qftLeadingHadamard_matrix_apply_pair (n : Nat)
    (outputHead inputHead : Fin 2)
    (outputTail inputTail : Fin (2 ^ n)) :
    (qftLeadingHadamard n).matrix
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      Gate.HOp outputHead inputHead *
        if outputTail = inputTail then 1 else 0 := by
  unfold qftLeadingHadamard
  rw [qftReindexTensor_matrix_apply_pair]
  simp [Gate.H_matrix, Matrix.one_apply]

/-- First `count` controlled phases of one leading QFT stage. -/
def qftPhaseLayerPrefix (n : Nat) :
    (count : Nat) → count ≤ n → UnitaryCircuit (Qubits (n + 1))
  | 0, _ =>
      UnitaryCircuit.identity (Qubits (n + 1)) (List.range (n + 1))
        List.nodup_range
  | count + 1, hcount =>
      UnitaryCircuit.seq (qftPhaseLayerPrefix n count (by omega))
        (qftPhaseStep n ⟨count, by omega⟩)

/-- All controlled phases for one leading recursive QFT stage. -/
def qftPhaseLayer (n : Nat) : UnitaryCircuit (Qubits (n + 1)) :=
  qftPhaseLayerPrefix n n le_rfl

/-- Scalar accumulated by the first `count` controlled phases of one QFT
stage on a computational-basis label. -/
def qftPhaseLayerFactorPrefix (n : Nat) :
    (count : Nat) → count ≤ n → Fin (2 ^ (n + 1)) → Complex
  | 0, _, _ => 1
  | count + 1, hcount, label =>
      qftControlledPhaseFactor 0
          ⟨count + 1, by omega⟩ (qftPhaseAngle count) label *
        qftPhaseLayerFactorPrefix n count (by omega) label

/-- One phase-layer factor, indexed in source-circuit order. -/
def qftPhaseFactorAt (n : Nat) (offset : Fin n)
    (label : Fin (2 ^ (n + 1))) : Complex :=
  qftControlledPhaseFactor 0
    ⟨offset.val + 1, Nat.succ_lt_succ offset.isLt⟩
    (qftPhaseAngle offset.val) label

/-- Reconstruct a natural number as the weighted sum of its finite bit vector. -/
theorem natOfBits_eq_sum {n : Nat} (bits : Fin n → Bool) :
    Nat.ofBits bits = ∑ bit : Fin n, (bits bit).toNat * 2 ^ bit.val := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.ofBits_succ, Fin.sum_univ_succ]
      rw [ih (bits ∘ Fin.succ)]
      simp only [Function.comp_apply]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have hsum :
          (∑ bit : Fin n,
              (bits bit.succ).toNat * 2 ^ (bit.val + 1)) =
            2 * ∑ bit : Fin n, (bits bit.succ).toNat * 2 ^ bit.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro bit _
        rw [pow_succ]
        ring
      rw [hsum]
      omega

/-- The recursive scalar accumulator is exactly the product of the phase
factors represented by its first `count` structural leaves. -/
theorem qftPhaseLayerFactorPrefix_eq_prod (n count : Nat)
    (hcount : count ≤ n) (label : Fin (2 ^ (n + 1))) :
    qftPhaseLayerFactorPrefix n count hcount label =
      ∏ offset : Fin count,
        qftPhaseFactorAt n
          ⟨offset.val, lt_of_lt_of_le offset.isLt hcount⟩ label := by
  induction count with
  | zero => simp [qftPhaseLayerFactorPrefix]
  | succ count ih =>
      rw [qftPhaseLayerFactorPrefix, Fin.prod_univ_castSucc, ih (by omega)]
      rw [mul_comm]
      rfl

/-- The source angle of one phase leaf is the corresponding binary-weight
power of the common `(n+1)`-qubit Fourier root. -/
theorem qftPhaseAngle_exp_eq_omega_pow (n : Nat) (offset : Fin n) :
    Complex.exp (qftPhaseAngle offset.val * Complex.I) =
      ω (n + 1) ^ (2 ^ (Fin.rev offset).val) := by
  rw [ω, ← Complex.exp_nat_mul]
  congr 1
  simp only [qftPhaseAngle]
  push_cast
  have hsum : (Fin.rev offset).val + (offset.val + 2) = n + 1 := by
    simp [Fin.rev]
    omega
  field_simp
  rw [← pow_add, add_comm (offset.val + 2) (Fin.rev offset).val, hsum]

/-- Each actual controlled-phase leaf contributes the Fourier-root power of
its addressed input bit, and contributes one when the leading bit is zero. -/
theorem qftPhaseFactorAt_eq_omega_pow (n : Nat) (offset : Fin n)
    (label : Fin (2 ^ (n + 1))) :
    qftPhaseFactorAt n offset label =
      if label.val.testBit n then
        ω (n + 1) ^
          ((label.val.testBit (Fin.rev offset).val).toNat *
            2 ^ (Fin.rev offset).val)
      else 1 := by
  have htarget : n - (offset.val + 1) = (Fin.rev offset).val := by
    simp [Fin.rev]
  unfold qftPhaseFactorAt qftControlledPhaseFactor
  change
    (if label.val.testBit n &&
          label.val.testBit (n - (offset.val + 1)) then
        Complex.exp (qftPhaseAngle offset.val * Complex.I)
      else 1) = _
  by_cases hhead : label.val.testBit n
  · simp only [hhead, Bool.true_and, if_true]
    by_cases htargetBit : label.val.testBit (n - (offset.val + 1))
    · rw [if_pos htargetBit]
      rw [qftPhaseAngle_exp_eq_omega_pow]
      simp [htargetBit]
    · rw [if_neg htargetBit]
      simp [htargetBit]
  · simp [hhead]

/-- The complete phase layer contributes the Fourier root raised to the lower
`n` input bits whenever the leading output branch is one. -/
theorem qftPhaseLayerFactor_eq (n : Nat)
    (label : Fin (2 ^ (n + 1))) :
    qftPhaseLayerFactorPrefix n n le_rfl label =
      if label.val.testBit n then
        ω (n + 1) ^ (label.val % 2 ^ n)
      else 1 := by
  rw [qftPhaseLayerFactorPrefix_eq_prod]
  have hcast (offset : Fin n) :
      (⟨offset.val, lt_of_lt_of_le offset.isLt le_rfl⟩ : Fin n) = offset :=
    Fin.ext rfl
  simp_rw [hcast]
  by_cases hhead : label.val.testBit n
  · simp_rw [qftPhaseFactorAt_eq_omega_pow, if_pos hhead]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))]
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    rw [← natOfBits_eq_sum]
    exact Nat.ofBits_testBit label.val n
  · simp [qftPhaseFactorAt_eq_omega_pow, hhead]

theorem qftPhaseLayerPrefix_applyVec_ket (n count : Nat)
    (hcount : count ≤ n) (label : Fin (2 ^ (n + 1))) :
    (qftPhaseLayerPrefix n count hcount).applyVec
        (NormalizedVector.ket (R := Qubits (n + 1)) label :
          HilbertVector (Qubits (n + 1))) =
      qftPhaseLayerFactorPrefix n count hcount label •
        (NormalizedVector.ket (R := Qubits (n + 1)) label :
          HilbertVector (Qubits (n + 1))) := by
  induction count with
  | zero =>
      simp [qftPhaseLayerPrefix, qftPhaseLayerFactorPrefix]
  | succ count ih =>
      rw [qftPhaseLayerPrefix, UnitaryCircuit.applyVec_seq, ih (by omega),
        UnitaryCircuit.applyVec_smul, qftPhaseStep_applyVec_ket]
      simp only [smul_smul, qftPhaseLayerFactorPrefix]
      rw [mul_comm]

@[simp]
theorem qftPhaseLayer_applyVec_ket (n : Nat)
    (label : Fin (2 ^ (n + 1))) :
    (qftPhaseLayer n).applyVec
        (NormalizedVector.ket (R := Qubits (n + 1)) label :
          HilbertVector (Qubits (n + 1))) =
      (if label.val.testBit n then
          ω (n + 1) ^ (label.val % 2 ^ n)
        else 1) •
        (NormalizedVector.ket (R := Qubits (n + 1)) label :
          HilbertVector (Qubits (n + 1))) := by
  rw [qftPhaseLayer, qftPhaseLayerPrefix_applyVec_ket,
    qftPhaseLayerFactor_eq]

theorem qftPairEquiv_testBit_high (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftPairEquiv n (head, tail)).val.testBit n = decide (head = 1) := by
  rw [qftPairEquiv_apply_val]
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add head.val tail.isLt n]
  fin_cases head
  · simp
  · simp

theorem qftPairEquiv_mod_tail (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftPairEquiv n (head, tail)).val % 2 ^ n = tail.val := by
  rw [qftPairEquiv_apply_val, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt tail.isLt

theorem qftPairEquiv_testBit_low (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) (bit : Fin n) :
    (qftPairEquiv n (head, tail)).val.testBit bit.val =
      tail.val.testBit bit.val := by
  rw [qftPairEquiv_apply_val, Nat.add_comm,
    Nat.testBit_two_pow_mul_add head.val tail.isLt bit.val]
  simp [bit.isLt]

/-- Bit reversal moves the leading bit to the least-significant position and
recursively reverses the lower label. -/
theorem qftReverseBits_pair (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftReverseBits (n + 1) (qftPairEquiv n (head, tail))).val =
      2 * (qftReverseBits n tail).val + head.val := by
  change Nat.ofBits (fun bit : Fin (n + 1) =>
      (qftPairEquiv n (head, tail)).val.testBit (Fin.rev bit).val) = _
  rw [Nat.ofBits_succ]
  congr 1
  · congr 1
    apply congrArg Nat.ofBits
    funext bit
    have hlow := qftPairEquiv_testBit_low n head tail (Fin.rev bit)
    simpa [Fin.rev] using hlow
  · have hhigh := qftPairEquiv_testBit_high n head tail
    fin_cases head <;> simpa [Fin.rev] using congrArg Bool.toNat hhigh

theorem qftPhaseLayer_applyVec_pair_ket (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftPhaseLayer n).applyVec
        (NormalizedVector.ket (R := Qubits (n + 1))
          (qftPairEquiv n (head, tail)) : HilbertVector (Qubits (n + 1))) =
      (if head = 1 then ω (n + 1) ^ tail.val else 1) •
        (NormalizedVector.ket (R := Qubits (n + 1))
          (qftPairEquiv n (head, tail)) : HilbertVector (Qubits (n + 1))) := by
  rw [qftPhaseLayer_applyVec_ket, qftPairEquiv_testBit_high,
    qftPairEquiv_mod_tail]
  by_cases hhead : head = 1 <;> simp [hhead]

@[simp]
theorem qftPhaseLayer_matrix_apply_pair (n : Nat)
    (outputHead inputHead : Fin 2)
    (outputTail inputTail : Fin (2 ^ n)) :
    (qftPhaseLayer n).matrix
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      if outputHead = inputHead ∧ outputTail = inputTail then
        (if inputHead = 1 then ω (n + 1) ^ inputTail.val else 1)
      else 0 := by
  have h := congrArg
    (fun state : HilbertVector (Qubits (n + 1)) =>
      state (qftPairEquiv n (outputHead, outputTail)))
    (qftPhaseLayer_applyVec_pair_ket n inputHead inputTail)
  change
    HilbertOperator.applyVec
        ((qftPhaseLayer n).matrix : HilbertOperator (Qubits (n + 1)))
        (NormalizedVector.ket (R := Qubits (n + 1))
          (qftPairEquiv n (inputHead, inputTail)) :
          HilbertVector (Qubits (n + 1)))
        (qftPairEquiv n (outputHead, outputTail)) = _ at h
  rw [HilbertOperator.applyVec_ket] at h
  have hsmul (c : Complex) (x i : Fin (2 ^ (n + 1))) :
      (c • (NormalizedVector.ket (R := Qubits (n + 1)) x :
        HilbertVector (Qubits (n + 1)))) i =
        c * (if i = x then 1 else 0) := by
    simp [NormalizedVector.ket_apply]
  rw [hsmul] at h
  simpa [Prod.ext_iff, and_comm] using h

/-- One leading QFT stage: Hadamard followed by its diagonal controlled-phase
layer. -/
theorem qftPhaseAfterLeading_matrix_apply_pair (n : Nat)
    (outputHead inputHead : Fin 2)
    (outputTail inputTail : Fin (2 ^ n)) :
    (((qftPhaseLayer n).matrix : HilbertOperator (Qubits (n + 1))) *
        ((qftLeadingHadamard n).matrix : HilbertOperator (Qubits (n + 1))))
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      (if outputHead = 1 then ω (n + 1) ^ outputTail.val else 1) *
        Gate.HOp outputHead inputHead *
          (if outputTail = inputTail then 1 else 0) := by
  rw [Matrix.mul_apply,
    ← Equiv.sum_comp (qftPairEquiv n), Fintype.sum_prod_type]
  rw [Finset.sum_eq_single outputHead]
  · rw [Finset.sum_eq_single outputTail]
    · simp [qftPhaseLayer_matrix_apply_pair,
        qftLeadingHadamard_matrix_apply_pair]
    · intro candidate _ hcandidate
      simp [qftPhaseLayer_matrix_apply_pair, Ne.symm hcandidate]
    · simp
  · intro candidate _ hcandidate
    simp [qftPhaseLayer_matrix_apply_pair, Ne.symm hcandidate]
  · simp

@[simp]
theorem qftPhaseLayerPrefix_physical_idx (n count : Nat) (hcount : count ≤ n) :
    (qftPhaseLayerPrefix n count hcount).physical_idx =
      List.range (n + 1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change UnitaryCircuit.unionPhysicalIdx
          (qftPhaseLayerPrefix n count _).physical_idx
          (qftPhaseStep n ⟨count, _⟩).physical_idx = _
      rw [ih (by omega), show (qftPhaseStep n ⟨count, by omega⟩).physical_idx =
        List.range (n + 1) from qftPrimitiveCircuitAt_physical_idx _]
      exact UnitaryCircuit.unionPhysicalIdx_self _

@[simp]
theorem qftPhaseLayer_physical_idx (n : Nat) :
    (qftPhaseLayer n).physical_idx = List.range (n + 1) :=
  qftPhaseLayerPrefix_physical_idx n n le_rfl



@[simp]
theorem qftPhaseStep_eventCost (n : Nat) (offset : Fin n) :
    (qftPhaseStep n offset).eventCost =
      ResourcePool.singleton (.gate qftControlledPhaseLabel) :=
  rfl

@[simp]
theorem qftPhaseStep_eventDepth (n : Nat) (offset : Fin n) :
    (qftPhaseStep n offset).eventDepth =
      .atom qftControlledPhaseEvent :=
  rfl

theorem qftPhaseLayerPrefix_eventCost (n count : Nat) (hcount : count ≤ n) :
    (qftPhaseLayerPrefix n count hcount).eventCost =
      count • ResourcePool.singleton (.gate qftControlledPhaseLabel) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [qftPhaseLayerPrefix, UnitaryCircuit.seq_eventCost,
        ih (by omega), qftPhaseStep_eventCost, succ_nsmul]

@[simp]
theorem qftPhaseLayer_eventCost (n : Nat) :
    (qftPhaseLayer n).eventCost =
      n • ResourcePool.singleton (.gate qftControlledPhaseLabel) :=
  qftPhaseLayerPrefix_eventCost n n le_rfl

/-- Under unit strict-event durations, the sequential phase prefix has one
layer per addressed controlled phase. -/
theorem qftPhaseLayerPrefix_evaluatedEventDepth_of_one
    (n count : Nat) (hcount : count ≤ n) :
    (qftPhaseLayerPrefix n count hcount).evaluatedEventDepth
        (fun _event => 1) = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [qftPhaseLayerPrefix, UnitaryCircuit.evaluatedEventDepth_seq,
        ih (by omega)]
      simp [UnitaryCircuit.evaluatedEventDepth, qftPhaseStep_eventDepth]

/-- A strict event assignment giving controlled phases unit duration makes the
sequential phase prefix exactly `count` layers deep. -/
theorem qftPhaseLayerPrefix_evaluatedEventDepth
    (n count : Nat) (hcount : count ≤ n)
    (assign : Resource.Event .quantum → Nat)
    (hPhase : assign qftControlledPhaseEvent = 1) :
    (qftPhaseLayerPrefix n count hcount).evaluatedEventDepth assign = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [qftPhaseLayerPrefix, UnitaryCircuit.evaluatedEventDepth_seq,
        ih (by omega)]
      simp [UnitaryCircuit.evaluatedEventDepth, qftPhaseStep_eventDepth, hPhase]

/-- The complete phase layer has one layer per controlled-phase event under any
assignment giving that literal event unit duration. -/
theorem qftPhaseLayer_evaluatedEventDepth (n : Nat)
    (assign : Resource.Event .quantum → Nat)
    (hPhase : assign qftControlledPhaseEvent = 1) :
    (qftPhaseLayer n).evaluatedEventDepth assign = n :=
  qftPhaseLayerPrefix_evaluatedEventDepth n n le_rfl assign hPhase

/-- Under unit strict-event durations, the complete phase layer has depth
exactly the number of controlled-phase leaves. -/
@[simp]
theorem qftPhaseLayer_evaluatedEventDepth_of_one (n : Nat) :
    (qftPhaseLayer n).evaluatedEventDepth (fun _event => 1) = n :=
  qftPhaseLayerPrefix_evaluatedEventDepth_of_one n n le_rfl

/-- Linearizing the phase prefix's strict event-depth tree recovers its exact
event pool. -/
theorem qftPhaseLayerPrefix_resourcesFromEventDepth
    (n count : Nat) (hcount : count ≤ n) :
    (qftPhaseLayerPrefix n count hcount).resourcesFromEventDepth =
      count • ResourcePool.singleton qftControlledPhaseEvent := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    qftPhaseLayerPrefix_eventCost]
  rfl

/-- Linearizing the complete phase layer's strict event-depth tree recovers
its exact event pool. -/
theorem qftPhaseLayer_resourcesFromEventDepth (n : Nat) :
    (qftPhaseLayer n).resourcesFromEventDepth =
      n • ResourcePool.singleton qftControlledPhaseEvent :=
  qftPhaseLayerPrefix_resourcesFromEventDepth n n le_rfl











/-- Embed an `n`-qubit circuit on the lower `n` wires of an `(n+1)`-qubit
register, leaving the leading wire unchanged. -/
def qftTailLayer (n : Nat) (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n) :
    UnitaryCircuit (Qubits (n + 1)) := by
  let leading := UnitaryCircuit.identity (Qubits 1) [0] (by simp)
  let tail := UnitaryCircuit.shiftPhysicalIdx 1 body
  let layout : PhysicalLayout.DisjointMerge leading.physical_idx tail.physical_idx :=
    { left_nodup := leading.physical_idx_nodup
      right_nodup := tail.physical_idx_nodup
      disjoint := by
        rw [show leading.physical_idx = [0] from rfl,
          UnitaryCircuit.shiftPhysicalIdx_physical_idx, hbody]
        simp }
  exact UnitaryCircuit.reindex (qftPairEquiv n)
    (UnitaryCircuit.tensor leading tail layout)

@[simp]
theorem qftTailLayer_physical_idx (n : Nat) (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n) :
    (qftTailLayer n body hbody).physical_idx = List.range (n + 1) := by
  unfold qftTailLayer
  simp only [UnitaryCircuit.reindex, UnitaryCircuit.tensor_physical_idx,
    UnitaryCircuit.shiftPhysicalIdx_physical_idx, hbody]
  change 0 :: List.map (fun index => 1 + index) (List.range n) =
    List.range (n + 1)
  simpa only [Nat.one_add] using (List.range_succ_eq_map (n := n)).symm



@[simp]
theorem qftTailLayer_eventCost (n : Nat) (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n) :
    (qftTailLayer n body hbody).eventCost = body.eventCost := by
  unfold qftTailLayer
  simp

/-- Embedding a tail circuit preserves its strict event-depth tree, in
parallel with the empty leading-wire path. -/
@[simp]
theorem qftTailLayer_eventDepth (n : Nat) (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n) :
    (qftTailLayer n body hbody).eventDepth = .tensor .id body.eventDepth := by
  simp [qftTailLayer]

/-- Tail embedding preserves evaluated strict event depth for every event
duration assignment. -/
theorem qftTailLayer_evaluatedEventDepth (n : Nat)
    (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n)
    (assign : Resource.Event .quantum → Nat) :
    (qftTailLayer n body hbody).evaluatedEventDepth assign =
      body.evaluatedEventDepth assign := by
  simp [UnitaryCircuit.evaluatedEventDepth, qftTailLayer_eventDepth]

/-- Tail embedding preserves the exact strict event pool obtained by
linearizing event depth. -/
theorem qftTailLayer_resourcesFromEventDepth (n : Nat)
    (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n) :
    (qftTailLayer n body hbody).resourcesFromEventDepth = body.eventCost := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    qftTailLayer_eventCost]





@[simp]
theorem qftTailLayer_matrix_apply_pair (n : Nat)
    (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n)
    (outputHead inputHead : Fin 2)
    (outputTail inputTail : Fin (2 ^ n)) :
    (qftTailLayer n body hbody).matrix
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      (if outputHead = inputHead then body.matrix outputTail inputTail else 0) := by
  unfold qftTailLayer
  rw [qftReindexTensor_matrix_apply_pair]
  simp [Matrix.one_apply]

/-- Recursive no-swap QFT circuit.  Each stage performs one leading H, the
controlled phases from the lower input bits, then the recursively compiled
tail circuit. -/
def qftNoSwapCircuitData :
    (n : Nat) → { circuit : UnitaryCircuit (Qubits n) //
      circuit.physical_idx = List.range n }
  | 0 => ⟨UnitaryCircuit.identity (Qubits 0) [] (by simp), rfl⟩
  | n + 1 => by
      let tail := qftNoSwapCircuitData n
      let circuit := UnitaryCircuit.seq (qftLeadingHadamard n)
        (UnitaryCircuit.seq (qftPhaseLayer n) (qftTailLayer n tail.val tail.property))
      refine ⟨circuit, ?_⟩
      have hleading :
          (qftLeadingHadamard n).physical_idx = List.range (n + 1) :=
        qftLeadingHadamard_physical_idx n
      have hphase := qftPhaseLayer_physical_idx n
      have htail := qftTailLayer_physical_idx n tail.val tail.property
      simp only [circuit, UnitaryCircuit.seq, hleading, hphase, htail,
        UnitaryCircuit.unionPhysicalIdx_self]

/-- Structural no-swap QFT circuit. -/
def qftNoSwapCircuit (n : Nat) : UnitaryCircuit (Qubits n) :=
  (qftNoSwapCircuitData n).val

@[simp]
theorem qftNoSwapCircuit_physical_idx (n : Nat) :
    (qftNoSwapCircuit n).physical_idx = List.range n :=
  (qftNoSwapCircuitData n).property



theorem qftNoSwapCircuit_eventCost (n : Nat) :
    (qftNoSwapCircuit n).eventCost =
      n • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        n.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (qftLeadingHadamard n).eventCost +
            ((qftPhaseLayer n).eventCost +
              (qftTailLayer n (qftNoSwapCircuit n)
                (qftNoSwapCircuit_physical_idx n)).eventCost) = _
      rw [qftPhaseLayer_eventCost, qftTailLayer_eventCost, ih]
      change
        ResourcePool.singleton (.gate (.builtin "hadamard")) +
            (n • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
              (n • ResourcePool.singleton (.gate (.builtin "hadamard")) +
                n.choose 2 •
                  ResourcePool.singleton (.gate qftControlledPhaseLabel))) = _
      rw [Nat.choose_succ_succ]
      simp only [show Nat.succ 1 = 2 from rfl, Nat.choose_one_right,
        succ_nsmul]
      rw [add_nsmul]
      abel

/-- The all-one strict event interpreter derives the no-swap QFT path directly
from its Hadamard, phase-layer, and recursive-tail syntax. -/
theorem qftNoSwapCircuit_evaluatedEventDepth_of_one (n : Nat) :
    (qftNoSwapCircuit n).evaluatedEventDepth (fun _event => 1) =
      n + n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (qftLeadingHadamard n).evaluatedEventDepth (fun _event => 1) +
            ((qftPhaseLayer n).evaluatedEventDepth (fun _event => 1) +
              (qftTailLayer n (qftNoSwapCircuit n)
                (qftNoSwapCircuit_physical_idx n)).evaluatedEventDepth
                  (fun _event => 1)) = _
      rw [qftLeadingHadamard_evaluatedEventDepth_of_one,
        qftPhaseLayer_evaluatedEventDepth_of_one,
        qftTailLayer_evaluatedEventDepth, ih]
      simp [Nat.choose_succ_succ, Nat.choose_one_right]
      omega

/-- The no-swap QFT depth formula depends only on unit duration for its literal
Hadamard and controlled-phase events. -/
theorem qftNoSwapCircuit_evaluatedEventDepth (n : Nat)
    (assign : Resource.Event .quantum → Nat)
    (hHadamard : assign qftHadamardEvent = 1)
    (hPhase : assign qftControlledPhaseEvent = 1) :
    (qftNoSwapCircuit n).evaluatedEventDepth assign = n + n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (qftLeadingHadamard n).evaluatedEventDepth assign +
            ((qftPhaseLayer n).evaluatedEventDepth assign +
              (qftTailLayer n (qftNoSwapCircuit n)
                (qftNoSwapCircuit_physical_idx n)).evaluatedEventDepth assign) = _
      rw [qftLeadingHadamard_evaluatedEventDepth n assign hHadamard,
        qftPhaseLayer_evaluatedEventDepth n assign hPhase,
        qftTailLayer_evaluatedEventDepth, ih]
      simp [Nat.choose_succ_succ, Nat.choose_one_right]
      omega

/-- Linearizing the no-swap QFT strict event path recovers its closed event
pool directly. -/
theorem qftNoSwapCircuit_resourcesFromEventDepth (n : Nat) :
    (qftNoSwapCircuit n).resourcesFromEventDepth =
      n • ResourcePool.singleton qftHadamardEvent +
        n.choose 2 • ResourcePool.singleton qftControlledPhaseEvent := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    qftNoSwapCircuit_eventCost]
  rfl





/-- Matrix recurrence of the structural no-swap QFT.  The leading branch is
preserved by the recursive tail block; its phase depends on the lower input
label, and the recursive QFT acts only on that lower label. -/
theorem qftNoSwapCircuit_succ_matrix_apply_pair (n : Nat)
    (outputHead inputHead : Fin 2)
    (outputTail inputTail : Fin (2 ^ n)) :
    (qftNoSwapCircuit (n + 1)).matrix
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      (qftNoSwapCircuit n).matrix outputTail inputTail *
        (if outputHead = 1 then ω (n + 1) ^ inputTail.val else 1) *
          Gate.HOp outputHead inputHead := by
  rw [show qftNoSwapCircuit (n + 1) =
      UnitaryCircuit.seq (qftLeadingHadamard n)
        (UnitaryCircuit.seq (qftPhaseLayer n)
          (qftTailLayer n (qftNoSwapCircuit n)
            (qftNoSwapCircuit_physical_idx n))) from rfl]
  simp only [UnitaryCircuit.seq_matrix]
  rw [mul_assoc]
  rw [Matrix.mul_apply,
    ← Equiv.sum_comp (qftPairEquiv n), Fintype.sum_prod_type]
  rw [Finset.sum_eq_single outputHead]
  · rw [Finset.sum_eq_single inputTail]
    · rw [qftTailLayer_matrix_apply_pair,
        qftPhaseAfterLeading_matrix_apply_pair]
      simp
      ring_nf
    · intro candidate _ hcandidate
      rw [qftTailLayer_matrix_apply_pair,
        qftPhaseAfterLeading_matrix_apply_pair]
      simp [hcandidate]
    · simp
  · intro candidate _ hcandidate
    apply Finset.sum_eq_zero
    intro candidateTail _
    rw [qftTailLayer_matrix_apply_pair]
    simp [Ne.symm hcandidate]
  · simp

/-- Closed matrix formula for the actual recursive no-swap circuit.  Its row
label is bit-reversed because the final symmetric SWAP network has not yet
been applied. -/
theorem qftNoSwapCircuit_matrix_apply (n : Nat)
    (output input : Fin (2 ^ n)) :
    (qftNoSwapCircuit n).matrix output input =
      invSqrtN n *
        ω n ^ ((qftReverseBits n output).val * input.val) := by
  induction n with
  | zero =>
      fin_cases output
      fin_cases input
      norm_num [qftNoSwapCircuit, qftNoSwapCircuitData, invSqrtN]
  | succ n ih =>
      rcases (qftPairEquiv n).surjective output with
        ⟨⟨outputHead, outputTail⟩, rfl⟩
      rcases (qftPairEquiv n).surjective input with
        ⟨⟨inputHead, inputTail⟩, rfl⟩
      rw [qftNoSwapCircuit_succ_matrix_apply_pair, ih,
        qftReverseBits_pair, qftPairEquiv_apply_val, invSqrtN_succ,
        HOp_apply_fin_two]
      calc
        (invSqrtN n *
              ω n ^ ((qftReverseBits n outputTail).val * inputTail.val)) *
            (if outputHead = 1 then
              ω (n + 1) ^ inputTail.val else 1) *
              (invSqrt2 *
                (if outputHead = 1 ∧ inputHead = 1 then -1 else 1)) =
            invSqrt2 * invSqrtN n *
              (ω n ^
                    ((qftReverseBits n outputTail).val * inputTail.val) *
                (if outputHead = 1 then
                  ω (n + 1) ^ inputTail.val else 1) *
                (if outputHead = 1 ∧ inputHead = 1 then -1 else 1)) := by
              ring
        _ = invSqrt2 * invSqrtN n *
              ω (n + 1) ^
                ((2 * (qftReverseBits n outputTail).val + outputHead.val) *
                  (inputTail.val + 2 ^ n * inputHead.val)) := by
              rw [qftOmega_pair_recurrence]

/-- Left wire of the `index`th symmetric bit-reversal swap. -/
def qftSwapLeft (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨index.val, lt_of_lt_of_le index.isLt (Nat.div_le_self n 2)⟩

/-- Right wire of the `index`th symmetric bit-reversal swap. -/
def qftSwapRight (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨n - 1 - index.val, by
    have hi := index.isLt
    omega⟩

theorem qftSwapLeft_ne_right (n : Nat) (index : Fin (n / 2)) :
    qftSwapLeft n index ≠ qftSwapRight n index := by
  intro h
  have hval := congrArg Fin.val h
  have hi := index.isLt
  simp only [qftSwapLeft, qftSwapRight] at hval
  omega

/-- Symmetric wire pair used by the final bit-reversal network. -/
def qftSwapPrimitive (n : Nat) (index : Fin (n / 2)) : QFTPrimitive n :=
  .swap (qftSwapLeft n index) (qftSwapRight n index)
    (qftSwapLeft_ne_right n index)

/-- One full-footprint swap leaf in the bit-reversal network. -/
def qftSwapStep (n : Nat) (index : Fin (n / 2)) : UnitaryCircuit (Qubits n) :=
  qftPrimitiveCircuitAt (qftSwapPrimitive n index)

@[simp]
theorem qftSwapStep_applyVec_ket (n : Nat) (index : Fin (n / 2))
    (label : Fin (2 ^ n)) :
    (qftSwapStep n index).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n)
          (qftSwapLabel (qftSwapLeft n index) (qftSwapRight n index) label) :
        HilbertVector (Qubits n)) := by
  change
    (qftSwapOperator (qftSwapLeft n index) (qftSwapRight n index)
      (qftSwapLeft_ne_right n index)).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) = _
  exact qftSwapOperator_applyVec_ket _ _ _ label

/-- Basis-label action of the first `count` symmetric swaps. -/
def qftBitReverseLabelPrefix (n : Nat) :
    (count : Nat) → count ≤ n / 2 → Fin (2 ^ n) → Fin (2 ^ n)
  | 0, _, label => label
  | count + 1, hcount, label =>
      let index : Fin (n / 2) := ⟨count, by omega⟩
      qftSwapLabel (qftSwapLeft n index) (qftSwapRight n index)
        (qftBitReverseLabelPrefix n count (by omega) label)

/-- First `count` symmetric swaps of the final bit-reversal network. -/
def qftBitReversePrefix (n : Nat) :
    (count : Nat) → count ≤ n / 2 → UnitaryCircuit (Qubits n)
  | 0, _ => UnitaryCircuit.identity (Qubits n) (List.range n) List.nodup_range
  | count + 1, hcount =>
      UnitaryCircuit.seq (qftBitReversePrefix n count (by omega))
        (qftSwapStep n ⟨count, by omega⟩)

theorem qftBitReversePrefix_applyVec_ket (n count : Nat)
    (hcount : count ≤ n / 2) (label : Fin (2 ^ n)) :
    (qftBitReversePrefix n count hcount).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n)
          (qftBitReverseLabelPrefix n count hcount label) :
        HilbertVector (Qubits n)) := by
  induction count with
  | zero => simp [qftBitReversePrefix, qftBitReverseLabelPrefix]
  | succ count ih =>
      rw [qftBitReversePrefix, UnitaryCircuit.applyVec_seq,
        ih (by omega), qftSwapStep_applyVec_ket]
      rfl

/-- After the first `count` symmetric swaps, the outer `count` wires on each
side contain their reversed source bits and every middle wire is unchanged. -/
theorem qftBitReverseLabelPrefix_invariant (n count : Nat)
    (hcount : count ≤ n / 2) (label : Fin (2 ^ n)) :
    (∀ wire : Fin n, wire.val < count →
      (qftBitReverseLabelPrefix n count hcount label).val.testBit
          (WireAddress.bitIndex wire).val = label.val.testBit wire.val) ∧
    (∀ wire : Fin n, n - count ≤ wire.val →
      (qftBitReverseLabelPrefix n count hcount label).val.testBit
          (WireAddress.bitIndex wire).val = label.val.testBit wire.val) ∧
    (∀ wire : Fin n, count ≤ wire.val → wire.val < n - count →
      (qftBitReverseLabelPrefix n count hcount label).val.testBit
          (WireAddress.bitIndex wire).val =
        label.val.testBit (WireAddress.bitIndex wire).val) := by
  induction count with
  | zero =>
      constructor
      · intro wire hwire
        omega
      constructor
      · intro wire hwire
        omega
      · intro wire hleft hright
        rfl
  | succ count ih =>
      obtain ⟨ihLeft, ihRight, ihMiddle⟩ := ih (by omega)
      let index : Fin (n / 2) := ⟨count, by omega⟩
      let left := qftSwapLeft n index
      let right := qftSwapRight n index
      let previous := qftBitReverseLabelPrefix n count (by omega) label
      have hne : left ≠ right := qftSwapLeft_ne_right n index
      have hnext :
          qftBitReverseLabelPrefix n (count + 1) hcount label =
            qftSwapLabel left right previous := rfl
      constructor
      · intro wire hwire
        rw [hnext]
        by_cases hlt : wire.val < count
        · rw [qftSwapLabel_of_ne left right wire hne]
          · exact ihLeft wire hlt
          · intro heq
            have hval := congrArg Fin.val heq
            simp [left, index, qftSwapLeft] at hval
            omega
          · intro heq
            have hval := congrArg Fin.val heq
            have hi := index.isLt
            simp [right, index, qftSwapRight] at hval
            omega
        · have heq : wire = left := by
            apply Fin.ext
            simp [left, index, qftSwapLeft]
            omega
          subst wire
          rw [qftSwapLabel_left left right hne]
          have hmiddle := ihMiddle right (by
            simp [right, index, qftSwapRight]
            omega) (by
            simp [right, index, qftSwapRight]
            omega)
          have hmirror : n - 1 - (n - 1 - count) = count := by
            have hi := index.isLt
            omega
          have hmiddle' :
              previous.val.testBit count = label.val.testBit count := by
            simpa [previous, right, index, qftSwapRight,
              WireAddress.bitIndex, hmirror] using hmiddle
          have hrightMirror :
              (WireAddress.bitIndex right).val = count := by
            simp [right, index, qftSwapRight, WireAddress.bitIndex]
            have hi := index.isLt
            omega
          rw [hrightMirror]
          simpa [left, index, qftSwapLeft] using hmiddle'
      constructor
      · intro wire hwire
        rw [hnext]
        by_cases houter : n - count ≤ wire.val
        · rw [qftSwapLabel_of_ne left right wire hne]
          · exact ihRight wire houter
          · intro heq
            have hval := congrArg Fin.val heq
            have hi := index.isLt
            simp [left, index, qftSwapLeft] at hval
            omega
          · intro heq
            have hval := congrArg Fin.val heq
            simp [right, index, qftSwapRight] at hval
            omega
        · have heq : wire = right := by
            apply Fin.ext
            simp [right, index, qftSwapRight]
            omega
          subst wire
          rw [qftSwapLabel_right left right hne]
          have hmiddle := ihMiddle left (by
            simp [left, index, qftSwapLeft]) (by
            have hi := index.isLt
            simp [left, index, qftSwapLeft]
            omega)
          simpa [left, right, index, qftSwapLeft, qftSwapRight,
            WireAddress.bitIndex] using hmiddle
      · intro wire hleftBound hrightBound
        rw [hnext, qftSwapLabel_of_ne left right wire hne]
        · exact ihMiddle wire (by omega) (by omega)
        · intro heq
          have hval := congrArg Fin.val heq
          simp [left, index, qftSwapLeft] at hval
          omega
        · intro heq
          have hval := congrArg Fin.val heq
          simp [right, index, qftSwapRight] at hval
          omega

/-- The complete symmetric SWAP network realizes the canonical bit-reversal
permutation on computational-basis labels. -/
theorem qftBitReverseLabel_eq (n : Nat) (label : Fin (2 ^ n)) :
    qftBitReverseLabelPrefix n (n / 2) le_rfl label =
      qftReverseBits n label := by
  apply Fin.val_injective
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · let bit : Fin n := ⟨k, hk⟩
    let wire : Fin n := WireAddress.littleEndianWire bit
    obtain ⟨hleft, hright, hmiddle⟩ :=
      qftBitReverseLabelPrefix_invariant n (n / 2) le_rfl label
    have hindex : WireAddress.bitIndex wire = bit := by
      exact WireAddress.bitIndex_littleEndianWire bit
    have hwireRev : wire = Fin.rev bit := by
      apply Fin.ext
      simp [wire, WireAddress.littleEndianWire, WireAddress.bitIndex, Fin.rev]
      omega
    have hvalue :
        (qftBitReverseLabelPrefix n (n / 2) le_rfl label).val.testBit bit.val =
          label.val.testBit wire.val := by
      by_cases hl : wire.val < n / 2
      · simpa only [hindex] using hleft wire hl
      by_cases hr : n - n / 2 ≤ wire.val
      · simpa only [hindex] using hright wire hr
      · have hm := hmiddle wire (by omega) (by omega)
        have hcentral : bit = wire := by
          apply Fin.ext
          have hb := bit.isLt
          have hw := wire.isLt
          have hv := congrArg Fin.val hindex
          simp [WireAddress.bitIndex] at hv
          omega
        simpa only [hindex, hcentral] using hm
    calc
      (qftBitReverseLabelPrefix n (n / 2) le_rfl label).val.testBit k =
          label.val.testBit wire.val := hvalue
      _ = label.val.testBit (Fin.rev bit).val := by rw [hwireRev]
      _ = (qftReverseBits n label).val.testBit k := by
        symm
        simpa [bit] using qftReverseBits_testBit n label bit
  · have hnk : n ≤ k := by omega
    have hpow : 2 ^ n ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hnk
    rw [Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le
          (qftBitReverseLabelPrefix n (n / 2) le_rfl label).isLt hpow),
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (qftReverseBits n label).isLt hpow)]

/-- Final bit-reversal network with exactly `n/2` addressed SWAP leaves. -/
def qftBitReverseCircuit (n : Nat) : UnitaryCircuit (Qubits n) :=
  qftBitReversePrefix n (n / 2) le_rfl

@[simp]
theorem qftBitReverseCircuit_applyVec_ket (n : Nat)
    (label : Fin (2 ^ n)) :
    (qftBitReverseCircuit n).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n) (qftReverseBits n label) :
        HilbertVector (Qubits n)) := by
  rw [qftBitReverseCircuit, qftBitReversePrefix_applyVec_ket,
    qftBitReverseLabel_eq]

/-- The structural SWAP network has exactly the certified bit-reversal
permutation matrix. -/
theorem qftBitReverseCircuit_matrix (n : Nat) :
    (qftBitReverseCircuit n).matrix =
      UnitaryOperator.ofPerm (qftReverseBitsPerm n) := by
  apply Subtype.ext
  ext output input
  have hc := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (qftBitReverseCircuit_applyVec_ket n input)
  have hp := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (UnitaryOperator.ofPerm_applyVec_ket (qftReverseBitsPerm n) input)
  have hinv : (qftReverseBitsPerm n)⁻¹ input = qftReverseBits n input := rfl
  rw [hinv] at hp
  simpa [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket] using hc.trans hp.symm

@[simp]
theorem qftBitReversePrefix_physical_idx (n count : Nat)
    (hcount : count ≤ n / 2) :
    (qftBitReversePrefix n count hcount).physical_idx = List.range n := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change UnitaryCircuit.unionPhysicalIdx
          (qftBitReversePrefix n count _).physical_idx
          (qftSwapStep n ⟨count, _⟩).physical_idx = _
      rw [ih (by omega), show (qftSwapStep n ⟨count, by omega⟩).physical_idx =
        List.range n from qftPrimitiveCircuitAt_physical_idx _]
      exact UnitaryCircuit.unionPhysicalIdx_self _



@[simp]
theorem qftSwapStep_eventCost (n : Nat) (index : Fin (n / 2)) :
    (qftSwapStep n index).eventCost =
      ResourcePool.singleton (.gate (.builtin "swap")) :=
  rfl

@[simp]
theorem qftSwapStep_eventDepth (n : Nat) (index : Fin (n / 2)) :
    (qftSwapStep n index).eventDepth = .atom qftSwapEvent :=
  rfl

theorem qftBitReversePrefix_eventCost (n count : Nat)
    (hcount : count ≤ n / 2) :
    (qftBitReversePrefix n count hcount).eventCost =
      count • ResourcePool.singleton (.gate (.builtin "swap")) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [qftBitReversePrefix, UnitaryCircuit.seq_eventCost,
        ih (by omega), qftSwapStep_eventCost, succ_nsmul]

/-- Unit strict-event durations give one sequential layer per swap in the
bit-reversal prefix. -/
theorem qftBitReversePrefix_evaluatedEventDepth_of_one
    (n count : Nat) (hcount : count ≤ n / 2) :
    (qftBitReversePrefix n count hcount).evaluatedEventDepth
        (fun _event => 1) = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [qftBitReversePrefix, UnitaryCircuit.evaluatedEventDepth_seq,
        ih (by omega)]
      simp [UnitaryCircuit.evaluatedEventDepth, qftSwapStep_eventDepth]

/-- A strict event assignment giving SWAP unit duration makes the sequential
bit-reversal prefix exactly `count` layers deep. -/
theorem qftBitReversePrefix_evaluatedEventDepth
    (n count : Nat) (hcount : count ≤ n / 2)
    (assign : Resource.Event .quantum → Nat)
    (hSwap : assign qftSwapEvent = 1) :
    (qftBitReversePrefix n count hcount).evaluatedEventDepth assign = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [qftBitReversePrefix, UnitaryCircuit.evaluatedEventDepth_seq,
        ih (by omega)]
      simp [UnitaryCircuit.evaluatedEventDepth, qftSwapStep_eventDepth, hSwap]





@[simp]
theorem qftBitReverseCircuit_physical_idx (n : Nat) :
    (qftBitReverseCircuit n).physical_idx = List.range n :=
  qftBitReversePrefix_physical_idx n (n / 2) le_rfl



@[simp]
theorem qftBitReverseCircuit_eventCost (n : Nat) :
    (qftBitReverseCircuit n).eventCost =
      (n / 2) • ResourcePool.singleton (.gate (.builtin "swap")) :=
  qftBitReversePrefix_eventCost n (n / 2) le_rfl

/-- The structural bit-reversal network has all-one strict event depth
`n / 2`. -/
@[simp]
theorem qftBitReverseCircuit_evaluatedEventDepth_of_one (n : Nat) :
    (qftBitReverseCircuit n).evaluatedEventDepth (fun _event => 1) = n / 2 :=
  qftBitReversePrefix_evaluatedEventDepth_of_one n (n / 2) le_rfl

/-- The complete bit-reversal network depends only on unit duration for its
literal SWAP event. -/
theorem qftBitReverseCircuit_evaluatedEventDepth (n : Nat)
    (assign : Resource.Event .quantum → Nat)
    (hSwap : assign qftSwapEvent = 1) :
    (qftBitReverseCircuit n).evaluatedEventDepth assign = n / 2 :=
  qftBitReversePrefix_evaluatedEventDepth n (n / 2) le_rfl assign hSwap

/-- Linearizing the bit-reversal prefix's event path recovers its exact swap
event pool. -/
theorem qftBitReversePrefix_resourcesFromEventDepth
    (n count : Nat) (hcount : count ≤ n / 2) :
    (qftBitReversePrefix n count hcount).resourcesFromEventDepth =
      count • ResourcePool.singleton qftSwapEvent := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    qftBitReversePrefix_eventCost]
  rfl

/-- Linearizing the complete bit-reversal path recovers its exact swap event
pool. -/
theorem qftBitReverseCircuit_resourcesFromEventDepth (n : Nat) :
    (qftBitReverseCircuit n).resourcesFromEventDepth =
      (n / 2) • ResourcePool.singleton qftSwapEvent :=
  qftBitReversePrefix_resourcesFromEventDepth n (n / 2) le_rfl





/-- The structural QFT: recursive Hadamard/controlled-phase layers followed by
the explicit bit-reversal SWAP network. -/
public def QFTCircuit (n : ℕ) : UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.seq (qftNoSwapCircuit n) (qftBitReverseCircuit n)

@[simp]
theorem QFTCircuit_physical_idx (n : ℕ) :
    (QFTCircuit n).physical_idx = List.range n := by
  rw [QFTCircuit, UnitaryCircuit.seq]
  simp [qftNoSwapCircuit_physical_idx, qftBitReverseCircuit_physical_idx,
    UnitaryCircuit.unionPhysicalIdx_self]







/-- Closed strict-event form computed from the actual recursive circuit tree. -/
@[simp]
theorem QFTCircuit_eventCost_eq (n : ℕ) :
    (QFTCircuit n).eventCost =
      n • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        n.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
          (n / 2) • ResourcePool.singleton (.gate (.builtin "swap")) := by
  rw [QFTCircuit, UnitaryCircuit.seq_eventCost,
    qftNoSwapCircuit_eventCost, qftBitReverseCircuit_eventCost]

@[simp]
theorem QFTCircuit_matrix (n : ℕ) :
    (QFTCircuit n).matrix = QFTOperator n := by
  apply Subtype.ext
  ext output input
  rw [QFTCircuit, UnitaryCircuit.seq_matrix, qftBitReverseCircuit_matrix]
  change Matrix.mulVec ((qftReverseBitsPerm n).permMatrix ℂ)
      (fun row => (qftNoSwapCircuit n).matrix row input) output = _
  rw [Matrix.permMatrix_mulVec]
  change (qftNoSwapCircuit n).matrix (qftReverseBits n output) input =
    (QFTOperator n : HilbertOperator (Qubits n)) output input
  rw [qftNoSwapCircuit_matrix_apply, qftReverseBits_involutive,
    QFTOperator_entry]









/-- The strict event interpreter gives the same closed all-one QFT path.
The equality follows directly from the shared sealed circuit tree. -/
theorem QFTCircuit_evaluatedEventDepth_of_one (n : Nat) :
    (QFTCircuit n).evaluatedEventDepth (fun _event => 1) =
      n + n * (n - 1) / 2 + n / 2 := by
  rw [QFTCircuit, UnitaryCircuit.evaluatedEventDepth_seq,
    qftNoSwapCircuit_evaluatedEventDepth_of_one,
    qftBitReverseCircuit_evaluatedEventDepth_of_one,
    Nat.choose_two_right]

/-- Any strict event assignment giving the three literal QFT gate events unit
duration yields the same closed structural critical-path length. -/
theorem QFTCircuit_evaluatedEventDepth (n : Nat)
    (assign : Resource.Event .quantum → Nat)
    (hHadamard : assign qftHadamardEvent = 1)
    (hPhase : assign qftControlledPhaseEvent = 1)
    (hSwap : assign qftSwapEvent = 1) :
    (QFTCircuit n).evaluatedEventDepth assign =
      n + n * (n - 1) / 2 + n / 2 := by
  rw [QFTCircuit, UnitaryCircuit.evaluatedEventDepth_seq,
    qftNoSwapCircuit_evaluatedEventDepth n assign hHadamard hPhase,
    qftBitReverseCircuit_evaluatedEventDepth n assign hSwap,
    Nat.choose_two_right]

/-- Linearizing the QFT strict event path gives the same closed event pool
computed from its circuit syntax. -/
theorem QFTCircuit_resourcesFromEventDepth (n : Nat) :
    (QFTCircuit n).resourcesFromEventDepth =
      n • ResourcePool.singleton qftHadamardEvent +
        n.choose 2 • ResourcePool.singleton qftControlledPhaseEvent +
          (n / 2) • ResourcePool.singleton qftSwapEvent := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    QFTCircuit_eventCost_eq]
  rfl



/-! ### Action on basis kets -/

/-- Component formula for the QFT acting on a basis ket:
`(QFT |x⟩)_i = (1/√N) · ω^{i·x}` [dW19, qcnotes.tex:1692]. -/
theorem QFT_apply_ket (n : ℕ) (x i : Fin (2 ^ n)) :
    UnitaryCircuit.applyNormalized (QFTCircuit n)
        (NormalizedVector.ket (R := Qubits n) x) i =
      invSqrtN n * ω n ^ (i.val * x.val) := by
  change HilbertOperator.applyVec
      ((QFTCircuit n).matrix : HilbertOperator (Qubits n))
      (NormalizedVector.ket (R := Qubits n) x : HilbertVector (Qubits n)) i = _
  rw [QFTCircuit_matrix]
  rw [HilbertOperator.applyVec_ket]
  exact QFTOperator_entry n i x



/-- Exact gate-coordinate multiplicities in the strict event ledger of the
same structural QFT circuit. -/
theorem QFTCircuit_exact_event_gate_counts (n : ℕ) :
    ResourcePool.count (.gate (.builtin "hadamard"))
        (QFTCircuit n).eventCost = n ∧
      ResourcePool.count (.gate qftControlledPhaseLabel)
          (QFTCircuit n).eventCost = n * (n - 1) / 2 ∧
      ResourcePool.count (.gate (.builtin "swap"))
          (QFTCircuit n).eventCost = n / 2 := by
  rw [QFTCircuit_eventCost_eq]
  simp +decide [qftControlledPhaseLabel, Nat.choose_two_right,
    ResourcePool.count, ResourcePool.singleton, Multiset.count_nsmul]

/-- A strict gate coordinate distinct from the three structural QFT
primitives does not occur in the circuit event ledger. -/
theorem QFTCircuit_event_count_eq_zero_of_ne (n : Nat)
    (label : Resource.GateLabel)
    (hHadamard : label ≠ .builtin "hadamard")
    (hPhase : label ≠ qftControlledPhaseLabel)
    (hSwap : label ≠ .builtin "swap") :
    ResourcePool.count (.gate label) (QFTCircuit n).eventCost = 0 := by
  rw [QFTCircuit_eventCost_eq]
  simp only [ResourcePool.count, Multiset.count_add,
    Multiset.count_nsmul]
  simp [ResourcePool.singleton, hHadamard, hPhase, hSwap]



/-- QFT basis action paired with the exact gate-event counts derived from the
same typed circuit. The complete endpoint reuses this construction theorem
without changing its exact basis action or native gate coordinates. -/
public theorem QuantumFourierTransform.basisAction_gateCounts (n : ℕ) (x : Fin (2 ^ n)) :
    (∀ i : Fin (2 ^ n),
      UnitaryCircuit.applyNormalized (QFTCircuit n)
          (NormalizedVector.ket (R := Qubits n) x) i =
        invSqrtN n * ω n ^ (i.val * x.val)) ∧
      (ResourcePool.count (.gate (.builtin "hadamard"))
          (QFTCircuit n).eventCost = n ∧
        ResourcePool.count (.gate qftControlledPhaseLabel)
            (QFTCircuit n).eventCost =
          n * (n - 1) / 2 ∧
        ResourcePool.count (.gate (.builtin "swap"))
          (QFTCircuit n).eventCost = n / 2) := by
  constructor
  · intro i
    exact QFT_apply_ket n x i
  · exact QFTCircuit_exact_event_gate_counts n


end

end QuantumAlg

end
