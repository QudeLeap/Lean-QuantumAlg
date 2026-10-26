/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.Real.Trig.Enclosure
public import QuantumAlg.Util.Rat.OutwardRound
public import QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Rational target intervals for standard Z rotations

The diagonal uses opposite half-angle phases, so the target retains its global
phase. The zero and one dyadic indices have rational sine/cosine values.
The interval branch uses 24 Taylor terms (parameter 20), whose certified
remainder is `2 / 24!`, in addition to the twenty-decimal pi uncertainty.
Endpoints are rounded outward to 64 fractional bits before computing errors.
-/

@[expose] public section

namespace QuantumAlg.CliffordT.Checker

open Gate

/-- Half of the dyadic rotation angle. -/
noncomputable def halfAngle (j : ℕ) : ℝ := 2 * Real.pi / 2 ^ (j + 1)

/-- Lower real coordinate of each diagonal target entry. -/
def cosLower (j : ℕ) : ℚ :=
  if j = 0 then -1 else if j = 1 then 0 else
    RationalBounds.roundDown (TrigEnclosure.cosLo (j + 1) 20)

/-- Upper real coordinate of each diagonal target entry. -/
def cosUpper (j : ℕ) : ℚ :=
  if j = 0 then -1 else if j = 1 then 0 else
    RationalBounds.roundUp (TrigEnclosure.cosHi (j + 1) 20)

/-- Lower sine coordinate of the positive half-angle phase. -/
def sinLower (j : ℕ) : ℚ :=
  if j = 0 then 0 else if j = 1 then 1 else
    RationalBounds.roundDown (TrigEnclosure.sinLo (j + 1) 20)

/-- Upper sine coordinate of the positive half-angle phase. -/
def sinUpper (j : ℕ) : ℚ :=
  if j = 0 then 0 else if j = 1 then 1 else
    RationalBounds.roundUp (TrigEnclosure.sinHi (j + 1) 20)

lemma target_cos_bounds (j : ℕ) :
    (cosLower j : ℝ) ≤ Real.cos (halfAngle j) ∧
      Real.cos (halfAngle j) ≤ (cosUpper j : ℝ) := by
  by_cases h0 : j = 0
  · subst j
    norm_num [cosLower, cosUpper, halfAngle]
  by_cases h1 : j = 1
  · subst j
    norm_num [cosLower, cosUpper, halfAngle, show (2 : ℝ) * Real.pi / 4 = Real.pi / 2 by ring]
  simp only [cosLower, cosUpper, if_neg h0, if_neg h1, halfAngle]
  constructor
  · apply le_trans _ (TrigEnclosure.cosLo_le_cos (j + 1) 20 (by omega))
    exact_mod_cast RationalBounds.roundDown_le (TrigEnclosure.cosLo (j + 1) 20)
  · apply le_trans (TrigEnclosure.cos_le_cosHi (j + 1) 20 (by omega))
    exact_mod_cast RationalBounds.le_roundUp (TrigEnclosure.cosHi (j + 1) 20)

lemma target_sin_bounds (j : ℕ) :
    (sinLower j : ℝ) ≤ Real.sin (halfAngle j) ∧
      Real.sin (halfAngle j) ≤ (sinUpper j : ℝ) := by
  by_cases h0 : j = 0
  · subst j
    norm_num [sinLower, sinUpper, halfAngle]
  by_cases h1 : j = 1
  · subst j
    norm_num [sinLower, sinUpper, halfAngle, show (2 : ℝ) * Real.pi / 4 = Real.pi / 2 by ring]
  simp only [sinLower, sinUpper, if_neg h0, if_neg h1, halfAngle]
  constructor
  · apply le_trans _ (TrigEnclosure.sinLo_le_sin (j + 1) 20 (by omega))
    exact_mod_cast RationalBounds.roundDown_le (TrigEnclosure.sinLo (j + 1) 20)
  · apply le_trans (TrigEnclosure.sin_le_sinHi (j + 1) 20 (by omega))
    exact_mod_cast RationalBounds.le_roundUp (TrigEnclosure.sinHi (j + 1) 20)

/-- Explicit target matrix with both standard rotation phases. -/
noncomputable def targetMatrix (j : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => if i = k then (Real.cos (halfAngle j) : ℂ) +
    Complex.I * (if i = 0 then -(Real.sin (halfAngle j) : ℂ) else Real.sin (halfAngle j))
    else 0

lemma targetMatrix_eq_rotZStdOp (j : ℕ) :
    targetMatrix j = (rotZStdOp (2 * Real.pi / 2 ^ j) : HilbertOperator (Qubits 1)) := by
  have ha : (2 * Real.pi / 2 ^ j) / 2 = halfAngle j := by
    unfold halfAngle
    rw [pow_succ]
    ring
  simp only [rotZStdOp]
  rw [ha]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp only [targetMatrix, Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one,
      one_ne_zero, ↓reduceIte, Complex.ofReal_cos, Complex.ofReal_sin, mul_neg,
      Nat.reducePow, rotZOp, Complex.ofReal_neg, neg_mul, neg_neg,
      UnitaryOperator.coe_ofMatrix, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · conv_rhs => rw [← neg_mul, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg]
    ring
  · rw [Complex.exp_mul_I]
    ring

end QuantumAlg.CliffordT.Checker
