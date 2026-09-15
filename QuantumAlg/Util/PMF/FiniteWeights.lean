/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.PMF
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Complex.BigOperators

/-!
# Finite complex weights of existing probability mass functions

The ordinary PMF map and bind operations transport finite complex weights by
their exact point probabilities. Characteristic weights recover the original
point mass. These identities concern finite probability alone and contain no
execution state or additional sampling construction.
-/

namespace QuantumAlg.PMF

noncomputable section

variable {A B : Type} [Fintype A] [Fintype B]

/-- A finite deterministic pushforward transports each complex weight to its original value. -/
theorem sum_map_toReal_mul (distribution : PMF A) (map : A → B) (weight : B → ℂ) :
    (∑ value : B, ((distribution.map map value).toReal : ℂ) * weight value) =
      ∑ original : A, ((distribution original).toReal : ℂ) * weight (map original) := by
  classical
  have point (value : B) : (distribution.map map value).toReal =
      ∑ original : A, if value = map original then (distribution original).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp only [apply_ite, ENNReal.toReal_zero]
    · intro original _
      split
      · exact distribution.apply_ne_top original
      · exact ENNReal.zero_ne_top
  simp_rw [point]
  simp only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, Finset.sum_mul,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Finite conditional sampling sums the original and conditional weights without approximation. -/
theorem sum_bind_toReal_mul (distribution : PMF A) (conditional : A → PMF B)
    (weight : B → ℂ) :
    (∑ value : B, ((distribution.bind conditional value).toReal : ℂ) * weight value) =
      ∑ original : A, ((distribution original).toReal : ℂ) *
        ∑ value : B, ((conditional original value).toReal : ℂ) * weight value := by
  have point (value : B) : (distribution.bind conditional value).toReal =
      ∑ original : A, (distribution original).toReal * (conditional original value).toReal := by
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
    · intro original _
      exact ENNReal.mul_ne_top (distribution.apply_ne_top original)
        ((conditional original).apply_ne_top value)
  simp_rw [point]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

/-- The exact finite characteristic weight is the original PMF's point probability. -/
theorem sum_toReal_indicator (distribution : PMF A) [DecidableEq A] (selected : A) :
    (∑ value : A, ((distribution value).toReal : ℂ) *
      (if value = selected then 1 else 0)) = ((distribution selected).toReal : ℂ) := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

end QuantumAlg.PMF
