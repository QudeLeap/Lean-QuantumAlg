/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ExecutionState
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Finite classical random choices

An independent uniform classical choice divides each existing branch's mass
equally among its finite outcomes. It preserves the complete quantum block
up to that probability factor. This is the internal interpretation of a
classical random-bit instruction; it introduces no measurement or quantum gate.
-/

namespace QuantumAlg.Execution

open scoped ComplexOrder

noncomputable section

private def divideMass {R : Register} (state : DensityOperator R) (count : ℕ+) :
    DensityOperator R where
  matrix := ((count : ℝ)⁻¹) • state.matrix
  positive := state.positive.smul (inv_nonneg.mpr (Nat.cast_nonneg (count : Nat)))
  trace_le_one := by
    simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    calc
      (count : ℝ)⁻¹ * state.matrix.trace.re ≤ (count : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left state.trace_le_one
          (inv_nonneg.mpr (Nat.cast_nonneg (count : Nat)))
      _ = (count : ℝ)⁻¹ := mul_one _
      _ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast count.pos)

private lemma divideMass_mass {R : Register} (state : DensityOperator R) (count : ℕ+) :
    (divideMass state count).mass = (count : ℝ)⁻¹ * state.mass := by
  simp only [DensityOperator.mass, divideMass, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul]

private lemma sum_divideMass_mass {R : Register}
    (state : DensityOperator R) (count : ℕ+) :
    ∑ _value : Fin count, (divideMass state count).mass = state.mass := by
  have positive : (0 : ℝ) < count := by exact_mod_cast count.pos
  simp only [divideMass_mass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt positive), one_mul]

/-- Attach an independent uniform finite classical value to every existing block. -/
def uniformChoice {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) : ExecutionState (C × Fin count) R where
  block result := divideMass (state.block result.1) count
  total_le_one := by
    rw [Fintype.sum_prod_type]
    simp only [sum_divideMass_mass]
    exact state.total_le_one

/-- Each joint outcome retains exactly one equal fraction of its original quantum block. -/
lemma uniformChoice_block_matrix {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) (value : C) (outcome : Fin count) :
    ((uniformChoice state count).block (value, outcome)).matrix =
      ((count : ℝ)⁻¹) • (state.block value).matrix := rfl

/-- The classical random choice preserves total execution probability. -/
lemma uniformChoice_mass {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) :
    (uniformChoice state count).mass = state.mass := by
  change (∑ result : C × Fin count, (divideMass (state.block result.1) count).mass) = _
  rw [Fintype.sum_prod_type]
  simp only [sum_divideMass_mass, ExecutionState.mass]

end

end QuantumAlg.Execution
