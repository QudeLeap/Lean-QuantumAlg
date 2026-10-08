/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
public import QuantumAlg.Core.Base.State.Pure
public import QuantumAlg.Components.Kets
public import Mathlib.Data.Fintype.Card
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Range-uniform state for the known-order experiment

This is the mathematical target of the native Shukla--Vedula preparation.
It is independent of the gate model: every basis label below the known order
has the same amplitude, and every unused label in the reviewed power-of-two
register has zero amplitude.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderPreparation

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Reciprocal square-root amplitude of a positive finite order. -/
@[expose] public def invSqrtOrder (order : Nat) : ℂ :=
  (Real.sqrt (order : ℝ) : ℂ)⁻¹

public theorem norm_sq_invSqrtOrder {order : Nat} (positive : 0 < order) :
    ‖invSqrtOrder order‖ ^ 2 = ((order : ℝ)⁻¹) := by
  rw [invSqrtOrder, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (order : ℝ))]

/-- Exact normalized range-uniform state in the reviewed exponent register. -/
public def state (P : KnownOrderProblem G) : NormalizedVector (Qubits (width P)) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun index =>
      if index.val < P.order then invSqrtOrder P.order else 0)
    (by
      rw [EuclideanSpace.norm_eq]
      have sum_norms :
          ∑ index : Fin (2 ^ width P),
              ‖if index.val < P.order then invSqrtOrder P.order else 0‖ ^ 2 = 1 := by
        simp_rw [apply_ite, ite_pow, norm_zero,
          zero_pow (by omega : 2 ≠ 0)]
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, Fin.card_filter_val_lt,
          min_eq_right (order_le_capacity P), nsmul_eq_mul,
          norm_sq_invSqrtOrder (Nat.pos_of_ne_zero P.order_ne_zero)]
        exact div_self (by exact_mod_cast P.order_ne_zero)
      rw [sum_norms, Real.sqrt_one])

private theorem state_apply_internal (P : KnownOrderProblem G)
    (index : Fin (2 ^ width P)) :
    state P index =
      if index.val < P.order then invSqrtOrder P.order else 0 :=
  rfl

@[simp] public theorem state_apply (P : KnownOrderProblem G)
    (index : Fin (2 ^ width P)) :
    state P index =
      if index.val < P.order then invSqrtOrder P.order else 0 :=
  state_apply_internal P index

end


end QuantumAlg.FiniteCyclicDLP.OrderPreparation
