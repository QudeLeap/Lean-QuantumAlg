/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Pauli propagation: the truncation-error bound

Pauli propagation evolves an observable in the Heisenberg picture as a vector of Pauli
coefficients and, to stay efficient, truncates low-coefficient / high-weight terms layer by
layer. Theory Box 3 of [RJT+25, main.tex:1026] bounds the **total** simulation error by
the **sum of the per-layer discarded `ℓ¹`-norms**: `Δ ≤ Δ_L + ⋯ + Δ_1`.

This module builds a concrete coefficient-vector model and proves a telescoping `ℓ¹` truncation
bound in the spirit of Eq. (32):

* a Pauli-coefficient vector `c : K → ℝ` over a finite key type `K`, with `ℓ¹` norm
  `l1 c = ∑ k, |c k|`;
* a per-layer Heisenberg evolution `evolve ℓ`, taken as a **named hypothesis** to be
  `ℓ¹`-nonexpansive on differences (`l1 (evolve ℓ a − evolve ℓ b) ≤ l1 (a − b)`), and a per-layer
  truncation `trunc ℓ`;
* the exact and truncated trajectories `exactState` / `truncState`, the per-layer discarded
  mass `discarded ℓ`, and the **telescoping bound** `truncation_error_le`, proved by induction
  via the `ℓ¹` triangle inequality.

**Scope / faithfulness caveat.** The source's Eq. (32) bounds the *expectation-value* error
`|Tr[(O_L − C†(O)) ρ]|` by the discarded `ℓ¹`-masses. Here we prove the closely related
*coefficient-vector* `ℓ¹` distance `‖exactState − truncState‖₁ ≤ Σ Δ_n` (from which the
expectation-value bound follows by Hölder), and the `ℓ¹`-nonexpansiveness `hne` is an *assumption*
on `evolve` — it holds for (sub-)stochastic Pauli-transfer maps but is **not** automatic for a
general Heisenberg layer. Discharging `hne` for a concrete circuit family is left as future work.

Source: [RJT+25, main.tex:1026], *Pauli Propagation* (arXiv:2505.21606), Theory Box 3. (The
Monte-Carlo error estimate and tree-search structure are out of scope here.)
-/

@[expose] public section

namespace QuantumAlg

open scoped BigOperators

variable {K : Type*} [Fintype K]

/-- The `ℓ¹` norm of a Pauli-coefficient vector. -/
def l1 (x : K → ℝ) : ℝ := ∑ k, |x k|

theorem l1_nonneg (x : K → ℝ) : 0 ≤ l1 x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_sub_self (x : K → ℝ) : l1 (x - x) = 0 := by simp [l1]

/-- The `ℓ¹` triangle inequality (through an intermediate point). -/
theorem l1_sub_le (a b c : K → ℝ) : l1 (a - c) ≤ l1 (a - b) + l1 (b - c) := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.sub_apply]
  rw [show a k - c k = (a k - b k) + (b k - c k) from by ring]
  exact abs_add_le _ _

/-- The exact Heisenberg trajectory after `n` layers (no truncation). -/
def exactState (init : K → ℝ) (evolve : ℕ → (K → ℝ) → (K → ℝ)) : ℕ → (K → ℝ)
  | 0 => init
  | n + 1 => evolve n (exactState init evolve n)

/-- The truncated trajectory after `n` layers (evolve then truncate at each layer). -/
def truncState (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ)) : ℕ → (K → ℝ)
  | 0 => init
  | n + 1 => trunc n (evolve n (truncState init evolve trunc n))

/-- The `ℓ¹` mass discarded by the truncation at layer `n` (along the truncated trajectory):
`Δ_n = ‖evolve n (truncState n) − trunc n (evolve n (truncState n))‖₁`. -/
def discarded (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ)) (n : ℕ) : ℝ :=
  l1 (evolve n (truncState init evolve trunc n)
        - trunc n (evolve n (truncState init evolve trunc n)))

theorem discarded_nonneg (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ)) (n : ℕ) :
    0 ≤ discarded init evolve trunc n := l1_nonneg _

/-- **Coefficient-vector truncation-error bound — models [RJT+25, main.tex:1026] Eq. (32).** Under
the named hypothesis `hne` that each layer's Heisenberg evolution is `ℓ¹`-nonexpansive on
differences, the total coefficient-vector `ℓ¹` error after `L` layers is bounded by the sum of the
per-layer discarded `ℓ¹`-norms. Proved by induction via the `ℓ¹` triangle inequality and the
nonexpansiveness of subsequent layers (telescoping). The source's expectation-value form follows by
Hölder; see the module-level faithfulness caveat on `hne`. -/
theorem truncation_error_le (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ))
    (hne : ∀ n a b, l1 (evolve n a - evolve n b) ≤ l1 (a - b)) (L : ℕ) :
    l1 (exactState init evolve L - truncState init evolve trunc L)
      ≤ ∑ n ∈ Finset.range L, discarded init evolve trunc n := by
  induction L with
  | zero => simp [exactState, truncState, l1]
  | succ L ih =>
    have key :
        l1 (exactState init evolve (L + 1) - truncState init evolve trunc (L + 1))
          ≤ l1 (exactState init evolve L - truncState init evolve trunc L)
            + discarded init evolve trunc L := by
      change l1 (evolve L (exactState init evolve L)
            - trunc L (evolve L (truncState init evolve trunc L))) ≤ _
      calc l1 (evolve L (exactState init evolve L)
              - trunc L (evolve L (truncState init evolve trunc L)))
          ≤ l1 (evolve L (exactState init evolve L) - evolve L (truncState init evolve trunc L))
              + l1 (evolve L (truncState init evolve trunc L)
                  - trunc L (evolve L (truncState init evolve trunc L))) :=
            l1_sub_le _ _ _
        _ ≤ l1 (exactState init evolve L - truncState init evolve trunc L)
              + discarded init evolve trunc L :=
            add_le_add (hne L _ _) le_rfl
    calc l1 (exactState init evolve (L + 1) - truncState init evolve trunc (L + 1))
        ≤ l1 (exactState init evolve L - truncState init evolve trunc L)
            + discarded init evolve trunc L := key
      _ ≤ (∑ n ∈ Finset.range L, discarded init evolve trunc n)
            + discarded init evolve trunc L := by linarith [ih]
      _ = ∑ n ∈ Finset.range (L + 1), discarded init evolve trunc n :=
          (Finset.sum_range_succ _ L).symm

/-- The error bound (sum of discarded norms) is nonnegative. -/
theorem truncation_error_bound_nonneg (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ))
    (L : ℕ) : 0 ≤ ∑ n ∈ Finset.range L, discarded init evolve trunc n :=
  Finset.sum_nonneg fun n _ => discarded_nonneg init evolve trunc n

/-- **Exact propagation incurs no error.** If nothing is discarded at any layer, the truncated
trajectory equals the exact one (zero error). -/
theorem truncation_error_exact (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ))
    (hne : ∀ n a b, l1 (evolve n a - evolve n b) ≤ l1 (a - b)) (L : ℕ)
    (h : ∀ n, discarded init evolve trunc n = 0) :
    l1 (exactState init evolve L - truncState init evolve trunc L) = 0 := by
  refine le_antisymm ?_ (l1_nonneg _)
  refine (truncation_error_le init evolve trunc hne L).trans ?_
  rw [Finset.sum_congr rfl fun n _ => h n, Finset.sum_const_zero]

end QuantumAlg
