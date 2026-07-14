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

This module builds a concrete coefficient-vector model and proves the telescoping truncation bound
in three forms:

* a Pauli-coefficient vector `c : K → ℝ` over a finite key type `K`, with `ℓ¹` norm
  `l1 c = ∑ k, |c k|`;
* a per-layer Heisenberg evolution `evolve ℓ`, taken as a **named hypothesis** to be
  `ℓ¹`-nonexpansive on differences (`l1 (evolve ℓ a − evolve ℓ b) ≤ l1 (a − b)`), and a per-layer
  truncation `trunc ℓ`;
* the exact and truncated trajectories `exactState` / `truncState`, the per-layer discarded
  mass `discarded ℓ`, and the **coefficient-vector telescoping bound** `truncation_error_le`,
  proved by induction via the `ℓ¹` triangle inequality;
* the **substochastic expectation-value bound** `expectation_truncation_error_le`: for any
  measurement weight `w` with `|w k| ≤ 1` (`w k = Tr[ρ P_k]`), the expectation-value error
  `|Tr[(O_L − C†(O)) ρ]|` is bounded by the same sum of discarded masses, obtained from the
  coefficient bound by the Hölder step `abs_trace_overlap_le`; it inherits the substochastic
  layer hypothesis `hne` from the coefficient bound;
* the **transported-weight Eq. (32) bound** `expectation_truncation_error_transport_le`: if
  weights `v n` are transported backward through the layers
  `∑ k, evolve n a k * v (n + 1) k = ∑ k, a k * v n k` and satisfy `|v n k| ≤ 1`, then the same
  expectation-value error is bounded by the sum of discarded masses with no `hne` / `ℓ¹`
  propagation / substochastic-layer hypothesis. This is the per-layer scalar-Hölder argument in
  Theory Box 3.

**Scope of the nonexpansiveness hypothesis.** The coefficient and fixed-weight substochastic
endpoints are stated under the named hypothesis `hne` that each layer is `ℓ¹`-nonexpansive on
differences. This is a *substochastic* condition: it holds for Clifford /
signed-Pauli-permutation layers (`ℓ¹`-isometries) and for `ℓ¹`-contractions, but **fails** for a
general rotation layer — a single `R_Z(θ)` sends `X`'s coefficient vector to `(cos 2θ, sin 2θ)` on
`(X, Y)`, whose `ℓ¹`-mass reaches `√2 > 1` (the source conserves the `2`-norm, not the `1`-norm).
`pauli_propagation_substochastic_witness` exhibits a concrete Clifford `ℓ¹`-isometry that discharges
`hne` with strictly positive discarded mass, so the hypothesis — and the expectation-value bound
built on it — is satisfiable and non-vacuous.

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

/-- **Hölder / ℓ∞–ℓ¹ overlap bound.** A weighted coefficient sum against a
weight of sup-norm at most
one (`|w k| ≤ 1`) is bounded by the `ℓ¹` norm of the coefficients. With `w k = Tr[ρ P_k]` — every
Pauli expectation has magnitude at most one — this is the Hölder step that turns a coefficient-`ℓ¹`
bound into an expectation-value bound. -/
theorem abs_trace_overlap_le (a w : K → ℝ) (hw : ∀ k, |w k| ≤ 1) :
    |∑ k, a k * w k| ≤ l1 a := by
  unfold l1
  refine (Finset.abs_sum_le_sum_abs (fun k => a k * w k) Finset.univ).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hw k)

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

/-- **Coefficient-vector truncation-error bound (substochastic layers).** Under the named hypothesis
`hne` that each layer's Heisenberg evolution is `ℓ¹`-nonexpansive on differences (a substochastic
condition — see the module docstring), the total coefficient-vector `ℓ¹` error after `L` layers is
bounded by the sum of the per-layer discarded `ℓ¹`-norms. Proved by induction via the `ℓ¹` triangle
inequality and the nonexpansiveness of subsequent layers (telescoping). The Eq. (32)-form
expectation-value corollary (under the same substochastic hypothesis) is
`expectation_truncation_error_le`, obtained from this bound by the Hölder step
`abs_trace_overlap_le`. -/
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

/-- **Expectation-value truncation-error bound in the [RJT+25, main.tex:1026] Eq. (32) form,
restricted to substochastic layers.** For any measurement weight `w` with `|w k| ≤ 1` (the
coefficient-space image of `w k = Tr[ρ P_k]`, since every Pauli expectation has magnitude at most
one), the expectation-value error `|Tr[(O_L − C†(O)) ρ]| = |⟨O⟩_exact − ⟨O⟩_trunc|` after `L`
substochastic / `ℓ¹`-nonexpansive layers is bounded by the same sum of per-layer discarded
`ℓ¹`-masses. Composes the Hölder step `abs_trace_overlap_le` with the coefficient-vector bound
`truncation_error_le`, and therefore inherits its `hne` hypothesis. For the Eq. (32) bound that uses
transported dual weights instead of `ℓ¹` propagation, see
`expectation_truncation_error_transport_le`. -/
theorem expectation_truncation_error_le
    (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ))
    (hne : ∀ n a b, l1 (evolve n a - evolve n b) ≤ l1 (a - b))
    (w : K → ℝ) (hw : ∀ k, |w k| ≤ 1) (L : ℕ) :
    |(∑ k, exactState init evolve L k * w k)
        - (∑ k, truncState init evolve trunc L k * w k)|
      ≤ ∑ n ∈ Finset.range L, discarded init evolve trunc n := by
  have hlin :
      (∑ k, exactState init evolve L k * w k)
          - (∑ k, truncState init evolve trunc L k * w k)
        = ∑ k, (exactState init evolve L - truncState init evolve trunc L) k * w k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.sub_apply, sub_mul]
  rw [hlin]
  exact (abs_trace_overlap_le _ w hw).trans
    (truncation_error_le init evolve trunc hne L)

/-- **Expectation-value truncation-error bound with transported dual weights.** This is the
coefficient-space version of the [RJT+25, main.tex:1020-1030] Theory Box 3 / Eq. (32) argument.
If the dual weights `v n` are transported backward through every Heisenberg layer (`evolve n`) and
have sup-norm at most one, then the final expectation-value error is bounded by the sum of the
per-layer discarded `ℓ¹` masses. The proof does not assume `hne`, `ℓ¹` propagation, or a
substochastic-layer condition; the load-bearing assumptions are exactly the scalar transport law
and the bound `|v n k| ≤ 1`. -/
theorem expectation_truncation_error_transport_le
    (init : K → ℝ) (evolve trunc : ℕ → (K → ℝ) → (K → ℝ))
    (v : ℕ → K → ℝ)
    (htransport : ∀ n a,
      (∑ k, evolve n a k * v (n + 1) k) = ∑ k, a k * v n k)
    (hv : ∀ n k, |v n k| ≤ 1) (L : ℕ) :
    |(∑ k, exactState init evolve L k * v L k)
        - (∑ k, truncState init evolve trunc L k * v L k)|
      ≤ ∑ n ∈ Finset.range L, discarded init evolve trunc n := by
  induction L with
  | zero => simp [exactState, truncState]
  | succ L ih =>
    let A : ℝ := ∑ k, evolve L (exactState init evolve L) k * v (L + 1) k
    let C : ℝ := ∑ k, evolve L (truncState init evolve trunc L) k * v (L + 1) k
    let B : ℝ :=
      ∑ k, trunc L (evolve L (truncState init evolve trunc L)) k * v (L + 1) k
    have hprev : |A - C| ≤ ∑ n ∈ Finset.range L, discarded init evolve trunc n := by
      dsimp [A, C]
      rw [htransport L (exactState init evolve L),
        htransport L (truncState init evolve trunc L)]
      exact ih
    have hdiscard : |C - B| ≤ discarded init evolve trunc L := by
      have hlin :
          C - B =
            ∑ k, (evolve L (truncState init evolve trunc L)
              - trunc L (evolve L (truncState init evolve trunc L))) k * v (L + 1) k := by
        dsimp [C, B]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← sub_mul]
      rw [hlin]
      exact abs_trace_overlap_le _ (v (L + 1)) (hv (L + 1))
    have htri : |A - B| ≤ |A - C| + |C - B| := by
      rw [show A - B = (A - C) + (C - B) by ring]
      exact abs_add_le _ _
    change |A - B| ≤ ∑ n ∈ Finset.range (L + 1), discarded init evolve trunc n
    calc
      |A - B| ≤ |A - C| + |C - B| := htri
      _ ≤ (∑ n ∈ Finset.range L, discarded init evolve trunc n)
            + discarded init evolve trunc L := add_le_add hprev hdiscard
      _ = ∑ n ∈ Finset.range (L + 1), discarded init evolve trunc n :=
          (Finset.sum_range_succ _ L).symm

/-- A one-qubit phase-gate Clifford signed swap on the `(X, Y)`
Pauli-coefficient subspace, acting as
`X ↦ Y`, `Y ↦ −X` (coefficients `(a₀, a₁) ↦ (−a₁, a₀)`): a per-layer Heisenberg evolution that is an
exact `ℓ¹`-isometry. -/
private def ppCliffordLayer : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun _ x => ![-(x 1), x 0]

/-- The truncation keeping only the first coordinate (discarding the second). -/
private def ppKeepFirstTrunc : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun _ x => ![x 0, 0]

/-- The initial coefficient vector `X` (first basis coordinate). -/
private def ppWitnessInit : Fin 2 → ℝ := ![1, 0]

/-- **The nonexpansiveness hypothesis is satisfiable — by a substochastic
layer.** A concrete Clifford
`ℓ¹`-isometric layer (a phase-gate Clifford signed swap acting as `X ↦ Y`, `Y ↦ −X` on the `(X, Y)`
Pauli-coefficient subspace) discharges the load-bearing hypothesis `hne` (it holds with equality),
while keeping only the first coordinate discards strictly positive `ℓ¹`-mass — so the truncation is
non-trivial and the expectation-value bound `expectation_truncation_error_le` is
non-vacuous here. The
witness is necessarily substochastic: a non-Clifford rotation `R_Z(θ)` sends
`X`'s coefficient vector
to `(cos 2θ, sin 2θ)` on `(X, Y)` with `ℓ¹`-mass up to `√2`, so `hne` cannot hold for a general
rotation layer. -/
theorem pauli_propagation_substochastic_witness :
    ∃ (init : Fin 2 → ℝ) (evolve trunc : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ)),
      (∀ n a b, l1 (evolve n a - evolve n b) ≤ l1 (a - b)) ∧
      0 < discarded init evolve trunc 0 ∧
      (∀ w : Fin 2 → ℝ, (∀ k, |w k| ≤ 1) → ∀ L,
        |(∑ k, exactState init evolve L k * w k)
           - (∑ k, truncState init evolve trunc L k * w k)|
          ≤ ∑ n ∈ Finset.range L, discarded init evolve trunc n) := by
  have hne : ∀ n a b,
      l1 (ppCliffordLayer n a - ppCliffordLayer n b) ≤ l1 (a - b) := by
    intro n a b
    simp only [l1, ppCliffordLayer, Fin.sum_univ_two, Pi.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show -(a 1) - -(b 1) = -(a 1 - b 1) from by ring, abs_neg]
    exact le_of_eq (add_comm _ _)
  refine ⟨ppWitnessInit, ppCliffordLayer, ppKeepFirstTrunc, hne, ?_, ?_⟩
  · norm_num [discarded, truncState, ppWitnessInit, ppCliffordLayer, ppKeepFirstTrunc,
      l1, Fin.sum_univ_two, Pi.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · intro w hw L
    exact expectation_truncation_error_le
      ppWitnessInit ppCliffordLayer ppKeepFirstTrunc hne w hw L

end QuantumAlg
