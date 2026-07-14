/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.QuantumFisher
public import QuantumAlg.Primitives.QNN.Core.LieAlgebraicBP

/-!
# The QFIM-rank-saturation definition of QNN overparametrization (Larocca Def. 1)

The rigorous overparametrization *predicate* for a quantum neural network, built on the genuine
Quantum Fisher Information Matrix (`QuantumAlg.qfim`) rather than an opaque `ℕ → ℕ` field.

For a training set indexed by `μ`, the **achievable QFIM rank** at parameter
count `M` is the supremum
of the rank over the loss landscape, and its **saturated** value is the supremum over `M`:
`R_μ(M) = ⨆_θ rank[F_μ(M,θ)]`, `R_μ = ⨆_M R_μ(M)`. The QNN is **overparametrized at `M`** iff every
training state has saturated: `∀ μ, R_μ(M) = R_μ` (Larocca et al. 2021, Def. 1).

The QFIM family and the two deep inputs are bundled as an `OverparamData` interface:
* `rank_le_dlaDim` — Larocca **Theorem 1** ceiling `rank[F] ≤ dim g` (the named analytic hypothesis,
  dischargeable against the genuine QFIM rank bound `qfim_rank_le_dlaDim`);
* `pad_block` — the parameter-padding block structure that makes the achievable rank monotone.

The supremum constructions carry explicit `BddAbove` obligations: the per-`M` sup is finite via
`rank ≤ M`, and the saturated sup is finite via the Theorem-1 ceiling — without
which the `ℕ`-indexed
`⨆` is junk-valued.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ}

/-- **Training-set-indexed QFIM data** for the overparametrization predicate
(Larocca Def. 1). `F μ M θ`
is the real QFIM at training state `μ`, parameter count `M`, parameters `θ`. The
bundled hypotheses are
the Theorem-1 ceiling (`rank ≤ dim g`, tied to the genuine QFIM) and the parameter-padding block
structure (freezing the new parameter to `0` exhibits `F μ M θ` as the top-left
block of `F μ (M+1) _`). -/
structure OverparamData (gens : Set (Matrix (Fin N) (Fin N) ℂ)) where
  /-- The training-set index type. -/
  ι : Type
  /-- The training set is finite. -/
  fι : Fintype ι
  /-- The QFIM at training state `μ`, parameter count `M`, parameters `θ`. -/
  F : ι → (M : ℕ) → (Fin M → ℝ) → Matrix (Fin M) (Fin M) ℝ
  /-- **Theorem 1** (named hypothesis): the QFIM rank never exceeds `dim g` [LJG+21]. Dischargeable
  against the genuine QFIM via `qfim_rank_le_dlaDim`. -/
  rank_le_dlaDim : ∀ μ M θ, (F μ M θ).rank ≤ dlaDim gens
  /-- **Parameter padding:** freezing the `(M+1)`-th parameter to `0` recovers the
  `M`-parameter QFIM as
  the top-left principal block. This drives monotonicity of the achievable rank. -/
  pad_block : ∀ μ M θ,
    F μ M θ = (F μ (M + 1) (Fin.snoc θ 0)).submatrix Fin.castSucc Fin.castSucc

namespace OverparamData

variable {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (D : OverparamData gens)

/-- The **achievable QFIM rank** at parameter count `M` for training state `μ`:
`R_μ(M) = ⨆_θ rank[F]`. -/
noncomputable def achievableRank (μ : D.ι) (M : ℕ) : ℕ := ⨆ θ : Fin M → ℝ, (D.F μ M θ).rank

/-- The per-`M` achievable-rank supremum is bounded above by `M` (each QFIM is `M × M`). -/
theorem bddAbove_achievable (μ : D.ι) (M : ℕ) :
    BddAbove (Set.range fun θ : Fin M → ℝ => (D.F μ M θ).rank) := by
  refine ⟨M, ?_⟩
  rintro r ⟨θ, rfl⟩
  exact (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin M)

/-- The achievable rank is bounded by the DLA dimension (Theorem 1 ceiling). -/
theorem achievable_le_dlaDim (μ : D.ι) (M : ℕ) : D.achievableRank μ M ≤ dlaDim gens :=
  ciSup_le fun θ => D.rank_le_dlaDim μ M θ

/-- The **saturated QFIM rank** for training state `μ`: `R_μ = ⨆_M R_μ(M)`. -/
noncomputable def saturatedRank (μ : D.ι) : ℕ := ⨆ M, D.achievableRank μ M

/-- The saturated-rank supremum is bounded above by `dim g` (Theorem 1 ceiling); without this the
`ℕ`-indexed supremum would be junk-valued. -/
theorem bddAbove_saturated (μ : D.ι) : BddAbove (Set.range (D.achievableRank μ)) := by
  refine ⟨dlaDim gens, ?_⟩
  rintro r ⟨M, rfl⟩
  exact D.achievable_le_dlaDim μ M

/-- The achievable rank at any `M` is at most the saturated rank (a single term of the `BddAbove`
supremum: `le_ciSup`, *not* monotonicity). -/
theorem achievable_le_saturated (μ : D.ι) (M : ℕ) : D.achievableRank μ M ≤ D.saturatedRank μ :=
  le_ciSup (D.bddAbove_saturated μ) M

/-- The QNN is **overparametrized at `M`** iff every training state's achievable rank has saturated
(Larocca Def. 1, multi-state form `∀ μ, R_μ(M) = R_μ`). -/
def IsOverparametrized (M : ℕ) : Prop := ∀ μ, D.achievableRank μ M = D.saturatedRank μ

/-- **Saturation from below.** Since `R_μ(M) ≤ R_μ` always holds, overparametrization is exactly the
reverse inequality for every training state. -/
theorem isOverparametrized_iff (M : ℕ) :
    D.IsOverparametrized M ↔ ∀ μ, D.saturatedRank μ ≤ D.achievableRank μ M := by
  constructor
  · intro h μ; exact (h μ).ge
  · intro h μ; exact le_antisymm (D.achievable_le_saturated μ M) (h μ)

/-- **Monotonicity of the achievable rank** — more parameters cannot decrease it.
Proved (not assumed)
from the parameter-padding block structure: `rank[F μ M θ] = rank` of a principal submatrix of
`F μ (M+1) (θ,0)`, and a submatrix's rank is at most the whole. -/
theorem achievable_mono (μ : D.ι) : Monotone (D.achievableRank μ) := by
  refine monotone_nat_of_le_succ fun M => ?_
  refine ciSup_le fun θ => ?_
  rw [D.pad_block μ M θ]
  exact (Matrix.rank_submatrix_le _ _ _).trans
    (le_ciSup (D.bddAbove_achievable μ (M + 1)) (Fin.snoc θ 0))

/-- **Persistence of overparametrization.** Once overparametrized at `M`, the QNN
stays overparametrized
for every `M' ≥ M`. -/
theorem isOverparametrized_stays {M M' : ℕ} (hMM' : M ≤ M')
    (h : D.IsOverparametrized M) : D.IsOverparametrized M' := fun μ =>
  le_antisymm (D.achievable_le_saturated μ M') (by rw [← h μ]; exact D.achievable_mono μ hMM')

/-- The saturated rank is attained at some finite parameter count (a monotone bounded `ℕ`-sequence
attains its supremum). -/
theorem exists_achievable_eq_saturated (μ : D.ι) :
    ∃ M, D.achievableRank μ M = D.saturatedRank μ :=
  Nat.sSup_mem (Set.range_nonempty (D.achievableRank μ)) (D.bddAbove_saturated μ)

/-- **Existence of an overparametrized point.** The set
`{M | IsOverparametrized M}` is nonempty: take
the (finite) max over the training set of the per-state saturation points. -/
theorem exists_isOverparametrized : ∃ M, D.IsOverparametrized M := by
  haveI := D.fι
  choose Mμ hMμ using D.exists_achievable_eq_saturated
  refine ⟨Finset.univ.sup Mμ, fun μ => le_antisymm (D.achievable_le_saturated μ _) ?_⟩
  rw [← hMμ μ]
  exact D.achievable_mono μ (Finset.le_sup (Finset.mem_univ μ))

/-- The **critical parameter count** `M_c`: the least parameter count at which the QNN is
overparametrized (Larocca Def. 1). Well-defined because `{M | IsOverparametrized M}` is nonempty. -/
noncomputable def criticalCount : ℕ := sInf {M | D.IsOverparametrized M}

/-- The QNN is overparametrized at its critical count (the degeneracy guard: `M_c` is meaningful).
-/
theorem isOverparametrized_criticalCount : D.IsOverparametrized D.criticalCount :=
  Nat.sInf_mem D.exists_isOverparametrized

/-- **`max_μ R_μ ≤ M_c`** (Larocca's lower bound on the onset): the saturated rank is at most the
critical count, since `rank[F] ≤ M`. -/
theorem saturated_le_criticalCount (μ : D.ι) : D.saturatedRank μ ≤ D.criticalCount := by
  rw [← D.isOverparametrized_criticalCount μ]
  exact ciSup_le fun θ => (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _)

end OverparamData

/-- **A non-trivial overparametrization witness.** A rank-`1`,
parameter-padding-compatible QFIM family
over the fully-controllable `gl(1)` algebra (`dim g = 1`). It instantiates `OverparamData` with a
genuine `Matrix.rank` and attains positive saturated rank — `R = 1 > 0`, `M_c = 1`
— so it is *not* the
degenerate all-zero instance (the VAC-1 defect of the previous overparametrization model). -/
noncomputable def overparamWitness :
    OverparamData (Set.univ : Set (Matrix (Fin 1) (Fin 1) ℂ)) where
  ι := Unit
  fι := inferInstance
  F := fun _ M _ => Matrix.diagonal (fun i : Fin M => if i.val = 0 then 1 else 0)
  rank_le_dlaDim := fun _ M _ => by
    rw [dlaDim_univ, Nat.mul_one, Matrix.rank_diagonal]
    refine Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => Subtype.ext (Fin.ext ?_)⟩
    have ha : a.val.val = 0 := by by_contra hc; exact a.property (by simp [hc])
    have hb : b.val.val = 0 := by by_contra hc; exact b.property (by simp [hc])
    rw [ha, hb]
  pad_block := fun _ M _ => by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [Fin.val_castSucc]
    · rw [if_neg hij, if_neg (mt Fin.castSucc_inj.mp hij)]

/-- The witness attains **positive** saturated rank: `R = 1 > 0`. -/
theorem overparamWitness_saturatedRank_pos (μ : overparamWitness.ι) :
    0 < overparamWitness.saturatedRank μ := by
  have h1 : 0 < overparamWitness.achievableRank μ 1 := by
    refine lt_of_lt_of_le ?_
      (le_ciSup (overparamWitness.bddAbove_achievable μ 1) (fun _ => (0 : ℝ)))
    change 0 < (Matrix.diagonal (fun i : Fin 1 => if i.val = 0 then (1 : ℝ) else 0)).rank
    rw [Matrix.rank_diagonal]
    exact Fintype.card_pos_iff.mpr ⟨⟨0, by simp⟩⟩
  exact lt_of_lt_of_le h1 (overparamWitness.achievable_le_saturated μ 1)

end QuantumAlg
