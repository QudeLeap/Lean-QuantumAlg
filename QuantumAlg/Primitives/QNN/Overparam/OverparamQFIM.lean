/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Overparam.OverparametrizationDef
public import QuantumAlg.Primitives.QNN.Overparam.QuantumFisherRank
public import QuantumAlg.Primitives.QNN.Algebras.SimpleDLA

/-!
# The overparametrization predicate on the genuine QFIM

The overparametrization onset theory (`OverparamData.achievableRank` / `saturatedRank` /
`IsOverparametrized` / `criticalCount` — `OverparametrizationDef`) is stated against the abstract
field `OverparamData.F`. Here we **discharge that field with the genuine Quantum Fisher Information
Matrix** `QuantumAlg.qfim` evaluated on a real dynamical-Lie-algebra generator family, so the onset
results (`M_c` exists, rank saturates, monotonicity, persistence) rest on a real
Fisher matrix rather
than the previous `gl(1)` placeholder.

`OverparamData.ofQFIM` builds the bundle for **any** Hermitian-orthonormal DLA basis `b` and any
generator sequence `gen : ℕ → …` whose skew-Hermitian forms lie in `g`: the Theorem-1 ceiling
(`rank_le_dlaDim`) is discharged by `qfim_rank_le_dlaDim`, and the parameter-padding block structure
(`pad_block`) by the purely structural `qfim_prefix_submatrix`.

Scope: the QFIM here is the **generator-family** Fisher matrix `qfim ψ (B₀,…,B_{M-1})` (the
reference-frame QFIM); it captures Larocca's "the rank of `M` generators
saturates to `dim g`" onset.
The fully `θ`-rotated ansatz QFIM (Heisenberg-rotated generators `U†H_aU`) coincides with this up to
the DLA Ad-invariance `exp(g)·g·exp(-g) = g`; that rotation is a deferred deeper-faithfulness step,
not used here.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ}

/-- **`pad_block` structural identity.** The `M`-generator QFIM is the top-left `M × M` principal
block of the `(M+1)`-generator QFIM, because each QFIM entry depends only on its two indexed
generators and `↑(castSucc a) = ↑a`. -/
theorem qfim_prefix_submatrix {n : Type*} [Fintype n] (ψ : n → ℂ)
    (gen : ℕ → Matrix n n ℂ) (M : ℕ) :
    qfim ψ (fun a : Fin M => gen a)
      = (qfim ψ (fun a : Fin (M + 1) => gen a)).submatrix Fin.castSucc Fin.castSucc := by
  ext a b
  simp only [qfim_apply, Matrix.submatrix_apply, Fin.val_castSucc]

/-- **The overparametrization bundle on the genuine QFIM.** For any Hermitian-orthonormal DLA basis
`b` of `g`, training states `ψ`, and a generator sequence `gen` whose
skew-Hermitian forms lie in `g`,
the QFIM `F μ M θ = qfim (ψ μ) (B₀,…,B_{M-1})` satisfies the Theorem-1 ceiling and the
parameter-padding block structure — so the full onset theory of `OverparamData` applies to it. -/
noncomputable def OverparamData.ofQFIM {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : DLAHermBasis gens) {ι : Type} [Fintype ι] (ψ : ι → (Fin N → ℂ))
    (gen : ℕ → Matrix (Fin N) (Fin N) ℂ) (hHerm : ∀ k, (gen k)ᴴ = gen k)
    (hMem : ∀ k, Complex.I • gen k ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    OverparamData gens where
  ι := ι
  fι := inferInstance
  F := fun μ M _ => qfim (ψ μ) (fun a : Fin M => gen a)
  rank_le_dlaDim := fun μ _ _ =>
    qfim_rank_le_dlaDim b (ψ μ) (fun a => hHerm a) (fun a => hMem a)
  pad_block := fun μ M _ => qfim_prefix_submatrix (ψ μ) gen M

/-! ### Concrete witness: the genuine `su(2)` QFIM -/

/-- The `su(2)` Hermitian generator sequence (the normalized Pauli basis, cycled). -/
noncomputable def su2GenSeq (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  su2HermBasis.B ⟨k % 3, Nat.mod_lt k (by norm_num)⟩

theorem su2GenSeq_isHermitian (k : ℕ) : (su2GenSeq k)ᴴ = su2GenSeq k :=
  su2HermBasis.herm _

theorem su2GenSeq_smul_I_mem (k : ℕ) :
    Complex.I • su2GenSeq k ∈ (dynamicalLieAlgebra su2Gens).toSubmodule := by
  refine Submodule.smul_mem _ _ ?_
  rw [← su2HermBasis.span_eq]
  exact Submodule.subset_span (Set.mem_range_self _)

/-- **The genuine `su(2)` QFIM overparametrization bundle** (single training state `ρ = |0⟩`). The
overparametrization field `F` is the real `qfim`, not an abstract placeholder. -/
noncomputable def su2QFIMOverparam : OverparamData su2Gens :=
  OverparamData.ofQFIM su2HermBasis (ι := Unit) (fun _ => (fun i => if i = 0 then 1 else 0))
    su2GenSeq su2GenSeq_isHermitian su2GenSeq_smul_I_mem

namespace QFIMOverparam

/-- The one-parameter slice of the concrete `su(2)` QFIM already has positive rank: on `|0⟩`,
the normalized Pauli-`X` generator has QFIM entry `2`. -/
private theorem su2QFIMOverparam_oneParam_rank_pos :
    0 < (qfim (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)
      (fun _ : Fin 1 => rt2inv • pauliX)).rank := by
  have h20 :
      (qfim (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)
        (fun _ : Fin 1 => rt2inv • pauliX)) 0 0 = 2 := by
    simp [qfim_apply, qCov, expval, pauliX, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two, rt2inv_mul_self]
    norm_num
  have hdiag :
      qfim (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)
        (fun _ : Fin 1 => rt2inv • pauliX) = Matrix.diagonal (fun _ => (2 : ℝ)) := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.diagonal] using h20
  rw [hdiag, Matrix.rank_diagonal]
  exact Fintype.card_pos_iff.mpr ⟨⟨0, by norm_num⟩⟩

/-- **Non-vacuity of the concrete QFIM onset witness.** The saturated QFIM rank of the `su(2)`
single-state witness is positive, so the onset theorem is not satisfied merely by the degenerate
all-zero QFIM family. -/
theorem su2QFIMOverparam_saturatedRank_pos (μ : su2QFIMOverparam.ι) :
    0 < su2QFIMOverparam.saturatedRank μ := by
  have hgen0 : (fun a : Fin 1 => su2GenSeq a) = fun _ : Fin 1 => rt2inv • pauliX := by
    funext a
    fin_cases a
    rw [su2GenSeq, su2HermBasis_B]
    change su2B (0 : Fin 3) = rt2inv • pauliX
    rfl
  have h1 : 0 < su2QFIMOverparam.achievableRank μ 1 := by
    refine lt_of_lt_of_le ?_
      (le_ciSup (su2QFIMOverparam.bddAbove_achievable μ 1) (fun _ : Fin 1 => (0 : ℝ)))
    change 0 < (qfim (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)
      (fun a : Fin 1 => su2GenSeq a)).rank
    rw [hgen0]
    exact su2QFIMOverparam_oneParam_rank_pos
  exact lt_of_lt_of_le h1 (su2QFIMOverparam.achievable_le_saturated μ 1)

/-- **Non-vacuous onset on the genuine QFIM.** The overparametrization onset
exists, and the saturated
QFIM rank is positive for the concrete `su(2)` witness. -/
theorem main :
    (∃ M, su2QFIMOverparam.IsOverparametrized M) ∧
      ∀ μ, 0 < su2QFIMOverparam.saturatedRank μ :=
  ⟨su2QFIMOverparam.exists_isOverparametrized, su2QFIMOverparam_saturatedRank_pos⟩

/-- **Onset on the genuine QFIM.** The overparametrization onset
(`∃ M, IsOverparametrized M`, hence a
well-defined critical count `M_c`) holds for the **real** `su(2)` Quantum Fisher
Information Matrix —
upgrading the overparametrization predicate from its previous `gl(1)` placeholder to a genuine DLA
QFIM. -/
theorem exists_isOverparametrized : ∃ M, su2QFIMOverparam.IsOverparametrized M :=
  main.1

end QFIMOverparam

end QuantumAlg
