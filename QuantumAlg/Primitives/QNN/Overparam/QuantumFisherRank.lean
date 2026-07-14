/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.QuantumFisher
public import QuantumAlg.Primitives.QNN.Algebras.FullDLABasis

/-!
# The QFIM-rank bound `rank[F] ≤ dim g` (Larocca Theorem 1)

This file connects the generator/covariance **Quantum Fisher Information
Matrix** (`QuantumAlg.qfim`,
`Util/QuantumFisher.lean`) to the genuine **dynamical Lie algebra** dimension,
proving Larocca et al.
2021 Theorem 1: the achievable QFIM rank never exceeds `dim(g)`.

The bridge is the real-form structure of the DLA. The circuit's (Heisenberg-rotated) generators `hₐ`
are Hermitian with `i·hₐ ∈ g`; since `g` is the complexification of its
skew-Hermitian real form (the
DLA of skew-Hermitian generators is `*`-closed,
`dynamicalLieAlgebra_conjTranspose_mem`), a Hermitian
element of `g` is a **real** linear combination of any Hermitian basis `B` of `g`
(`DLAHermBasis.hermitian_real_combo`). The bilinear Gram factorization
`F = R·(qfim ψ B)·Rᵀ` then forces
`rank[F] ≤ #B = dim(g)` (`qfim_rank_le_of_real_combo`).

This **proves** the rank bound that the QNN overparametrization theory previously assumed as a named
hypothesis. The deeper analytic identification of this covariance matrix with the ansatz's QFIM /
`4·g^FS` (the fidelity expansion / Fubini–Study metric) remains the honest named bridge.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N M : ℕ}

/-- **A Hermitian element of the DLA has real coordinates in a Hermitian basis.** If `Xᴴ = X` and
`i·X ∈ g`, then `X = ∑ⱼ rⱼ Bⱼ` with `rⱼ ∈ ℝ`. (The DLA is `*`-closed, so its
Hermitian part is the real
span of `B`; concretely, `ℂ`-coordinates of a Hermitian element in a Hermitian basis are real.) -/
theorem DLAHermBasis.hermitian_real_combo {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : DLAHermBasis gens) {X : Matrix (Fin N) (Fin N) ℂ} (hX : Xᴴ = X)
    (hmem : Complex.I • X ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    ∃ r : Fin b.dim → ℝ, X = ∑ j, (r j : ℂ) • b.B j := by
  have hXmem : X ∈ (dynamicalLieAlgebra gens).toSubmodule := by
    have h2 := Submodule.smul_mem _ (-Complex.I) hmem
    rwa [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at h2
  rw [← b.span_eq] at hXmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hXmem
  have hconj : ∑ j, (starRingEnd ℂ (c j)) • b.B j = ∑ j, c j • b.B j := by
    have hH : (∑ j, c j • b.B j)ᴴ = ∑ j, (starRingEnd ℂ (c j)) • b.B j := by
      rw [conjTranspose_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [conjTranspose_smul, b.herm j]; rfl
    rw [← hH, hc, hX]
  have hli := (Fintype.linearIndependent_iff).mp b.linearIndependent_B
  have hcreal : ∀ j, starRingEnd ℂ (c j) = c j := by
    intro j
    have hz : ∑ k, (starRingEnd ℂ (c k) - c k) • b.B k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hconj, sub_self]
    exact sub_eq_zero.mp (hli (fun k => starRingEnd ℂ (c k) - c k) hz j)
  refine ⟨fun j => (c j).re, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  change c j • b.B j = ((c j).re : ℂ) • b.B j
  rw [Complex.conj_eq_iff_re.mp (hcreal j)]

/-- **Larocca Theorem 1 — the QFIM rank is bounded by the DLA dimension.** For Hermitian generators
`hₐ` whose skew-Hermitian forms lie in the dynamical Lie algebra `g`, the QFIM rank obeys
`rank[F] ≤ dim(g)`. This is a *proved* consequence of the real-form structure, not an assumption. -/
theorem qfim_rank_le_dlaDim {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (ψ : Fin N → ℂ) {h : Fin M → Matrix (Fin N) (Fin N) ℂ} (hherm : ∀ a, (h a)ᴴ = h a)
    (hmem : ∀ a, Complex.I • h a ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    (qfim ψ h).rank ≤ dlaDim gens := by
  rw [b.dlaDim_eq]
  exact qfim_rank_le_of_real_combo ψ b.B (fun a => b.hermitian_real_combo (hherm a) (hmem a))

/-- **Non-vacuity.** The rank bound applies to the generator family `h = B` (the DLA Hermitian basis
itself): each `Bₐ` is Hermitian and `i·Bₐ ∈ g`. This is a genuine instance for every simple/full DLA
(`su`, `so`, `sp`, `gl`), avoiding the degenerate-witness defect of the previous
overparametrization model. -/
theorem qfim_basis_rank_le_dlaDim {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (ψ : Fin N → ℂ) :
    (qfim ψ b.B).rank ≤ dlaDim gens :=
  qfim_rank_le_dlaDim b ψ b.herm fun a => by
    rw [← b.span_eq]; exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))

/-- **Fully-controllable witness `gl(2ⁿ)`.** Concrete non-vacuous instance of Theorem 1: the QFIM of
the Hermitized matrix-unit basis has rank at most `dim gl(N) = N²`. -/
theorem qfim_fullControllable_rank_le (ψ : Fin N → ℂ) :
    (qfim ψ (fullHermBasis N).B).rank ≤ dlaDim (Set.univ : Set (Matrix (Fin N) (Fin N) ℂ)) :=
  qfim_basis_rank_le_dlaDim (fullHermBasis N) ψ

/-- The unit state `|0⟩` and the Pauli-`X` operator on one qubit (explicit, notation-free). -/
def ket0 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

/-- The Pauli-`X` matrix on one qubit, written without matrix notation. -/
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i = j then 0 else 1

/-- **The QFIM attains positive rank.** For the single Pauli-`X` generator on the unit state `|0⟩`,
`[F] = [4]`, so `rank[F] = 1 > 0`. This is the strict-positivity companion to the
rank bound: the QFIM is
not vacuously zero (e.g. `qfim 0 = 0`), so the bound `0 < rank[F] ≤ dim g` is
non-trivially exercised. -/
theorem qfim_rank_pos_witness : 0 < (qfim ket0 (fun _ : Fin 1 => pauliX2)).rank := by
  have h40 : (qfim ket0 (fun _ : Fin 1 => pauliX2)) 0 0 = 4 := by
    simp [qfim_apply, qCov, expval, ket0, pauliX2, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two]
  have hdiag : (qfim ket0 (fun _ : Fin 1 => pauliX2)) = Matrix.diagonal (fun _ => (4 : ℝ)) := by
    ext i j; fin_cases i; fin_cases j; simpa [Matrix.diagonal] using h40
  rw [hdiag, Matrix.rank_diagonal]
  exact Fintype.card_pos_iff.mpr ⟨⟨0, by norm_num⟩⟩

end QuantumAlg
