/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Scalar common stabilizers

Two Hermitian spectral expansions with simple spectra and nonzero cross-basis
overlaps have only scalar unitary common stabilizers. Orthonormality of both
supplied eigenbases is essential. Positivity and full rank are unnecessary for
this matrix theorem; no density-state or algorithm implementation is asserted.
-/

@[expose] public section

namespace Matrix.CommonStabilizer

noncomputable section

open scoped BigOperators

/-- Definition: outer product |v⟩⟨w|. -/
def ketbra {d : ℕ} (v w : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => v i * starRingEnd ℂ (w j)

/-- Definition: standard inner product ⟨v|w⟩ = Σ_i v̄_i w_i. -/
def innerProd {d : ℕ} (v w : Fin d → ℂ) : ℂ :=
  ∑ i : Fin d, starRingEnd ℂ (v i) * w i

/-- Matrix whose columns are the vectors `rv i`. -/
def basisMat {d : ℕ} (rv : Fin d → Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => rv j i

/-- Definition: spectral expansion with an orthonormal
eigenbasis. -/
def HasSpectralExpansion {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ)
    (eigenvalues : Fin d → ℝ)
    (eigenvectors : Fin d → Fin d → ℂ) : Prop :=
  ρ = ∑ i, (eigenvalues i : ℂ) • ketbra (eigenvectors i) (eigenvectors i) ∧
    (∀ i j : Fin d, innerProd (eigenvectors i) (eigenvectors j) = if i = j then 1 else 0)

/-- Definition: all eigenvalues distinct. -/
def SimpleSpectrum {d : ℕ} (eigenvalues : Fin d → ℝ) : Prop :=
  ∀ i i' : Fin d, i ≠ i' → eigenvalues i ≠ eigenvalues i'

/-- Definition: W = e^{iθ} I for some θ ∈ ℝ. -/
def IsScalarUnitary {d : ℕ}
    (W : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ θ : ℝ, W = Complex.exp (Complex.I * (θ : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- `R† R = 1` from orthonormality of the columns of `R = basisMat rv`. -/
lemma RtR_id {d : ℕ} (rv : Fin d → Fin d → ℂ)
    (hon : ∀ i j, innerProd (rv i) (rv j) = if i = j then 1 else 0) :
    (basisMat rv).conjTranspose * basisMat rv = 1 := by
  ext i j
  simpa [basisMat, Matrix.conjTranspose, Matrix.mul_apply,
    Matrix.one_apply, innerProd] using hon i j

/-- `R R† = 1` from orthonormality of the columns of `R = basisMat rv`. -/
lemma RRt_id {d : ℕ} (rv : Fin d → Fin d → ℂ)
    (hon : ∀ i j, innerProd (rv i) (rv j) = if i = j then 1 else 0) :
    basisMat rv * (basisMat rv).conjTranspose = 1 := by
  exact (mul_eq_one_comm.mp (RtR_id rv hon))

/-- Entry of `A * diag v`: only the diagonal entry of `diag v` contributes. -/
lemma mul_diagonal_apply {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ)
    (i j : Fin d) :
    (A * Matrix.diagonal v) i j = A i j * v j := by
  simp [Matrix.mul_apply, Matrix.diagonal]

/-- Entry of `diag v * A`: only the diagonal entry of `diag v` contributes. -/
lemma diagonal_mul_apply {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ)
    (i j : Fin d) :
    (Matrix.diagonal v * A) i j = v i * A i j := by
  simp [Matrix.mul_apply, Matrix.diagonal]

/-- Spectral expansion as a matrix product: `ρ = R · diag r · R†`. -/
lemma rho_decomp {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (r : Fin d → ℝ)
    (rv : Fin d → Fin d → ℂ)
    (hρ : ρ = ∑ i, (r i : ℂ) • ketbra (rv i) (rv i)) :
    ρ = basisMat rv * Matrix.diagonal (fun i => (r i : ℂ)) * (basisMat rv).conjTranspose := by
  rw [hρ]
  ext i j
  rw [Matrix.sum_apply i j Finset.univ]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_diagonal_apply]
  simp only [basisMat, Matrix.conjTranspose_apply, ketbra, RCLike.star_def]
  ring

/-- Entry of `(R† S)`: the cross-overlap `innerProd (rvec i) (svec j)`. -/
lemma cross_entry {d : ℕ} (rvec svec : Fin d → Fin d → ℂ) (i j : Fin d) :
    ((basisMat rvec).conjTranspose * basisMat svec) i j = innerProd (rvec i) (svec j) := by
  simp [basisMat, Matrix.conjTranspose, Matrix.mul_apply, innerProd]

/-- `W ρ W† = ρ` with `W† W = 1` implies `W ρ = ρ W`. -/
lemma commute_from_stabilize {d : ℕ} (W ρ : Matrix (Fin d) (Fin d) ℂ)
    (hWtW : W.conjTranspose * W = 1)
    (hWρ : W * ρ * W.conjTranspose = ρ) :
    W * ρ = ρ * W := by
  calc
    W * ρ = W * ρ * (W.conjTranspose * W) := by rw [hWtW, Matrix.mul_one]
    _ = (W * ρ * W.conjTranspose) * W := by rw [← Matrix.mul_assoc]
    _ = ρ * W := by rw [hWρ]

/-- Conjugation by a matrix `R` with `R R† = 1` is involutive. -/
lemma conj_eq {d : ℕ} (R W : Matrix (Fin d) (Fin d) ℂ)
    (hRRt : R * R.conjTranspose = 1) :
    R * (R.conjTranspose * W * R) * R.conjTranspose = W := by
  calc
    R * (R.conjTranspose * W * R) * R.conjTranspose
        = (R * R.conjTranspose) * W * (R * R.conjTranspose) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc]
    _ = W := by rw [hRRt]; simp

/-- Sandwiching `W X = X W` (with `X = R · D · R†`) by `R† · _ · R` makes
`R† W R` commute with `D`. -/
lemma sandwich_comm {d : ℕ} (R W X : Matrix (Fin d) (Fin d) ℂ)
    (hRtR : R.conjTranspose * R = 1)
    (hWX : W * (R * X * R.conjTranspose) = (R * X * R.conjTranspose) * W) :
    (R.conjTranspose * W * R) * X = X * (R.conjTranspose * W * R) := by
  calc
    (R.conjTranspose * W * R) * X
        = R.conjTranspose * (W * (R * X)) := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = R.conjTranspose * (W * ((R * X) * R.conjTranspose * R)) := by
          congr 1
          congr 1
          rw [Matrix.mul_assoc, hRtR, Matrix.mul_one]
    _ = R.conjTranspose * ((W * ((R * X) * R.conjTranspose)) * R) := by
          congr 1
          rw [← Matrix.mul_assoc]
    _ = R.conjTranspose * ((W * (R * X * R.conjTranspose)) * R) := rfl
    _ = R.conjTranspose * (((R * X * R.conjTranspose) * W) * R) := by
          rw [hWX]
    _ = R.conjTranspose * ((R * X) * (R.conjTranspose * W * R)) := by
          congr 1
          calc
            ((R * X) * R.conjTranspose * W) * R
                = ((R * X) * R.conjTranspose) * (W * R) := by
                  rw [Matrix.mul_assoc]
            _ = (R * X) * (R.conjTranspose * (W * R)) := by
                  rw [Matrix.mul_assoc]
            _ = (R * X) * (R.conjTranspose * W * R) := by
                  congr 1
                  rw [← Matrix.mul_assoc]
    _ = (R.conjTranspose * (R * X)) * (R.conjTranspose * W * R) := by
          noncomm_ring
    _ = ((R.conjTranspose * R) * X) * (R.conjTranspose * W * R) := by
          noncomm_ring
    _ = X * (R.conjTranspose * W * R) := by
          rw [hRtR, Matrix.one_mul]

/-- Commuting with a diagonal matrix with distinct entries forces the matrix
to be diagonal. -/
lemma diag_of_commute {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (r : Fin d → ℝ)
    (hsimple : SimpleSpectrum r)
    (h : A * Matrix.diagonal (fun i => (r i : ℂ)) =
      Matrix.diagonal (fun i => (r i : ℂ)) * A) :
    ∀ i j : Fin d, i ≠ j → A i j = 0 := by
  intro i j hij
  have hcom : (A * Matrix.diagonal (fun i => (r i : ℂ))) i j =
      (Matrix.diagonal (fun i => (r i : ℂ)) * A) i j := by
    rw [h]
  rw [mul_diagonal_apply, diagonal_mul_apply] at hcom
  have hsub : ((r i : ℂ) - (r j : ℂ)) * A i j = 0 := by
    calc
      ((r i : ℂ) - (r j : ℂ)) * A i j = (r i : ℂ) * A i j - (r j : ℂ) * A i j := by ring
      _ = (r i : ℂ) * A i j - A i j * (r j : ℂ) := by ring
      _ = 0 := by rw [← hcom]; ring
  have hne : (r i : ℂ) - (r j : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (Complex.ofReal_inj.not.mpr (hsimple i j hij))
  exact (mul_eq_zero.mp hsub).resolve_left hne

/-- A matrix with all off-diagonal entries zero equals its diagonal. -/
lemma diag_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hoff : ∀ i j : Fin d, i ≠ j → A i j = 0) :
    A = Matrix.diagonal (fun i => A i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.diagonal, hij, hoff i j hij]

/-- `(A · C) = (C · B)` where `A = R† W R`, `B = S† W S`, `C = R† S`: both
sides equal `R† W S`. -/
lemma AC_eq_CB {d : ℕ} (R W S : Matrix (Fin d) (Fin d) ℂ)
    (hRRt : R * R.conjTranspose = 1) (hSSRt : S * S.conjTranspose = 1) :
    (R.conjTranspose * W * R) * (R.conjTranspose * S) =
      (R.conjTranspose * S) * (S.conjTranspose * W * S) := by
  calc
    (R.conjTranspose * W * R) * (R.conjTranspose * S)
        = R.conjTranspose * W * S := by
          rw [Matrix.mul_assoc (R.conjTranspose * W) R (R.conjTranspose * S),
            ← Matrix.mul_assoc R R.conjTranspose S, hRRt, Matrix.one_mul]
    _ = (R.conjTranspose * S) * (S.conjTranspose * W * S) := by
          rw [← Matrix.mul_assoc (R.conjTranspose * S) (S.conjTranspose * W) S,
            Matrix.mul_assoc R.conjTranspose S (S.conjTranspose * W),
            ← Matrix.mul_assoc S S.conjTranspose W, hSSRt, Matrix.one_mul]

/-- Entry of `c • 1`. -/
lemma smul_one_apply {d : ℕ} (c : ℂ) (i j : Fin d) :
    (c • (1 : Matrix (Fin d) (Fin d) ℂ)) i j = if i = j then c else 0 := by
  simp [Matrix.one_apply]

/-- Entry of `(c • 1)†`. -/
lemma smul_one_conjTranspose_apply {d : ℕ} (c : ℂ) (i j : Fin d) :
    ((c • (1 : Matrix (Fin d) (Fin d) ℂ)).conjTranspose) i j =
      if i = j then starRingEnd ℂ c else 0 := by
  rw [Matrix.conjTranspose_apply]
  rw [smul_one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

/-- A scalar multiple of the identity that is unitary has unit scalar. -/
lemma entry_norm_one_of_smul_unitary {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (c : ℂ) (i : Fin d)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hWc : W = c • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    ‖c‖ = 1 := by
  have hWWt : W * W.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hW)
  have hentry : (W * W.conjTranspose) i i = 1 := by
    simpa using congrFun (congrFun hWWt i) i
  rw [hWc] at hentry
  have hcompute : ((c • (1 : Matrix (Fin d) (Fin d) ℂ)) *
      (c • (1 : Matrix (Fin d) (Fin d) ℂ)).conjTranspose) i i = c * starRingEnd ℂ c := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [smul_one_apply, smul_one_conjTranspose_apply]
      simp
    · intro b hb hbi
      rw [smul_one_apply, smul_one_conjTranspose_apply]
      have hib : i ≠ b := fun h => hbi h.symm
      simp [hib]
    · intro hi
      exfalso
      exact hi (Finset.mem_univ i)
  have hprod : c * starRingEnd ℂ c = 1 := by
    rw [hcompute] at hentry
    exact hentry
  have hnormSq : ‖c‖ ^ 2 = 1 := by
    have hnsC : (Complex.normSq c : ℂ) = 1 := by
      have hmul := Complex.normSq_eq_conj_mul_self (z := c)
      rw [mul_comm] at hmul
      exact hmul.trans hprod
    have hnsR : Complex.normSq c = 1 := Complex.ofReal_inj.mp hnsC
    rwa [Complex.normSq_eq_norm_sq] at hnsR
  rcases sq_eq_one_iff.mp hnormSq with h | h
  · exact h
  · nlinarith [norm_nonneg c]

/-- Any unitary W stabilizing both simple-spectrum Hermitian matrices is a
scalar unitary. -/
lemma commonUnitaryStabilizer_isScalar {d : ℕ}
    (W : Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (r s : Fin d → ℝ)
    (rvec svec : Fin d → Fin d → ℂ)
    (hρ_spectrum : HasSpectralExpansion ρ r rvec)
    (hσ_spectrum : HasSpectralExpansion σ s svec)
    (hr_simple : SimpleSpectrum r)
    (hs_simple : SimpleSpectrum s)
    (h_cross : ∀ i j : Fin d, innerProd (rvec i) (svec j) ≠ 0)
    (hW_unitary : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hWρ : W * ρ * W.conjTranspose = ρ)
    (hWσ : W * σ * W.conjTranspose = σ) :
    IsScalarUnitary W := by
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, ?_⟩
    have hW1 : W = (1 : Matrix (Fin 0) (Fin 0) ℂ) := by
      ext i j
      rcases i with ⟨v, hv⟩
      exact (Nat.not_lt_zero v hv).elim
    rw [hW1]
    simp
  · have hnon : Nonempty (Fin d) := by
      exact Fintype.card_pos_iff.mp (by simpa using (Nat.pos_of_ne_zero hd))
    let R : Matrix (Fin d) (Fin d) ℂ := basisMat rvec
    let S : Matrix (Fin d) (Fin d) ℂ := basisMat svec
    have hRtR : R.conjTranspose * R = 1 := by
      simpa [R] using RtR_id rvec hρ_spectrum.2
    have hRRt : R * R.conjTranspose = 1 := by
      simpa [R] using RRt_id rvec hρ_spectrum.2
    have hStS : S.conjTranspose * S = 1 := by
      simpa [S] using RtR_id svec hσ_spectrum.2
    have hSSRt : S * S.conjTranspose = 1 := by
      simpa [S] using RRt_id svec hσ_spectrum.2
    have hρ_dec : ρ = R * Matrix.diagonal (fun i => (r i : ℂ)) * R.conjTranspose := by
      simpa [R] using rho_decomp ρ r rvec hρ_spectrum.1
    have hσ_dec : σ = S * Matrix.diagonal (fun i => (s i : ℂ)) * S.conjTranspose := by
      simpa [S] using rho_decomp σ s svec hσ_spectrum.1
    have hWtW : W.conjTranspose * W = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hW_unitary)
    have hWρ_comm : W * ρ = ρ * W := commute_from_stabilize W ρ hWtW hWρ
    have hWσ_comm : W * σ = σ * W := commute_from_stabilize W σ hWtW hWσ
    let A : Matrix (Fin d) (Fin d) ℂ := R.conjTranspose * W * R
    have hAcomm : A * Matrix.diagonal (fun i => (r i : ℂ)) =
        Matrix.diagonal (fun i => (r i : ℂ)) * A := by
      dsimp [A]
      exact sandwich_comm R W (Matrix.diagonal (fun i => (r i : ℂ))) hRtR
        (by simpa [hρ_dec] using hWρ_comm)
    have hAdiag : ∀ i j : Fin d, i ≠ j → A i j = 0 :=
      diag_of_commute A r hr_simple hAcomm
    let lam : Fin d → ℂ := fun i => A i i
    have hAeq : A = Matrix.diagonal lam := diag_eq A hAdiag
    have hWrep : W = R * A * R.conjTranspose := by
      calc
        W = R * (R.conjTranspose * W * R) * R.conjTranspose := by
          conv_lhs =>
            rw [← conj_eq R W hRRt]
        _ = R * A * R.conjTranspose := rfl
    let B : Matrix (Fin d) (Fin d) ℂ := S.conjTranspose * W * S
    have hBcomm : B * Matrix.diagonal (fun i => (s i : ℂ)) =
        Matrix.diagonal (fun i => (s i : ℂ)) * B := by
      dsimp [B]
      exact sandwich_comm S W (Matrix.diagonal (fun i => (s i : ℂ))) hStS
        (by simpa [hσ_dec] using hWσ_comm)
    have hBdiag : ∀ i j : Fin d, i ≠ j → B i j = 0 :=
      diag_of_commute B s hs_simple hBcomm
    let μ : Fin d → ℂ := fun j => B j j
    have hBeq : B = Matrix.diagonal μ := diag_eq B hBdiag
    have hWrepB : W = S * B * S.conjTranspose := by
      calc
        W = S * (S.conjTranspose * W * S) * S.conjTranspose := by
          conv_lhs =>
            rw [← conj_eq S W hSSRt]
        _ = S * B * S.conjTranspose := rfl
    let C : Matrix (Fin d) (Fin d) ℂ := R.conjTranspose * S
    have hACCB : A * C = C * B := by
      dsimp [A, B, C]
      exact AC_eq_CB R W S hRRt hSSRt
    have hACdiag : Matrix.diagonal lam * C = C * Matrix.diagonal μ := by
      calc
        Matrix.diagonal lam * C = A * C := by rw [← hAeq]
        _ = C * B := hACCB
        _ = C * Matrix.diagonal μ := by rw [hBeq]
    have hlambda_mu : ∀ i j : Fin d, lam i = μ j := by
      intro i j
      have hentry : (Matrix.diagonal lam * C) i j = (C * Matrix.diagonal μ) i j := by
        rw [hACdiag]
      rw [diagonal_mul_apply, mul_diagonal_apply] at hentry
      have hsub : (lam i - μ j) * C i j = 0 := by
        calc
          (lam i - μ j) * C i j = lam i * C i j - μ j * C i j := by ring
          _ = C i j * μ j - μ j * C i j := by rw [hentry]
          _ = 0 := by ring
      have hC : C i j ≠ 0 := by
        have hc := cross_entry rvec svec i j
        have hc2 : C i j = innerProd (rvec i) (svec j) := by simpa [C] using hc
        simpa [hc2] using h_cross i j
      have hdiff : lam i - μ j = 0 := (mul_eq_zero.mp hsub).resolve_right hC
      exact sub_eq_zero.mp hdiff
    let i₀ : Fin d := hnon.some
    have hlamconst : ∀ j : Fin d, lam j = μ i₀ := fun j => hlambda_mu j i₀
    let c : ℂ := μ i₀
    have hdiag_c : Matrix.diagonal lam = c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.diagonal, hlamconst, c]
      · simp [Matrix.diagonal, hij, c]
    have hWc : W = c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      calc
        W = R * A * R.conjTranspose := hWrep
        _ = R * Matrix.diagonal lam * R.conjTranspose := by rw [hAeq]
        _ = R * (c • (1 : Matrix (Fin d) (Fin d) ℂ)) * R.conjTranspose := by
          rw [hdiag_c]
        _ = c • (R * 1 * R.conjTranspose) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = c • (R * R.conjTranspose) := by rw [Matrix.mul_one]
        _ = c • (1 : Matrix (Fin d) (Fin d) ℂ) := by rw [hRRt]
    have hc_unit : ‖c‖ = 1 := entry_norm_one_of_smul_unitary W c i₀ hW_unitary hWc
    have hc_exp : c = Complex.exp (Complex.I * (Complex.arg c : ℂ)) := by
      have hm := Complex.norm_mul_exp_arg_mul_I c
      have htmp : c = Complex.exp (Complex.arg c * Complex.I) := by
        simpa [hc_unit] using hm.symm
      have hm1 : Complex.exp (Complex.arg c * Complex.I) = c := htmp.symm
      simpa [mul_comm] using hm1.symm
    refine ⟨Complex.arg c, ?_⟩
    rw [hWc]
    conv_lhs =>
      rw [hc_exp]

end

end Matrix.CommonStabilizer
