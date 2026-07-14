/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.OrthogonalDLA
public import QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra

/-!
# The `n`-qubit Pauli realization of `sp(2ⁿ)` and the symplectic-DLA barren plateau

With the symplectic form `J₀ = i·Y₀` (the single-qubit `Y` on the first qubit, `J₀ᵀ = -J₀` and
`J₀² = -1` for every `n`), the symplectic Lie algebra `sp(2ⁿ) = {A : Aᵀ J₀ = -J₀ A}` is the fixed
space of the involution `θ(A) = J₀ Aᵀ J₀`. On the Pauli basis `θ` is **diagonal**,
`θ(P_s) = spSign s · P_s` with `spSign s = -(-1)^{#Y(s)}·ε(s₀)` (`ε(a) = +1` for `I,Y`, `-1` for
`X,Z`), exactly as transpose parity was diagonal for `so`. The `(4ⁿ + 2ⁿ)/2` Paulis with
`spSign = +1` form a Hermitian Hilbert–Schmidt orthonormal basis of `sp(2ⁿ)`, realising it as a
`DLAHermBasis`; the single-ideal Ragone variance reduction and the exponential barren plateau then
follow on the qubit family — the symplectic analogue of the `su(2ⁿ)`/`so(2ⁿ)` cases.

Mirrors `OrthogonalDLA.lean`, reusing the Pauli basis of `gl(2ⁿ)`; the new ingredient is the Pauli
product law (for the `J₀`-conjugation) in place of the pure entrywise transpose.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The Pauli-string product law -/

/-- **Pauli-string product factorises over qubits**:
`(P_s P_t) i j = ∏ₖ (σ_{sₖ} σ_{tₖ}) (iₖ, jₖ)`. -/
theorem pauliStr_mul_apply {n : ℕ} (s t : Fin n → Fin 4) (i j : Fin n → Fin 2) :
    (pauliStr s * pauliStr t) i j = ∏ k, (pauli1 (s k) * pauli1 (t k)) (i k) (j k) := by
  simp only [Matrix.mul_apply, pauliStr, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 2)))
      (fun k a => pauli1 (s k) (i k) a * pauli1 (t k) a (j k))]

/-! ### Single-qubit `Y`-conjugation -/

/-- The `Y`-conjugation sign of a single-qubit Pauli label: `+1` for `I,Y` (commute with `Y`),
`-1` for `X,Z` (anticommute). -/
noncomputable def yConjSign (a : Fin 4) : ℂ := if a = 0 ∨ a = 2 then 1 else -1

/-- Single-qubit `Y`-conjugation: `Y σ_a Y = ε(a) σ_a`. -/
theorem pauli1_Y_conj (a : Fin 4) :
    pauli1 2 * pauli1 a * pauli1 2 = yConjSign a • pauli1 a := by
  fin_cases a <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli1, yConjSign, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, Complex.I_mul_I])

/-- **Pauli-string triple product factorises over qubits.** -/
theorem pauliStr_mul3_apply {n : ℕ} (a b c : Fin n → Fin 4) (i j : Fin n → Fin 2) :
    (pauliStr a * pauliStr b * pauliStr c) i j
      = ∏ k, (pauli1 (a k) * pauli1 (b k) * pauli1 (c k)) (i k) (j k) := by
  rw [Matrix.mul_apply]
  simp only [pauliStr_mul_apply]
  simp only [pauliStr, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 2)))
      (fun k a' => (pauli1 (a k) * pauli1 (b k)) (i k) a' * pauli1 (c k) a' (j k))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply]

/-! ### `Y₀`-conjugation and the symplectic involution -/

/-- The Pauli label of `Y` on qubit `0` (identity elsewhere). -/
def siteY0 (n : ℕ) [NeZero n] : Fin n → Fin 4 := Function.update (fun _ => 0) 0 2

/-- `Y₀`-conjugation of a Pauli string: `Y₀ P_s Y₀ = ε(s₀) P_s`. -/
theorem pauliStr_Y0_conj {n : ℕ} [NeZero n] (s : Fin n → Fin 4) :
    pauliStr (siteY0 n) * pauliStr s * pauliStr (siteY0 n) = yConjSign (s 0) • pauliStr s := by
  ext i j
  rw [pauliStr_mul3_apply, Matrix.smul_apply, smul_eq_mul, pauliStr, Matrix.of_apply]
  have hterm : ∀ k, (pauli1 (siteY0 n k) * pauli1 (s k) * pauli1 (siteY0 n k)) (i k) (j k)
      = (if k = 0 then yConjSign (s 0) else 1) * pauli1 (s k) (i k) (j k) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [siteY0, pauli1_Y_conj, Matrix.smul_apply, smul_eq_mul]
    · simp [siteY0, hk, pauli1_zero]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ (0 : Fin n) (fun _ => yConjSign (s 0))]
  simp

/-- `Y₀`-conjugation on the `Fin (2ⁿ)` reindexing. -/
theorem pauliMat_Y0_conj {n : ℕ} [NeZero n] (s : Fin n → Fin 4) :
    pauliMat (siteY0 n) * pauliMat s * pauliMat (siteY0 n) = yConjSign (s 0) • pauliMat s := by
  have h : pauliMat (siteY0 n) * pauliMat s * pauliMat (siteY0 n)
      = (pauliStr (siteY0 n) * pauliStr s * pauliStr (siteY0 n)).submatrix
          finFunctionFinEquiv.symm finFunctionFinEquiv.symm := by
    simp only [pauliMat, Matrix.submatrix_mul_equiv]
  rw [h, pauliStr_Y0_conj]
  ext p q
  simp [Matrix.submatrix_apply, Matrix.smul_apply, pauliMat]

/-- The eigenvalue of the symplectic involution `θ(A) = J₀ Aᵀ J₀` on `P_s`:
`spSign s = -(-1)^{#Y(s)}·ε(s₀) ∈ {±1}`. -/
noncomputable def spSign {n : ℕ} [NeZero n] (s : Fin n → Fin 4) : ℂ :=
  -((-1) ^ yCount s * yConjSign (s 0))

/-- **The symplectic involution is diagonal on the Pauli basis**:
`J₀ (P_s)ᵀ J₀ = spSign s · P_s`, with `J₀ = i·Y₀`. -/
theorem pauliMat_theta {n : ℕ} [NeZero n] (s : Fin n → Fin 4) :
    (Complex.I • pauliMat (siteY0 n)) * (pauliMat s)ᵀ * (Complex.I • pauliMat (siteY0 n))
      = spSign s • pauliMat s := by
  have hc : (Complex.I • pauliMat (siteY0 n)) * (pauliMat s)ᵀ * (Complex.I • pauliMat (siteY0 n))
      = (Complex.I * Complex.I) • (pauliMat (siteY0 n) * (pauliMat s)ᵀ * pauliMat (siteY0 n)) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hc, pauliMat_transpose, prod_ySign_eq, mul_smul_comm, smul_mul_assoc, pauliMat_Y0_conj,
    smul_smul, smul_smul, spSign]
  congr 1
  rw [Complex.I_mul_I]; ring

/-- Pull a scalar through a `J · _ · J` conjugation (with `J` atomic, so the scalar inside `J`
itself is not disturbed). -/
private theorem jconj_smul {n : ℕ} (J X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (c : ℂ) :
    J * (c • X) * J = c • (J * X * J) := by
  rw [mul_smul_comm, smul_mul_assoc]

/-! ### The `θ=+1` (symplectic) Pauli strings as a candidate basis -/

open scoped Classical in
/-- Dimension of the symplectic basis: the count of `θ=+1` (symplectic) Pauli strings. -/
noncomputable def spDim (n : ℕ) [NeZero n] : ℕ :=
  Fintype.card {s : Fin n → Fin 4 // spSign s = 1}

open scoped Classical in
/-- An enumeration of the `θ=+1` Pauli labels. -/
noncomputable def spEquiv (n : ℕ) [NeZero n] :
    Fin (spDim n) ≃ {s : Fin n → Fin 4 // spSign s = 1} :=
  (Fintype.equivFin _).symm

/-- The symplectic Pauli generators `{i·P_s : θ(P_s) = P_s}` of the
`sp(2ⁿ)` dynamical Lie algebra. -/
def spGens (n : ℕ) [NeZero n] : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4, spSign s = 1 ∧ A = Complex.I • pauliMat s}

/-- The candidate Hermitian orthonormal basis of `sp(2ⁿ)`: the normalized `θ=+1` Pauli strings. -/
noncomputable def spB (n : ℕ) [NeZero n] (i : Fin (spDim n)) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  rtNinv n • pauliMat (spEquiv n i).1

theorem spB_isHermitian (n : ℕ) [NeZero n] (i : Fin (spDim n)) : (spB n i)ᴴ = spB n i := by
  rw [spB, conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]

theorem spB_ortho (n : ℕ) [NeZero n] (i j : Fin (spDim n)) :
    hsInner (spB n i) (spB n j) = if i = j then 1 else 0 := by
  rw [spB, spB, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply, rtNinv_conj, ← mul_assoc,
    rtNinv_mul_self, pauliMat_hsInner]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, one_div,
      inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg h, if_neg (fun he => h ((spEquiv n).injective (Subtype.ext he))), mul_zero]

theorem spB_linearIndependent (n : ℕ) [NeZero n] : LinearIndependent ℂ (spB n) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : hsInner (spB n i) (∑ j, c j • spB n j) = c i := by
    rw [hsInner_sum_right]
    have hterm : ∀ j, hsInner (spB n i) (c j • spB n j) = if i = j then c j else 0 := by
      intro j; rw [hsInner_smul_right, spB_ortho]; split <;> simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq]
    simp
  rw [hc] at h1
  simpa [hsInner] using h1.symm

/-! ### `Y₀² = I`, `J₀² = -1`, and the skew-adjoint bridge -/

/-- `Y₀² = I`. -/
theorem pauliMat_siteY0_sq {n : ℕ} [NeZero n] :
    pauliMat (siteY0 n) * pauliMat (siteY0 n) = 1 := by
  simp only [pauliMat, Matrix.submatrix_mul_equiv, pauliStr_sq, Matrix.submatrix_one_equiv]

/-- `J₀² = -1` for the symplectic form `J₀ = i·Y₀`. -/
theorem symJ_sq {n : ℕ} [NeZero n] :
    (Complex.I • pauliMat (siteY0 n)) * (Complex.I • pauliMat (siteY0 n)) = -1 := by
  rw [smul_mul_smul_comm, pauliMat_siteY0_sq, Complex.I_mul_I, neg_one_smul]

/-- **Skew-adjointness w.r.t. `J₀` is the `θ`-fixed condition** (uses `J₀² = -1`). -/
theorem mem_skewAdjoint_iff_theta {n : ℕ} [NeZero n] (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    A ∈ skewAdjointMatricesSubmodule (Complex.I • pauliMat (siteY0 n)) ↔
      (Complex.I • pauliMat (siteY0 n)) * Aᵀ * (Complex.I • pauliMat (siteY0 n)) = A := by
  rw [mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  constructor
  · intro h
    calc (Complex.I • pauliMat (siteY0 n)) * Aᵀ * (Complex.I • pauliMat (siteY0 n))
        = (Complex.I • pauliMat (siteY0 n)) * (Aᵀ * (Complex.I • pauliMat (siteY0 n))) := by
          rw [mul_assoc]
      _ = (Complex.I • pauliMat (siteY0 n)) *
          ((Complex.I • pauliMat (siteY0 n)) * (-A)) := by
        rw [h]
      _ = (Complex.I • pauliMat (siteY0 n)) * (Complex.I • pauliMat (siteY0 n)) * (-A) := by
          rw [mul_assoc]
      _ = (-1 : Matrix _ _ ℂ) * (-A) := by rw [symJ_sq]
      _ = A := by rw [neg_one_mul, neg_neg]
  · intro h
    conv_rhs => rw [← h]
    rw [mul_neg, ← mul_assoc, ← mul_assoc, symJ_sq, neg_one_mul, neg_mul, neg_neg]

/-! ### `span{spB} = sp(2ⁿ)` via the symplectic involution and the Pauli basis -/

/-- Each symplectic basis element is `θ`-fixed (lies in `sp`). -/
theorem spB_theta (n : ℕ) [NeZero n] (i : Fin (spDim n)) :
    (Complex.I • pauliMat (siteY0 n)) * (spB n i)ᵀ *
      (Complex.I • pauliMat (siteY0 n)) = spB n i := by
  rw [spB, Matrix.transpose_smul,
    jconj_smul (Complex.I • pauliMat (siteY0 n)) ((pauliMat (spEquiv n i).1)ᵀ) (rtNinv n),
    pauliMat_theta, (spEquiv n i).2, one_smul]

/-- **Every `J₀`-skew-adjoint matrix is a span of `θ=+1` Pauli strings.** -/
theorem mem_span_spB_of_sp {n : ℕ} [NeZero n] {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hA : A ∈ skewAdjointMatricesSubmodule (Complex.I • pauliMat (siteY0 n))) :
    A ∈ Submodule.span ℂ (Set.range (spB n)) := by
  rw [mem_skewAdjoint_iff_theta] at hA
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (show A ∈ Submodule.span ℂ (Set.range (fun s : Fin n → Fin 4 => pauliMat s)) by
      rw [pauliMat_span_top]; exact Submodule.mem_top)
  have hAt : (Complex.I • pauliMat (siteY0 n)) * Aᵀ * (Complex.I • pauliMat (siteY0 n))
      = ∑ s, (c s * spSign s) • pauliMat s := by
    have h0 : (∑ s, c s • pauliMat s)ᵀ = ∑ s, (c s • pauliMat s)ᵀ := by
      ext p q; simp [Matrix.transpose_apply, Matrix.sum_apply]
    rw [← hc, h0, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.transpose_smul,
      jconj_smul (Complex.I • pauliMat (siteY0 n)) ((pauliMat s)ᵀ) (c s), pauliMat_theta, smul_smul]
  have hsum : ∑ s, (c s * spSign s - c s) • pauliMat s = 0 := by
    have hcomb : ∑ s, (c s * spSign s) • pauliMat s = ∑ s, c s • pauliMat s := by
      rw [← hAt, hA, hc]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hcomb
    simpa only [← sub_smul] using hcomb
  have hrel := Fintype.linearIndependent_iff.mp (pauliMat_linearIndependent n)
    (fun s => c s * spSign s - c s) hsum
  have hrtne : rtNinv n ≠ 0 := by
    intro hh; have hm := rtNinv_mul_self n; rw [hh, mul_zero] at hm
    exact (one_div_ne_zero (pow_ne_zero n (two_ne_zero))) hm.symm
  rw [← hc]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : spSign s = 1
  · refine Submodule.smul_mem _ _ ?_
    have hkey : spB n ((spEquiv n).symm ⟨s, hs⟩) = rtNinv n • pauliMat s := by
      simp only [spB, Equiv.apply_symm_apply]
    have hpm : pauliMat s = (rtNinv n)⁻¹ • spB n ((spEquiv n).symm ⟨s, hs⟩) := by
      rw [hkey, smul_smul, inv_mul_cancel₀ hrtne, one_smul]
    rw [hpm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have hcs : c s = 0 := by
      have hfac : c s * (spSign s - 1) = 0 := by rw [mul_sub, mul_one]; exact hrel s
      rcases mul_eq_zero.mp hfac with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hs
    rw [hcs, zero_smul]; exact Submodule.zero_mem _

/-- **The genuine `sp(2ⁿ)` as a `DLAHermBasis`.** The `(4ⁿ + 2ⁿ)/2`
symplectic (`θ=+1`, normalized) Pauli strings form a Hermitian
Hilbert–Schmidt orthonormal basis whose span is the symplectic algebra
`sp(2ⁿ)` (the `J₀`-skew-adjoint matrices), the dynamical Lie algebra generated
by `{i·P_s}`. -/
noncomputable def spHermBasis (n : ℕ) [NeZero n] : DLAHermBasis (spGens n) where
  dim := spDim n
  B := spB n
  herm := spB_isHermitian n
  ortho := spB_ortho n
  span_eq := by
    have ha : Submodule.span ℂ (Set.range (spB n)) ≤
        (skewAdjointMatricesSubmodule (Complex.I • pauliMat (siteY0 n))) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe]
      exact (mem_skewAdjoint_iff_theta (spB n i)).mpr (spB_theta n i)
    have hspan_eq : Submodule.span ℂ (Set.range (spB n)) =
        skewAdjointMatricesSubmodule (Complex.I • pauliMat (siteY0 n)) :=
      le_antisymm ha (fun A hA => mem_span_spB_of_sp hA)
    have hf : Submodule.span ℂ (Set.range (spB n)) ≤
        (dynamicalLieAlgebra (spGens n)).toSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, spB]
      refine Submodule.smul_mem _ _ ?_
      have hgen : Complex.I • pauliMat (spEquiv n i).1 ∈ dynamicalLieAlgebra (spGens n) :=
        LieSubalgebra.subset_lieSpan ⟨(spEquiv n i).1, (spEquiv n i).2, rfl⟩
      have hpm : pauliMat (spEquiv n i).1
          = (-Complex.I) • (Complex.I • pauliMat (spEquiv n i).1) := by
        rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      rw [hpm]
      exact Submodule.smul_mem _ _ hgen
    have hg : (dynamicalLieAlgebra (spGens n)).toSubmodule ≤
        skewAdjointMatricesSubmodule (Complex.I • pauliMat (siteY0 n)) := by
      have hsub : dynamicalLieAlgebra (spGens n)
          ≤ skewAdjointMatricesLieSubalgebra (Complex.I • pauliMat (siteY0 n)) := by
        apply dynamicalLieAlgebra_minimal
        rintro _ ⟨s, hs, rfl⟩
        rw [SetLike.mem_coe, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjoint_iff_theta,
          Matrix.transpose_smul,
          jconj_smul (Complex.I • pauliMat (siteY0 n)) ((pauliMat s)ᵀ) Complex.I,
          pauliMat_theta, hs, one_smul]
      intro x hx
      exact hsub hx
    exact le_antisymm hf (hg.trans hspan_eq.ge)

/-! ### The dimension count `dim sp(2ⁿ) = (4ⁿ + 2ⁿ)/2` -/

/-- `spSign` factorises over qubits with a sign twist on qubit `0`. -/
theorem spSign_eq_prod {n : ℕ} [NeZero n] (s : Fin n → Fin 4) :
    spSign s = ∏ k, (if k = 0 then -(ySign (s k) * yConjSign (s k)) else ySign (s k)) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun k => if k = 0 then -(ySign (s k) * yConjSign (s k))
        else ySign (s k)) (Finset.mem_univ (0 : Fin n)), if_pos rfl,
    Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk)),
    spSign, ← prod_ySign_eq,
    ← Finset.mul_prod_erase Finset.univ (fun k => ySign (s k)) (Finset.mem_univ (0 : Fin n))]
  ring

/-- `∑_s spSign s = 2ⁿ`. -/
theorem sum_spSign (n : ℕ) [NeZero n] : ∑ s : Fin n → Fin 4, spSign s = 2 ^ n := by
  rw [Finset.sum_congr rfl (fun s _ => spSign_eq_prod s), ← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 4)))
      (fun k a => if k = 0 then -(ySign a * yConjSign a) else ySign a)]
  have hF : ∀ k : Fin n,
      (∑ a : Fin 4, if k = 0 then -(ySign a * yConjSign a) else ySign a) = 2 := by
    intro k
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; rw [Fin.sum_univ_four]; simp [ySign, yConjSign]; norm_num
    · simp only [if_neg hk]; rw [Fin.sum_univ_four]; simp [ySign]; norm_num
  rw [Finset.prod_congr rfl (fun k _ => hF k), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- `spSign s = ±1`. -/
theorem spSign_eq_one_or {n : ℕ} [NeZero n] (s : Fin n → Fin 4) :
    spSign s = 1 ∨ spSign s = -1 := by
  have hb : yConjSign (s 0) * yConjSign (s 0) = 1 := by rw [yConjSign]; split <;> norm_num
  have ha : (-1 : ℂ) ^ yCount s * (-1) ^ yCount s = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hsq : spSign s * spSign s = 1 := by
    rw [spSign, neg_mul_neg, mul_mul_mul_comm, ha, hb, mul_one]
  exact mul_self_eq_one_iff.mp hsq

/-- **`2·dim sp(2ⁿ) = 4ⁿ + 2ⁿ`** (division-free). -/
theorem spDim_two_mul (n : ℕ) [NeZero n] : 2 * spDim n = 2 ^ n * 2 ^ n + 2 ^ n := by
  classical
  have htot : (Finset.univ.filter fun s : Fin n → Fin 4 => spSign s = 1).card
      + (Finset.univ.filter fun s : Fin n → Fin 4 => ¬ spSign s = 1).card = 2 ^ n * 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, card_pauliIndex]
  have hsplit : (((Finset.univ.filter fun s : Fin n → Fin 4 => spSign s = 1).card : ℂ))
      - ((Finset.univ.filter fun s : Fin n → Fin 4 => ¬ spSign s = 1).card : ℂ) = 2 ^ n := by
    rw [← sum_spSign n,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => spSign s = 1) spSign]
    have h1 : ∑ s ∈ Finset.univ.filter (fun s : Fin n → Fin 4 => spSign s = 1), spSign s
        = ((Finset.univ.filter fun s : Fin n → Fin 4 => spSign s = 1).card : ℂ) := by
      rw [Finset.sum_congr rfl (fun s hs => (Finset.mem_filter.mp hs).2), Finset.sum_const,
        nsmul_eq_mul, mul_one]
    have h2 : ∑ s ∈ Finset.univ.filter (fun s : Fin n → Fin 4 => ¬ spSign s = 1), spSign s
        = -((Finset.univ.filter fun s : Fin n → Fin 4 => ¬ spSign s = 1).card : ℂ) := by
      rw [Finset.sum_congr rfl (fun s hs => ?_), Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
      rcases spSign_eq_one_or s with h | h
      · exact absurd h (Finset.mem_filter.mp hs).2
      · exact h
    rw [h1, h2]; ring
  have hE : (Finset.univ.filter fun s : Fin n → Fin 4 => spSign s = 1).card
      = (Finset.univ.filter fun s : Fin n → Fin 4 => ¬ spSign s = 1).card + 2 ^ n := by
    have hcast : (((Finset.univ.filter fun s : Fin n → Fin 4 => spSign s = 1).card : ℂ))
        = ((Finset.univ.filter fun s : Fin n → Fin 4 => ¬ spSign s = 1).card : ℂ) + 2 ^ n := by
      rw [← hsplit]; ring
    exact_mod_cast hcast
  have hsoO : spDim n = (Finset.univ.filter fun s : Fin n → Fin 4 => spSign s = 1).card := by
    rw [spDim, Fintype.card_subtype]
  omega

/-- **`dim sp(2ⁿ) = (4ⁿ + 2ⁿ)/2`**. -/
theorem spDim_eq (n : ℕ) [NeZero n] : spDim n = (2 ^ n * 2 ^ n + 2 ^ n) / 2 := by
  have := spDim_two_mul n; omega

/-! ### The single-ideal variance reduction and the exponential barren plateau -/

@[simp] theorem spHermBasis_dim (n : ℕ) [NeZero n] : (spHermBasis n).dim = spDim n := rfl

/-- **The `g ≃ sp(2ⁿ)` loss-variance reduction.** Under the Haar second-moment bundle and Hermitian
`ρ`, `O`, the loss variance of the symplectic dynamical Lie algebra collapses to the single term
`Var_θ[ℓ] = P_g(ρ)·P_g(O) / dim sp(2ⁿ)`, with `dim sp(2ⁿ) = (4ⁿ + 2ⁿ)/2`
[RBS+23, Arxiv_Final.tex:691]. Downstream of the proved `variance_eq_gPurity`; the symplectic
analogue of `SimpleSU.main`. -/
theorem SimpleSp.main {n : ℕ} [NeZero n] {ρ O : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (M : RagoneSecondMoment (spHermBasis n) ρ O) (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hpos : 0 < spDim n) :
    (M.variance : ℂ) = (spHermBasis n).gPurity ρ * (spHermBasis n).gPurity O
      / (((2 ^ n * 2 ^ n + 2 ^ n) / 2 : ℕ) : ℂ) := by
  rw [M.variance_eq_gPurity hρ hO (by rwa [spHermBasis_dim]), spHermBasis_dim, spDim_eq]

/-- `2ⁿ ≤ dim sp(2ⁿ⁺¹)`, so the dimension grows exponentially. -/
theorem two_pow_le_spDim_succ (n : ℕ) : 2 ^ n ≤ spDim (n + 1) := by
  have h := spDim_two_mul (n + 1)
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  nlinarith [h, h2]

theorem spDim_succ_pos (n : ℕ) : 0 < spDim (n + 1) :=
  lt_of_lt_of_le (by positivity) (two_pow_le_spDim_succ n)

/-- The index of the first `sp(2ⁿ⁺¹)` basis element. -/
def spI0 (n : ℕ) : Fin (spHermBasis (n + 1)).dim :=
  ⟨0, by rw [spHermBasis_dim]; exact spDim_succ_pos n⟩

/-- The Ragone second-moment bundle for the `sp(2ⁿ⁺¹)` qubit family, with both Hermitian witness
operators chosen as the first normalized basis element, given the Schur hypothesis `hSchur` (H2).
Since `sp(2ⁿ⁺¹)` is **traceless** the centered `(g⊗g)^g` genuinely equals `span{C}`, so `hSchur`
is true in principle — a deferred named input, not a circular posit. -/
noncomputable def spSM (n : ℕ)
    (hSchur : gTensorGInvariant (spHermBasis (n + 1))
      = Submodule.span ℂ {(spHermBasis (n + 1)).casimir}) :
    RagoneSecondMoment (spHermBasis (n + 1))
      ((spHermBasis (n + 1)).B (spI0 n)) ((spHermBasis (n + 1)).B (spI0 n)) :=
  RagoneSecondMoment.consistencyWitness ((spHermBasis (n + 1)).herm (spI0 n))
    ((spHermBasis (n + 1)).herm (spI0 n)) (by rw [spHermBasis_dim]; exact spDim_succ_pos n) hSchur

/-- **The `sp(2ⁿ)` single-ideal reduction, witnessed.** With `ρ = O` a normalized basis element,
given the Schur hypothesis the loss variance is `1 / dim sp(2ⁿ⁺¹) = 2 / (4ⁿ⁺¹ + 2ⁿ⁺¹)`, vanishing
exponentially [RBS+23, Arxiv_Final.tex:691]. -/
theorem spN_variance_value (n : ℕ)
    (hSchur : gTensorGInvariant (spHermBasis (n + 1))
      = Submodule.span ℂ {(spHermBasis (n + 1)).casimir}) :
    ((spSM n hSchur).variance : ℂ) = 1 / (spDim (n + 1) : ℂ) := by
  rw [(spSM n hSchur).variance_eq_gPurity ((spHermBasis (n + 1)).herm (spI0 n))
      ((spHermBasis (n + 1)).herm (spI0 n)) (by rw [spHermBasis_dim]; exact spDim_succ_pos n)]
  simp only [DLAHermBasis.gPurity_basis_elem, one_mul, spHermBasis_dim]

/-- **Bundle-quantified exponential barren plateau for `sp(2ⁿ)`.** For any genuine
`RagoneSecondMoment` family on the concrete `sp(2ⁿ⁺¹)` Pauli-string basis, bounded `g`-purity
numerator and exponential DLA dimension imply a barren plateau. This theorem consumes the H1/H2
second-moment bundle as data; it does not manufacture a circuit ensemble or use the diagonal
consistency witness. -/
theorem spN_hasBarrenPlateau
    {ρ O : (n : ℕ) → Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ}
    (M : (n : ℕ) → RagoneSecondMoment (spHermBasis (n + 1)) (ρ n) (O n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n,
      ‖(spHermBasis (n + 1)).gPurity (ρ n) * (spHermBasis (n + 1)).gPurity (O n)‖ ≤ C) :
    HasBarrenPlateau (fun n => (M n).variance) := by
  refine ragone_hasBarrenPlateau M hρ hO
    (fun n => by rw [spHermBasis_dim]; exact spDim_succ_pos n)
    hC hbound (base := 2) one_lt_two ?_
  intro n
  rw [spHermBasis_dim]
  exact_mod_cast two_pow_le_spDim_succ n

end QuantumAlg
