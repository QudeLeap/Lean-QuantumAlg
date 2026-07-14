/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliStringDLA
public import Mathlib.Algebra.Lie.Classical

/-!
# The `n`-qubit Pauli realization of `so(2ⁿ)` and the orthogonal-DLA barren plateau

The `n`-qubit Pauli strings split by transpose parity: `(P_s)ᵀ = (-1)^{#Y(s)} · P_s`, because only
the `Y` factor is antisymmetric (`Xᵀ = X`, `Zᵀ = Z`, `Iᵀ = I`, `Yᵀ = -Y`). The Pauli strings with an
**odd** number of `Y` factors are therefore (complex) skew-symmetric, and there are exactly
`(4ⁿ − 2ⁿ)/2 = dim so(2ⁿ)` of them, so they form a Hermitian, Hilbert–Schmidt orthonormal basis of
the orthogonal Lie algebra `so(2ⁿ, ℂ)` (the skew-symmetric matrices). This realises the genuine
`so(2ⁿ)` dynamical Lie algebra as a `DLAHermBasis`, so the single-ideal Ragone variance reduction
`Var = P_g(ρ)·P_g(O) / dim g` and the exponential barren plateau hold on a concrete qubit family —
the orthogonal analogue of the seminal `su(2ⁿ)` case.

This file follows the same architecture as the `su(2ⁿ)` construction (`PauliStringDLA.lean`): the
abstract simple-DLA reduction is `SimpleSO.main`, and the genuine `so(2ⁿ)` basis makes it
non-vacuous on the qubit family.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Pauli transpose parity

Only the single-qubit `Y` (label `2`) is antisymmetric, so transposing a Pauli string multiplies it
by `(-1)^{#Y}`, recorded multiplicatively as `∏ₖ ySign (sₖ)`. -/

/-- The transpose sign of a single-qubit Pauli label: `-1` for `Y` (label `2`), `+1` otherwise. -/
noncomputable def ySign (a : Fin 4) : ℂ := if a = 2 then -1 else 1

/-- Single-qubit Pauli transpose: `σ_aᵀ = ySign a · σ_a` (only `Y` flips sign). -/
theorem pauli1_transpose (a : Fin 4) : (pauli1 a)ᵀ = ySign a • pauli1 a := by
  fin_cases a <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli1, ySign, pauliX, pauliY, pauliZ, Matrix.transpose_apply, Matrix.smul_apply])

/-- **Pauli-string transpose parity**: `(P_s)ᵀ = (∏ₖ ySign sₖ) · P_s = (-1)^{#Y(s)} · P_s`. -/
theorem pauliStr_transpose {n : ℕ} (s : Fin n → Fin 4) :
    (pauliStr s)ᵀ = (∏ k, ySign (s k)) • pauliStr s := by
  ext i j
  simp only [Matrix.transpose_apply, pauliStr, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := congrFun (congrFun (pauli1_transpose (s k)) (i k)) (j k)
  simpa only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] using h

/-- The same parity on the `Fin (2ⁿ)` reindexing used by `DLAHermBasis`. -/
theorem pauliMat_transpose {n : ℕ} (s : Fin n → Fin 4) :
    (pauliMat s)ᵀ = (∏ k, ySign (s k)) • pauliMat s := by
  ext p q
  have h := congrFun (congrFun (pauliStr_transpose s)
      (finFunctionFinEquiv.symm p)) (finFunctionFinEquiv.symm q)
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
  simpa only [Matrix.transpose_apply, pauliMat, Matrix.submatrix_apply, Matrix.smul_apply,
    smul_eq_mul] using h

/-! ### The full Pauli basis of `gl(2ⁿ)`

The `4ⁿ` Pauli strings are Hilbert–Schmidt orthogonal (`⟪P_s, P_t⟫ = 2ⁿ δ_{st}`), hence linearly
independent, and there are exactly `4ⁿ = (2ⁿ)² = dim gl(2ⁿ)` of them, so they span the whole matrix
algebra. This lets us read off the Pauli coordinates of any matrix and split a skew-symmetric matrix
by transpose parity. -/

/-- The `4ⁿ` Pauli strings are linearly independent (from Hilbert–Schmidt orthogonality). -/
theorem pauliMat_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (fun s : Fin n → Fin 4 => pauliMat s) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have h1 : hsInner (pauliMat s) (∑ t, c t • pauliMat t) = c s * (2 ^ n : ℂ) := by
    rw [hsInner_sum_right]
    have hterm : ∀ t, hsInner (pauliMat s) (c t • pauliMat t)
        = if s = t then c t * (2 ^ n : ℂ) else 0 := fun t => by
      rw [hsInner_smul_right, pauliMat_hsInner, mul_ite, mul_zero]
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_ite_eq]
    simp
  rw [hc] at h1
  simp only [hsInner, Matrix.mul_zero, Matrix.trace_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_right (pow_ne_zero n two_ne_zero)

/-- The Pauli index type has `4ⁿ = 2ⁿ·2ⁿ` elements. -/
theorem card_pauliIndex (n : ℕ) : Fintype.card (Fin n → Fin 4) = 2 ^ n * 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, show (4 : ℕ) = 2 * 2 from rfl, mul_pow]

/-- **The `4ⁿ` Pauli strings span `gl(2ⁿ)`** (a linearly independent family of full dimension). -/
theorem pauliMat_span_top (n : ℕ) :
    Submodule.span ℂ (Set.range (fun s : Fin n → Fin 4 => pauliMat s)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hM : Module.finrank ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) = 2 ^ n * 2 ^ n := by
    simp [Module.finrank_matrix]
  rw [finrank_span_eq_card (pauliMat_linearIndependent n), card_pauliIndex, hM]

/-! ### The odd-`#Y` (skew-symmetric) Pauli strings as a candidate basis -/

/-- The number of `Y` factors (label `2`) in a Pauli string. -/
def yCount {n : ℕ} (s : Fin n → Fin 4) : ℕ := (Finset.univ.filter fun k => s k = 2).card

/-- The transpose sign is `(-1)^{#Y}`. -/
theorem prod_ySign_eq {n : ℕ} (s : Fin n → Fin 4) :
    (∏ k, ySign (s k)) = (-1 : ℂ) ^ yCount s := by
  have h1 : ∀ k ∈ Finset.univ.filter (fun k => s k = 2), ySign (s k) = (-1 : ℂ) := by
    intro k hk; simp only [Finset.mem_filter] at hk; simp [ySign, hk.2]
  have h2 : ∀ k ∈ Finset.univ.filter (fun k => ¬ s k = 2), ySign (s k) = (1 : ℂ) := by
    intro k hk; simp only [Finset.mem_filter] at hk; simp [ySign, hk.2]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => s k = 2),
    Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_const,
    Finset.prod_const_one, mul_one]
  rfl

/-- Dimension of the orthogonal basis: the count of odd-`#Y` Pauli strings. -/
def soDim (n : ℕ) : ℕ := Fintype.card {s : Fin n → Fin 4 // Odd (yCount s)}

/-- An enumeration of the odd-`#Y` Pauli labels. -/
noncomputable def soEquiv (n : ℕ) : Fin (soDim n) ≃ {s : Fin n → Fin 4 // Odd (yCount s)} :=
  (Fintype.equivFin _).symm

/-- The odd-`#Y` Pauli generators `{i·P_s : #Y(s) odd}` of the `so(2ⁿ)` dynamical Lie algebra. -/
def soGens (n : ℕ) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4, Odd (yCount s) ∧ A = Complex.I • pauliMat s}

/-- The candidate Hermitian orthonormal basis of `so(2ⁿ)`: the normalized odd-`#Y` Pauli strings. -/
noncomputable def soB (n : ℕ) (i : Fin (soDim n)) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  rtNinv n • pauliMat (soEquiv n i).1

theorem soB_isHermitian (n : ℕ) (i : Fin (soDim n)) : (soB n i)ᴴ = soB n i := by
  rw [soB, conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]

theorem soB_ortho (n : ℕ) (i j : Fin (soDim n)) :
    hsInner (soB n i) (soB n j) = if i = j then 1 else 0 := by
  rw [soB, soB, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply, rtNinv_conj, ← mul_assoc,
    rtNinv_mul_self, pauliMat_hsInner]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, one_div,
      inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg h, if_neg (fun he => h ((soEquiv n).injective (Subtype.ext he))), mul_zero]

theorem soB_linearIndependent (n : ℕ) : LinearIndependent ℂ (soB n) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : hsInner (soB n i) (∑ j, c j • soB n j) = c i := by
    rw [hsInner_sum_right]
    have hterm : ∀ j, hsInner (soB n i) (c j • soB n j) = if i = j then c j else 0 := by
      intro j; rw [hsInner_smul_right, soB_ortho]; split <;> simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq]
    simp
  rw [hc] at h1
  simpa [hsInner] using h1.symm

theorem soB_span_finrank (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (soB n))) = soDim n := by
  rw [finrank_span_eq_card (soB_linearIndependent n), Fintype.card_fin]

/-! ### `span{soB} = so(2ⁿ)` via transpose parity and the Pauli basis -/

/-- Each odd-`#Y` basis element is skew-symmetric. -/
theorem soB_skew (n : ℕ) (i : Fin (soDim n)) : (soB n i)ᵀ = -(soB n i) := by
  simp only [soB, Matrix.transpose_smul, pauliMat_transpose, prod_ySign_eq,
    Odd.neg_one_pow (soEquiv n i).2, neg_one_smul, smul_neg]

/-- **Every skew-symmetric matrix is a span of odd-`#Y` Pauli strings.** Expanding `A` in the full
Pauli basis, the transpose parity forces the even-`#Y` (symmetric) coordinates to vanish. -/
theorem mem_span_soB_of_skew {n : ℕ} {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hA : Aᵀ = -A) : A ∈ Submodule.span ℂ (Set.range (soB n)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (show A ∈ Submodule.span ℂ (Set.range (fun s : Fin n → Fin 4 => pauliMat s)) by
      rw [pauliMat_span_top]; exact Submodule.mem_top)
  have hAt : Aᵀ = ∑ s, (c s * (∏ k, ySign (s k))) • pauliMat s := by
    have h0 : (∑ s, c s • pauliMat s)ᵀ = ∑ s, (c s • pauliMat s)ᵀ := by
      ext p q; simp [Matrix.transpose_apply, Matrix.sum_apply]
    rw [← hc, h0]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.transpose_smul, pauliMat_transpose, smul_smul]
  have hsum : ∑ s, (c s * (∏ k, ySign (s k)) + c s) • pauliMat s = 0 := by
    have hz : (∑ s, (c s * (∏ k, ySign (s k))) • pauliMat s) + (∑ s, c s • pauliMat s) = 0 := by
      rw [← hAt, hc, hA, neg_add_cancel]
    rw [← Finset.sum_add_distrib] at hz
    simpa only [← add_smul] using hz
  have hrel := Fintype.linearIndependent_iff.mp (pauliMat_linearIndependent n)
    (fun s => c s * (∏ k, ySign (s k)) + c s) hsum
  have hrtne : rtNinv n ≠ 0 := by
    intro h; have hm := rtNinv_mul_self n; rw [h, mul_zero] at hm
    exact (one_div_ne_zero (pow_ne_zero n (two_ne_zero))) hm.symm
  rw [← hc]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : Odd (yCount s)
  · refine Submodule.smul_mem _ _ ?_
    have hkey : soB n ((soEquiv n).symm ⟨s, hs⟩) = rtNinv n • pauliMat s := by
      simp only [soB, Equiv.apply_symm_apply]
    have hpm : pauliMat s = (rtNinv n)⁻¹ • soB n ((soEquiv n).symm ⟨s, hs⟩) := by
      rw [hkey, smul_smul, inv_mul_cancel₀ hrtne, one_smul]
    rw [hpm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have h1 : (∏ k, ySign (s k)) = (1 : ℂ) := by
      rw [prod_ySign_eq, (Nat.not_odd_iff_even.mp hs).neg_one_pow]
    have hcs : c s = 0 := by
      have hr := hrel s; rw [h1, mul_one] at hr; exact add_self_eq_zero.mp hr
    rw [hcs, zero_smul]; exact Submodule.zero_mem _

/-- **The odd-`#Y` Pauli basis spans Mathlib's complex orthogonal Lie algebra.** -/
theorem soB_span_orthogonal_so (n : ℕ) :
    Submodule.span ℂ (Set.range (soB n)) =
      (LieAlgebra.Orthogonal.so (Fin (2 ^ n)) ℂ).toSubmodule := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LieSubalgebra.mem_toSubmodule, LieAlgebra.Orthogonal.mem_so]
    exact soB_skew n i
  · intro A hA
    rw [LieSubalgebra.mem_toSubmodule, LieAlgebra.Orthogonal.mem_so] at hA
    exact mem_span_soB_of_skew hA

/-- The odd-`#Y` Pauli basis spans exactly the dynamical Lie algebra generated by the
skew-Hermitian odd-`#Y` Pauli generators. -/
theorem soB_span_dla (n : ℕ) :
    Submodule.span ℂ (Set.range (soB n)) = (dynamicalLieAlgebra (soGens n)).toSubmodule := by
  have hf : Submodule.span ℂ (Set.range (soB n)) ≤
      (dynamicalLieAlgebra (soGens n)).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, soB]
    refine Submodule.smul_mem _ _ ?_
    have hgen : Complex.I • pauliMat (soEquiv n i).1 ∈ dynamicalLieAlgebra (soGens n) :=
      LieSubalgebra.subset_lieSpan ⟨(soEquiv n i).1, (soEquiv n i).2, rfl⟩
    have hpm : pauliMat (soEquiv n i).1
        = (-Complex.I) • (Complex.I • pauliMat (soEquiv n i).1) := by
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    rw [hpm]
    exact Submodule.smul_mem _ _ hgen
  have hg : (dynamicalLieAlgebra (soGens n)).toSubmodule ≤
      (LieAlgebra.Orthogonal.so (Fin (2 ^ n)) ℂ).toSubmodule := by
    have hsub : dynamicalLieAlgebra (soGens n) ≤ LieAlgebra.Orthogonal.so (Fin (2 ^ n)) ℂ := by
      apply dynamicalLieAlgebra_minimal
      rintro _ ⟨s, hs, rfl⟩
      rw [SetLike.mem_coe, LieAlgebra.Orthogonal.mem_so, Matrix.transpose_smul, pauliMat_transpose,
        prod_ySign_eq, Odd.neg_one_pow hs, neg_one_smul, smul_neg]
    intro x hx
    exact hsub hx
  exact le_antisymm hf (hg.trans (soB_span_orthogonal_so n).ge)

/-- **The odd-`#Y` Pauli generators have DLA exactly Mathlib's `so(2ⁿ, ℂ)`.** -/
theorem soDLA_eq_orthogonalSo (n : ℕ) :
    dynamicalLieAlgebra (soGens n) = LieAlgebra.Orthogonal.so (Fin (2 ^ n)) ℂ := by
  ext A
  change A ∈ (dynamicalLieAlgebra (soGens n)).toSubmodule ↔
    A ∈ (LieAlgebra.Orthogonal.so (Fin (2 ^ n)) ℂ).toSubmodule
  rw [← soB_span_dla n, soB_span_orthogonal_so n]

/-- **The genuine `so(2ⁿ)` as a `DLAHermBasis`.** The `(4ⁿ − 2ⁿ)/2` odd-`#Y` (normalized) Pauli
strings form a Hermitian Hilbert–Schmidt orthonormal basis whose span is the orthogonal algebra
`so(2ⁿ)` (the skew-symmetric matrices), the dynamical Lie algebra generated by
`{i·P_s : #Y(s) odd}`. -/
noncomputable def soHermBasis (n : ℕ) : DLAHermBasis (soGens n) where
  dim := soDim n
  B := soB n
  herm := soB_isHermitian n
  ortho := soB_ortho n
  span_eq := soB_span_dla n

/-! ### The dimension count `dim so(2ⁿ) = (4ⁿ − 2ⁿ)/2` -/

/-- The signed Pauli count: `∑_s (-1)^{#Y(s)} = ∏_k (∑_a ySign a) = 2ⁿ`. -/
theorem sum_ySign_pow (n : ℕ) : ∑ s : Fin n → Fin 4, (-1 : ℂ) ^ yCount s = 2 ^ n := by
  have h1 : ∑ s : Fin n → Fin 4, (-1 : ℂ) ^ yCount s
      = ∑ s : Fin n → Fin 4, ∏ k, ySign (s k) :=
    Finset.sum_congr rfl fun s _ => (prod_ySign_eq s).symm
  rw [h1, ← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 4))) (fun _ a => ySign a)]
  have hsum4 : (∑ a : Fin 4, ySign a) = 2 := by rw [Fin.sum_univ_four]; simp [ySign]; norm_num
  simp only [hsum4, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`2·dim so(2ⁿ) + 2ⁿ = 4ⁿ`** — the division-free count of odd-`#Y` Pauli strings. -/
theorem soDim_two_mul (n : ℕ) : 2 * soDim n + 2 ^ n = 2 ^ n * 2 ^ n := by
  have htot : (Finset.univ.filter fun s : Fin n → Fin 4 => Odd (yCount s)).card
      + (Finset.univ.filter fun s : Fin n → Fin 4 => ¬ Odd (yCount s)).card = 2 ^ n * 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, card_pauliIndex]
  have hsplit : (((Finset.univ.filter fun s : Fin n → Fin 4 => ¬ Odd (yCount s)).card : ℂ))
      - ((Finset.univ.filter fun s : Fin n → Fin 4 => Odd (yCount s)).card : ℂ) = 2 ^ n := by
    rw [← sum_ySign_pow n, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun s => Odd (yCount s)) (fun s => (-1 : ℂ) ^ yCount s)]
    have hOdd : ∑ s ∈ Finset.univ.filter (fun s : Fin n → Fin 4 => Odd (yCount s)),
        (-1 : ℂ) ^ yCount s
        = -(((Finset.univ.filter fun s : Fin n → Fin 4 => Odd (yCount s)).card : ℂ)) := by
      rw [Finset.sum_congr rfl (fun s hs => Odd.neg_one_pow (Finset.mem_filter.mp hs).2),
        Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
    have hEven : ∑ s ∈ Finset.univ.filter (fun s : Fin n → Fin 4 => ¬ Odd (yCount s)),
        (-1 : ℂ) ^ yCount s
        = ((Finset.univ.filter fun s : Fin n → Fin 4 => ¬ Odd (yCount s)).card : ℂ) := by
      rw [Finset.sum_congr rfl (fun s hs =>
        (Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hs).2).neg_one_pow),
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hOdd, hEven]; ring
  have hE_eq : (Finset.univ.filter fun s : Fin n → Fin 4 => ¬ Odd (yCount s)).card
      = (Finset.univ.filter fun s : Fin n → Fin 4 => Odd (yCount s)).card + 2 ^ n := by
    have hcast : (((Finset.univ.filter fun s : Fin n → Fin 4 => ¬ Odd (yCount s)).card : ℂ))
        = ((Finset.univ.filter fun s : Fin n → Fin 4 => Odd (yCount s)).card : ℂ) + 2 ^ n := by
      rw [← hsplit]; ring
    exact_mod_cast hcast
  have hsoO : soDim n = (Finset.univ.filter fun s : Fin n → Fin 4 => Odd (yCount s)).card := by
    rw [soDim, Fintype.card_subtype]
  omega

/-- **`dim so(2ⁿ) = (4ⁿ − 2ⁿ)/2`**. -/
theorem soDim_eq (n : ℕ) : soDim n = (2 ^ n * 2 ^ n - 2 ^ n) / 2 := by
  have := soDim_two_mul n; omega

/-! ### The single-ideal variance reduction and the exponential barren plateau -/

@[simp] theorem soHermBasis_dim (n : ℕ) : (soHermBasis n).dim = soDim n := rfl

/-- **Closed-form dimension of the `so(2ⁿ)` Pauli DLA basis.** -/
theorem soHermBasis_dim_closedForm (n : ℕ) :
    (soHermBasis n).dim = (2 ^ n * 2 ^ n - 2 ^ n) / 2 := by
  rw [soHermBasis_dim, soDim_eq]

/-- **The `g ≃ so(2ⁿ)` loss-variance reduction.** Under the Haar second-moment bundle and Hermitian
`ρ`, `O`, the loss variance of the orthogonal dynamical Lie algebra collapses to the single term
`Var_θ[ℓ] = P_g(ρ)·P_g(O) / dim so(2ⁿ)`, with `dim so(2ⁿ) = (4ⁿ − 2ⁿ)/2`
[RBS+23, Arxiv_Final.tex:691]. Downstream of the proved `variance_eq_gPurity`; the orthogonal
analogue of `SimpleSU.main`. -/
theorem SimpleSO.main {n : ℕ} {ρ O : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (M : RagoneSecondMoment (soHermBasis n) ρ O) (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hpos : 0 < soDim n) :
    (M.variance : ℂ) = (soHermBasis n).gPurity ρ * (soHermBasis n).gPurity O
      / (((2 ^ n * 2 ^ n - 2 ^ n) / 2 : ℕ) : ℂ) := by
  rw [M.variance_eq_gPurity hρ hO (by rwa [soHermBasis_dim]), soHermBasis_dim, soDim_eq]

/-- `2ⁿ ≤ dim so(2ⁿ⁺¹)`, so the dimension grows exponentially (used for the barren plateau). -/
theorem two_pow_le_soDim_succ (n : ℕ) : 2 ^ n ≤ soDim (n + 1) := by
  have h := soDim_two_mul (n + 1)
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hsq : 2 ^ n ≤ 2 ^ n * 2 ^ n := Nat.le_mul_of_pos_left _ (by positivity : 0 < 2 ^ n)
  rw [h2] at h
  nlinarith [h, hsq]

theorem soDim_succ_pos (n : ℕ) : 0 < soDim (n + 1) :=
  lt_of_lt_of_le (by positivity) (two_pow_le_soDim_succ n)

/-- The index of the first `so(2ⁿ⁺¹)` basis element. -/
def soI0 (n : ℕ) : Fin (soHermBasis (n + 1)).dim :=
  ⟨0, by rw [soHermBasis_dim]; exact soDim_succ_pos n⟩

/-- The Ragone second-moment bundle for the `so(2ⁿ⁺¹)` qubit family, with both Hermitian witness
operators chosen as the first normalized basis element, given the Schur hypothesis `hSchur`
(H2). For the
**simple** members `so(2ᵐ)` with `m ≥ 3` the identity `(g⊗g)^g = span{C}` is genuinely proved
(`soHermBasis_schur`); it is FALSE at `so(4)` (`m = 2`, semisimple `su(2) ⊕ su(2)`, a
two-dimensional
commutant) and degenerate at `so(2)` (`m = 1`, abelian). Here `hSchur` is therefore a named input
covering the member at hand, not a proved fact of every member. -/
noncomputable def soSM (n : ℕ)
    (hSchur : gTensorGInvariant (soHermBasis (n + 1))
      = Submodule.span ℂ {(soHermBasis (n + 1)).casimir}) :
    RagoneSecondMoment (soHermBasis (n + 1))
      ((soHermBasis (n + 1)).B (soI0 n)) ((soHermBasis (n + 1)).B (soI0 n)) :=
  RagoneSecondMoment.consistencyWitness ((soHermBasis (n + 1)).herm (soI0 n))
    ((soHermBasis (n + 1)).herm (soI0 n)) (by rw [soHermBasis_dim]; exact soDim_succ_pos n) hSchur

/-- **The `so(2ⁿ)` single-ideal reduction, witnessed.** With `ρ = O` a normalized basis element
(`P_g = 1`), given the Schur hypothesis the loss variance is `1 / dim so(2ⁿ⁺¹) = 2 / (4ⁿ⁺¹ − 2ⁿ⁺¹)`,
vanishing exponentially in the qubit count — the orthogonal analogue of the `su(2ⁿ)` reduction
[RBS+23, Arxiv_Final.tex:691]. -/
theorem soN_variance_value (n : ℕ)
    (hSchur : gTensorGInvariant (soHermBasis (n + 1))
      = Submodule.span ℂ {(soHermBasis (n + 1)).casimir}) :
    ((soSM n hSchur).variance : ℂ) = 1 / (soDim (n + 1) : ℂ) := by
  rw [(soSM n hSchur).variance_eq_gPurity ((soHermBasis (n + 1)).herm (soI0 n))
      ((soHermBasis (n + 1)).herm (soI0 n)) (by rw [soHermBasis_dim]; exact soDim_succ_pos n)]
  simp only [DLAHermBasis.gPurity_basis_elem, one_mul, soHermBasis_dim]

/-- **Bundle-quantified exponential barren plateau for the simple `so(2ᵐ)` qubit family.** For any
genuine `RagoneSecondMoment` family on `so(2ⁿ⁺³) = so(8), so(16), ...`, bounded `g`-purity numerator
and exponential DLA dimension imply a barren plateau. Starting at `m = 3` is load-bearing:
`so(2)` is abelian and `so(4)` is reductive with a two-Casimir invariant space. -/
theorem soN_hasBarrenPlateau
    {ρ O : (n : ℕ) → Matrix (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) ℂ}
    (M : (n : ℕ) → RagoneSecondMoment (soHermBasis (n + 3)) (ρ n) (O n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n,
      ‖(soHermBasis (n + 3)).gPurity (ρ n) * (soHermBasis (n + 3)).gPurity (O n)‖ ≤ C) :
    HasBarrenPlateau (fun n => (M n).variance) := by
  refine ragone_hasBarrenPlateau M hρ hO
    (fun n => by rw [soHermBasis_dim]; exact soDim_succ_pos (n + 2))
    hC hbound (base := 2) one_lt_two ?_
  intro n
  rw [soHermBasis_dim]
  have h1 : (2 : ℕ) ^ n ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast le_trans h1 (two_pow_le_soDim_succ (n + 2))

end QuantumAlg
