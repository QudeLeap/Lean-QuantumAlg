/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.SimpleDLA
public import QuantumAlg.Util.Haar

/-!
# The `n`-qubit Pauli-string basis of `su(2ⁿ)` and the McClean barren plateau

The `4ⁿ` Pauli strings `P_s = σ_{s₁} ⊗ ⋯ ⊗ σ_{sₙ}`
(`s : Fin n → Fin 4`, `σ₀=I, σ₁=X, σ₂=Y, σ₃=Z`) are a Hermitian,
Hilbert–Schmidt orthonormal basis of `gl(2ⁿ, ℂ)`; the `4ⁿ − 1`
**non-identity** ones
(`s ≠ 0`) are an orthonormal Hermitian basis of the traceless algebra `su(2ⁿ)` (dimension `4ⁿ − 1`).
This realises the genuine `su(2ⁿ)` dynamical Lie algebra as a `DLAHermBasis`, so the
`SimpleSU` reduction `Var = P_g(ρ)·P_g(O)/(4ⁿ − 1)` and the exponential barren plateau hold on a
concrete qubit family — the seminal `su(2ⁿ)`/2-design case [MBS+18, maintext.tex:148], whose
`Var = (1/(4ⁿ − 1)) Tr[O_g²] Tr[ρ_g²]` reduction is recovered as the `g = su(2ⁿ)` special case of
the Ragone framework [RBS+23, Arxiv_Final.tex:825-828].

Pauli strings are indexed over the register type `Fin n → Fin 2`;
`P_s i j = ∏ₖ σ_{sₖ}(iₖ, jₖ)`. Orthonormality `⟪P_s, P_t⟫ = 2ⁿ δ_{st}`
factorises over the qubits. The `span_eq` of the DLA is proved by the
trace-codimension argument (the traceless subspace is a Lie subalgebra and
equals `span{non-identity Paulis}` by dimension), avoiding the Pauli
multiplication rule.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Single-qubit Pauli matrices by label -/

/-- Single-qubit Pauli matrix: `0 ↦ I`, `1 ↦ X`, `2 ↦ Y`, `3 ↦ Z`. -/
noncomputable def pauli1 (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then 1 else if a = 1 then pauliX else if a = 2 then pauliY else pauliZ

theorem pauli1_isHermitian (a : Fin 4) : (pauli1 a)ᴴ = pauli1 a := by
  fin_cases a <;>
    simp [pauli1, conjTranspose_one, pauliX_isHermitian, pauliY_isHermitian, pauliZ_isHermitian]

/-- Single-qubit Pauli orthogonality: `Tr[σ_a σ_b] = 2 δ_{ab}`. -/
theorem pauli1_trace_mul (a b : Fin 4) :
    (pauli1 a * pauli1 b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauli1, pauliX, pauliY, pauliZ, Matrix.trace_fin_two, Complex.I_mul_I] <;> norm_num

/-! ### `n`-qubit Pauli strings over the register index `Fin n → Fin 2` -/

/-- The `n`-qubit Pauli string `P_s` with single-qubit labels `s : Fin n → Fin 4`, as a matrix over
the register index `Fin n → Fin 2`: `P_s i j = ∏ₖ σ_{sₖ}(iₖ, jₖ)`. -/
noncomputable def pauliStr {n : ℕ} (s : Fin n → Fin 4) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun i j => ∏ k, pauli1 (s k) (i k) (j k)

theorem pauliStr_isHermitian {n : ℕ} (s : Fin n → Fin 4) : (pauliStr s)ᴴ = pauliStr s := by
  ext i j
  simp only [Matrix.conjTranspose_apply, pauliStr, Matrix.of_apply]
  rw [← starRingEnd_apply, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [starRingEnd_apply]
  have h := congrFun (congrFun (pauli1_isHermitian (s k)) (i k)) (j k)
  rwa [Matrix.conjTranspose_apply] at h

/-- **Pauli-string trace factorises over qubits**:
`Tr[P_s P_t] = ∏ₖ Tr[σ_{sₖ} σ_{tₖ}]`. -/
theorem pauliStr_trace_mul {n : ℕ} (s t : Fin n → Fin 4) :
    (pauliStr s * pauliStr t).trace = ∏ k, (pauli1 (s k) * pauli1 (t k)).trace := by
  have hLHS : (pauliStr s * pauliStr t).trace
      = ∑ c : Fin n → Fin 2 × Fin 2,
          ∏ k, pauli1 (s k) (c k).1 (c k).2 * pauli1 (t k) (c k).2 (c k).1 := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, pauliStr, Matrix.of_apply,
      ← Finset.prod_mul_distrib]
    rw [← Fintype.sum_prod_type (fun q : (Fin n → Fin 2) × (Fin n → Fin 2) =>
          ∏ k, pauli1 (s k) (q.1 k) (q.2 k) * pauli1 (t k) (q.2 k) (q.1 k)),
      ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 2) (fun _ => Fin 2))
          (fun q : (Fin n → Fin 2) × (Fin n → Fin 2) =>
            ∏ k, pauli1 (s k) (q.1 k) (q.2 k) * pauli1 (t k) (q.2 k) (q.1 k))]
    rfl
  have hfac : ∀ k, (pauli1 (s k) * pauli1 (t k)).trace
      = ∑ p : Fin 2 × Fin 2, pauli1 (s k) p.1 p.2 * pauli1 (t k) p.2 p.1 := by
    intro k
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
  have hRHS : (∏ k, (pauli1 (s k) * pauli1 (t k)).trace)
      = ∑ c : Fin n → Fin 2 × Fin 2,
          ∏ k, pauli1 (s k) (c k).1 (c k).2 * pauli1 (t k) (c k).2 (c k).1 := by
    rw [Finset.prod_congr rfl fun k _ => hfac k,
      Finset.prod_univ_sum (fun _ => Finset.univ)
        (fun (k : Fin n) (p : Fin 2 × Fin 2) => pauli1 (s k) p.1 p.2 * pauli1 (t k) p.2 p.1)]
    apply Finset.sum_congr
    · exact Fintype.piFinset_univ
    · intro c _; rfl
  rw [hLHS, hRHS]

theorem pauliStr_hsInner {n : ℕ} (s t : Fin n → Fin 4) :
    hsInner (pauliStr s) (pauliStr t) = if s = t then (2 ^ n : ℂ) else 0 := by
  rw [hsInner, pauliStr_isHermitian, pauliStr_trace_mul]
  have hterm : ∀ k, (pauli1 (s k) * pauli1 (t k)).trace = if s k = t k then (2 : ℂ) else 0 :=
    fun k => pauli1_trace_mul (s k) (t k)
  rw [Finset.prod_congr rfl fun k _ => hterm k]
  by_cases h : s = t
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-! ### Tracelessness of non-identity Pauli strings -/

theorem pauli1_zero : pauli1 0 = 1 := by rw [pauli1]; simp

/-- A non-identity single-qubit Pauli is traceless. -/
theorem pauli1_trace_zero {a : Fin 4} (h : a ≠ 0) : (pauli1 a).trace = 0 := by
  fin_cases a <;> simp_all [pauli1, pauliX, pauliY, pauliZ, Matrix.trace_fin_two]

/-- The all-identity Pauli string is the identity matrix. -/
theorem pauliStr_zero {n : ℕ} : pauliStr (0 : Fin n → Fin 4) = 1 := by
  ext i j
  simp only [pauliStr, Matrix.of_apply, Pi.zero_apply, pauli1_zero]
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [Matrix.one_apply, if_neg hk])

/-- A non-identity Pauli string is traceless: `Tr[P_s] = ∏ₖ Tr[σ_{sₖ}] = 0` whenever some
qubit carries a non-identity factor. -/
theorem pauliStr_trace_eq_zero {n : ℕ} {s : Fin n → Fin 4} (h : s ≠ 0) :
    (pauliStr s).trace = 0 := by
  have hrw : (pauliStr s).trace = (pauliStr s * pauliStr (0 : Fin n → Fin 4)).trace := by
    rw [pauliStr_zero, Matrix.mul_one]
  rw [hrw, pauliStr_trace_mul]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp h
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp only [Pi.zero_apply, pauli1_zero, Matrix.mul_one]
  exact pauli1_trace_zero hk

/-! ### Reindexing to the `Fin (2ⁿ)` matrix type used by `DLAHermBasis` -/

/-- The `n`-qubit Pauli string as a matrix over `Fin (2ⁿ)` (the index type the variance stack
uses), obtained by relabelling the register index `Fin n → Fin 2` along `finFunctionFinEquiv`. -/
noncomputable def pauliMat {n : ℕ} (s : Fin n → Fin 4) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (pauliStr s).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

/-- Relabelling by a bijection preserves the trace. -/
theorem trace_submatrix_ffe {n : ℕ} (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (M.submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finFunctionFinEquiv.symm (fun j => M j j)

theorem pauliMat_isHermitian {n : ℕ} (s : Fin n → Fin 4) : (pauliMat s)ᴴ = pauliMat s := by
  rw [pauliMat, Matrix.conjTranspose_submatrix, pauliStr_isHermitian]

theorem pauliMat_hsInner {n : ℕ} (s t : Fin n → Fin 4) :
    hsInner (pauliMat s) (pauliMat t) = if s = t then (2 ^ n : ℂ) else 0 := by
  rw [hsInner, pauliMat, pauliMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    trace_submatrix_ffe, ← hsInner, pauliStr_hsInner]

theorem pauliMat_trace_eq_zero {n : ℕ} {s : Fin n → Fin 4} (h : s ≠ 0) :
    (pauliMat s).trace = 0 := by
  rw [pauliMat, trace_submatrix_ffe, pauliStr_trace_eq_zero h]

/-! ### The `su(2ⁿ)` `DLAHermBasis` via the non-identity Pauli strings -/

/-- Normalization constant `(√(2ⁿ))⁻¹`, so that `rtNinv n • P_s` has unit Hilbert–Schmidt norm. -/
noncomputable def rtNinv (n : ℕ) : ℂ := ((Real.sqrt (2 ^ n))⁻¹ : ℝ)

theorem rtNinv_conj (n : ℕ) : star (rtNinv n) = rtNinv n := by
  rw [rtNinv, ← starRingEnd_apply]; exact Complex.conj_ofReal _

theorem rtNinv_mul_self (n : ℕ) : rtNinv n * rtNinv n = 1 / (2 ^ n : ℂ) := by
  rw [rtNinv, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity),
    Complex.ofReal_inv]
  push_cast
  ring

/-- The non-identity Pauli generators `{i·P_s : s ≠ 0}` of the `su(2ⁿ)` dynamical Lie algebra. -/
def suGens (n : ℕ) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4, s ≠ 0 ∧ A = Complex.I • pauliMat s}

theorem card_nz (n : ℕ) :
    Fintype.card {s : Fin n → Fin 4 // s ≠ 0} = 2 ^ n * 2 ^ n - 1 := by
  simp only [ne_eq]
  rw [Fintype.card_subtype_compl (p := fun s : Fin n → Fin 4 => s = 0),
    Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  congr 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]

/-- An enumeration of the `2ⁿ·2ⁿ − 1` non-identity Pauli labels. -/
noncomputable def nzEquiv (n : ℕ) : Fin (2 ^ n * 2 ^ n - 1) ≃ {s : Fin n → Fin 4 // s ≠ 0} :=
  (Fintype.equivFinOfCardEq (card_nz n)).symm

/-- The candidate Hermitian orthonormal basis of `su(2ⁿ)`: the normalized non-identity Pauli
strings. -/
noncomputable def suB (n : ℕ) (i : Fin (2 ^ n * 2 ^ n - 1)) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  rtNinv n • pauliMat (nzEquiv n i).1

theorem suB_isHermitian (n : ℕ) (i : Fin (2 ^ n * 2 ^ n - 1)) : (suB n i)ᴴ = suB n i := by
  rw [suB, conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]

theorem suB_ortho (n : ℕ) (i j : Fin (2 ^ n * 2 ^ n - 1)) :
    hsInner (suB n i) (suB n j) = if i = j then 1 else 0 := by
  rw [suB, suB, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply, rtNinv_conj, ← mul_assoc,
    rtNinv_mul_self, pauliMat_hsInner]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, one_div,
      inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg h, if_neg (fun he => h ((nzEquiv n).injective (Subtype.ext he))), mul_zero]

theorem suB_linearIndependent (n : ℕ) : LinearIndependent ℂ (suB n) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : hsInner (suB n i) (∑ j, c j • suB n j) = c i := by
    rw [hsInner_sum_right]
    have hterm : ∀ j, hsInner (suB n i) (c j • suB n j) = if i = j then c j else 0 := by
      intro j; rw [hsInner_smul_right, suB_ortho]; split <;> simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq]
    simp
  rw [hc] at h1
  simpa [hsInner] using h1.symm

theorem suB_span_finrank (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (suB n))) = 2 ^ n * 2 ^ n - 1 := by
  rw [finrank_span_eq_card (suB_linearIndependent n), Fintype.card_fin]

/-- The **traceless matrices** as a Lie subalgebra (commutators are always traceless). -/
noncomputable def tracelessLie (m : ℕ) : LieSubalgebra ℂ (Matrix (Fin m) (Fin m) ℂ) :=
  { LinearMap.ker (Matrix.traceLinearMap (Fin m) ℂ ℂ) with
    lie_mem' := fun {x y} _ _ =>
      show ⁅x, y⁆ ∈ LinearMap.ker (Matrix.traceLinearMap (Fin m) ℂ ℂ) by
        rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply, Ring.lie_def, Matrix.trace_sub,
          Matrix.trace_mul_comm, sub_self] }

theorem traceLinearMap_ker_finrank {m : ℕ} (hm : 0 < m) :
    Module.finrank ℂ (LinearMap.ker (Matrix.traceLinearMap (Fin m) ℂ ℂ)) = m * m - 1 := by
  have hsurj : Function.Surjective (Matrix.traceLinearMap (Fin m) ℂ ℂ) := by
    intro c
    refine ⟨(c / (m : ℂ)) • 1, ?_⟩
    rw [Matrix.traceLinearMap_apply, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul, div_mul_cancel₀]
    exact_mod_cast hm.ne'
  have hrange : Module.finrank ℂ (LinearMap.range (Matrix.traceLinearMap (Fin m) ℂ ℂ)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hrn := (Matrix.traceLinearMap (Fin m) ℂ ℂ).finrank_range_add_finrank_ker
  rw [hrange] at hrn
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrn
  omega

/-- **The genuine `su(2ⁿ)` as a `DLAHermBasis`.** The `2ⁿ·2ⁿ − 1` non-identity `n`-qubit Pauli
strings (normalized) form a Hermitian Hilbert–Schmidt orthonormal basis whose span is the
traceless subalgebra `su(2ⁿ)` — the dynamical Lie algebra generated by `{i·P_s : s ≠ 0}`. -/
noncomputable def suHermBasis (n : ℕ) : DLAHermBasis (suGens n) where
  dim := 2 ^ n * 2 ^ n - 1
  B := suB n
  herm := suB_isHermitian n
  ortho := suB_ortho n
  span_eq := by
    have ha : Submodule.span ℂ (Set.range (suB n)) ≤
        LinearMap.ker (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.traceLinearMap_apply, suB, Matrix.trace_smul,
        pauliMat_trace_eq_zero (nzEquiv n i).2, smul_zero]
    have hspan_eq_ker : Submodule.span ℂ (Set.range (suB n))
        = LinearMap.ker (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ) :=
      Submodule.eq_of_le_of_finrank_le ha
        (le_of_eq ((traceLinearMap_ker_finrank (by positivity)).trans (suB_span_finrank n).symm))
    have hf : Submodule.span ℂ (Set.range (suB n))
        ≤ (dynamicalLieAlgebra (suGens n)).toSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, suB]
      refine Submodule.smul_mem _ _ ?_
      have hgen : Complex.I • pauliMat (nzEquiv n i).1 ∈ dynamicalLieAlgebra (suGens n) :=
        LieSubalgebra.subset_lieSpan ⟨(nzEquiv n i).1, (nzEquiv n i).2, rfl⟩
      have hpm : pauliMat (nzEquiv n i).1
          = (-Complex.I) • (Complex.I • pauliMat (nzEquiv n i).1) := by
        rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      rw [hpm]
      exact Submodule.smul_mem _ _ hgen
    have hg : (dynamicalLieAlgebra (suGens n)).toSubmodule ≤
        LinearMap.ker (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ) := by
      have hsub : dynamicalLieAlgebra (suGens n) ≤ tracelessLie (2 ^ n) := by
        apply dynamicalLieAlgebra_minimal
        rintro _ ⟨s, hs, rfl⟩
        change Complex.I • pauliMat s ∈ LinearMap.ker (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ)
        rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_smul,
          pauliMat_trace_eq_zero hs, smul_zero]
      intro x hx
      exact hsub hx
    exact le_antisymm hf (hg.trans hspan_eq_ker.ge)

/-! ### Concrete `su(2ⁿ)` exponential barren plateau

The `su(2ⁿ)` basis exists for every `n`, so the abstract `SimpleSU` reduction and the exponential
barren plateau are witnessed **concretely** on the qubit family — the seminal `su(2ⁿ)`/2-design case
[MBS+18, maintext.tex:148].
We index by `n + 1` qubits so the dimension `2ⁿ⁺¹·2ⁿ⁺¹ − 1` is positive at every `n`. -/

theorem suHermBasis_dim_pos (n : ℕ) : 0 < (suHermBasis (n + 1)).dim := by
  change 0 < 2 ^ (n + 1) * 2 ^ (n + 1) - 1
  have h2 : 2 ≤ 2 ^ (n + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ 2 ^ (n + 1) * 2 ^ (n + 1) := by nlinarith [h2]
  omega

/-- The index of the first `su(2ⁿ⁺¹)` basis element. -/
def suI0 (n : ℕ) : Fin (suHermBasis (n + 1)).dim := ⟨0, suHermBasis_dim_pos n⟩

/-- The Ragone second-moment bundle for the `su(2ⁿ⁺¹)` qubit family, with state and observable the
first (normalized, Hermitian) basis element. -/
noncomputable def suSM (n : ℕ) :
    RagoneSecondMoment (suHermBasis (n + 1))
      ((suHermBasis (n + 1)).B (suI0 n)) ((suHermBasis (n + 1)).B (suI0 n)) :=
  RagoneSecondMoment.ofHermitian ((suHermBasis (n + 1)).herm (suI0 n))
    ((suHermBasis (n + 1)).herm (suI0 n)) (suHermBasis_dim_pos n)

/-- **The `su(2ⁿ)` reduction, witnessed.** For the genuine `su(2ⁿ⁺¹)` dynamical Lie algebra, the
loss variance equals `P_g(ρ)·P_g(O) / (2ⁿ⁺¹·2ⁿ⁺¹ − 1)` — the `SimpleSU.main` reduction on a concrete
`g ≃ su(d)` with `d = 2ⁿ⁺¹` [RBS+23, Arxiv_Final.tex:682]. -/
theorem suN_variance_eq (n : ℕ) :
    ((suSM n).variance : ℂ)
      = (suHermBasis (n + 1)).gPurity ((suHermBasis (n + 1)).B (suI0 n))
          * (suHermBasis (n + 1)).gPurity ((suHermBasis (n + 1)).B (suI0 n))
          / ((2 ^ (n + 1) * 2 ^ (n + 1) - 1 : ℕ) : ℂ) :=
  SimpleSU.main (suSM n) ((suHermBasis (n + 1)).herm (suI0 n))
    ((suHermBasis (n + 1)).herm (suI0 n)) (d := 2 ^ (n + 1)) rfl (suHermBasis_dim_pos n)

/-- With `ρ = O` a normalized basis element (`P_g = 1`), the variance is exactly
`1 / (2ⁿ⁺¹·2ⁿ⁺¹ − 1)`, vanishing exponentially in the qubit count. -/
theorem suN_variance_value (n : ℕ) :
    ((suSM n).variance : ℂ) = 1 / ((2 ^ (n + 1) * 2 ^ (n + 1) - 1 : ℕ) : ℂ) := by
  rw [suN_variance_eq, DLAHermBasis.gPurity_basis_elem, one_mul]

/-- **Concrete exponential barren plateau for `su(2ⁿ)`**
[MBS+18, maintext.tex:148]. The qubit-indexed family of circuits whose
dynamical Lie algebra is the full special-unitary algebra `su(2ⁿ⁺¹)`
(dimension `4ⁿ⁺¹ − 1`, realized by the non-identity Pauli strings) has an exponentially vanishing
loss variance — a genuine barren plateau. This instantiates `SimpleSU.main_barren_plateau` on a
concrete `su(2ⁿ)` family, so the exponential plateau is **not vacuous**. -/
theorem suN_hasBarrenPlateau : HasBarrenPlateau (fun n => (suSM n).variance) := by
  apply SimpleSU.main_barren_plateau (M := suSM)
    (hρ := fun n => (suHermBasis (n + 1)).herm (suI0 n))
    (hO := fun n => (suHermBasis (n + 1)).herm (suI0 n))
    (hdim := fun n => rfl) (C := 1) (hC := zero_le_one)
  intro n
  rw [DLAHermBasis.gPurity_basis_elem]
  norm_num

end QuantumAlg
