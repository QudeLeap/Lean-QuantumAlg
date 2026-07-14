/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.RagoneInterface
public import QuantumAlg.Primitives.QNN.Interface.SchurGeneric
public import QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra
public import QuantumAlg.Primitives.QNN.Algebras.PauliStringDLA
public import QuantumAlg.Primitives.QNN.Algebras.FullDLABasis

/-!
# Locality and the absence of barren plateaus: `g = su(2)^{⊕n}` with a local observable

For a circuit of *general single-qubit gates* on `ρ = |0⟩⟨0|^{⊗n}`, the dynamical Lie algebra is the
inexpressive (polynomial-dimensional, `dim g = 3n`) orthogonal direct sum `g = su(2)^{⊕n}` of the
per-qubit `su(2)`'s. A **local** observable `O = X₁` lands inside the algebra, so the reductive
Ragone sum collapses to a positive constant: `Var = 1/3`, independent of `n` — **no barren
plateau** [RBS+23, Arxiv_Final.tex:837-846]. This is the canonical "inexpressiveness alone is not
enough" counterpoint to the exponential traceless-`su(2ⁿ)` barren plateau
`suN_hasBarrenPlateau_schurDischarged`.

Everything is downstream of the proved reductive variance formula
`RagoneReductive.totalVariance_eq`.
The per-ideal Schur one-dimensionality (H2) is discharged by `su2EmbHermBasis_schur`, so
`rLocal` carries no deferred per-ideal Schur hypothesis. The bundle itself is the
`consistencyWitness` — an
explicit *satisfiability* instance with a hand-set diagonal second moment, **not** the physical
Haar/2-design twirl; that physical route is `RagoneSecondMoment.ofTwoDesign`, whose finite-2-design
(commutant-completeness) bridge remains a named, mechanism-level hypothesis (H1). The genuinely new
work here is the `su(2)^{⊕n}` Hermitian orthonormal basis (embedded single-qubit Paulis), the
per-ideal `su(2)` Schur discharge, and the per-ideal g-purity computations, all built on the
`pauliMat` machinery of `PauliStringDLA`.

The global observable `O = X^{⊗n}` (a separate `O(1/2ⁿ)` plateau attributed to a non-vendored
source) is out of scope: its DLA projection vanishes, so the formula yields the
degenerate `Var = 0`.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

variable {n : ℕ}

/-! ### Single-site Pauli labels and the Pauli-string product law -/

/-- The single-site Pauli label: the Pauli `a` on qubit `j`, identity on every other qubit. -/
def siteP (j : Fin n) (a : Fin 4) : Fin n → Fin 4 := Function.update 0 j a

@[simp] theorem siteP_same (j : Fin n) (a : Fin 4) : siteP j a j = a := by
  simp [siteP]

theorem siteP_ne {j l : Fin n} (a : Fin 4) (h : l ≠ j) : siteP j a l = 0 := by
  simp only [siteP, Function.update_of_ne h, Pi.zero_apply]

/-- **Entrywise Pauli-string product law**: the matrix product factorises over qubits,
`(P_s P_t)_{ik} = ∏ₗ (σ_{sₗ} σ_{tₗ})_{iₗ kₗ}`. -/
theorem pauliStr_mul_apply (s t : Fin n → Fin 4) (i k : Fin n → Fin 2) :
    (pauliStr s * pauliStr t) i k = ∏ l, (pauli1 (s l) * pauli1 (t l)) (i l) (k l) := by
  have hfac : ∀ l, (pauli1 (s l) * pauli1 (t l)) (i l) (k l)
      = ∑ ml : Fin 2, pauli1 (s l) (i l) ml * pauli1 (t l) ml (k l) := fun l => Matrix.mul_apply
  rw [Matrix.mul_apply, Finset.prod_congr rfl (fun l _ => hfac l),
    Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 2)))
      (fun (l : Fin n) (ml : Fin 2) => pauli1 (s l) (i l) ml * pauli1 (t l) ml (k l)),
    Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [pauliStr, Matrix.of_apply, ← Finset.prod_mul_distrib]

/-- If two single-qubit Paulis multiply to `ph · σ_c`, then the single-site Pauli strings
multiply to `ph · P_{siteP j c}` (the other legs are `I·I = I`). -/
theorem pauliStr_siteP_mul (j : Fin n) {a b c : Fin 4} {ph : ℂ}
    (h : pauli1 a * pauli1 b = ph • pauli1 c) :
    pauliStr (siteP j a) * pauliStr (siteP j b) = ph • pauliStr (siteP j c) := by
  ext i k
  rw [pauliStr_mul_apply, Matrix.smul_apply, pauliStr, Matrix.of_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase Finset.univ
        (fun l => (pauli1 (siteP j a l) * pauli1 (siteP j b l)) (i l) (k l)) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ
        (fun l => pauli1 (siteP j c l) (i l) (k l)) (Finset.mem_univ j)]
  have hj : (pauli1 (siteP j a j) * pauli1 (siteP j b j)) (i j) (k j)
      = ph * pauli1 (siteP j c j) (i j) (k j) := by
    rw [siteP_same, siteP_same, siteP_same, h, Matrix.smul_apply, smul_eq_mul]
  have herase : ∏ l ∈ Finset.univ.erase j,
        (pauli1 (siteP j a l) * pauli1 (siteP j b l)) (i l) (k l)
      = ∏ l ∈ Finset.univ.erase j, pauli1 (siteP j c l) (i l) (k l) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    rw [siteP_ne a hlj, siteP_ne b hlj, siteP_ne c hlj, pauli1_zero, Matrix.one_mul]
  rw [hj, herase, mul_assoc]

/-! ### The single-qubit Pauli products `σ_a σ_b = ±i σ_c` -/

theorem pauli1_mul_12 : pauli1 1 * pauli1 2 = Complex.I • pauli1 3 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauli1, pauliX, pauliY, pauliZ]

theorem pauli1_mul_21 : pauli1 2 * pauli1 1 = (-Complex.I) • pauli1 3 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauli1, pauliX, pauliY, pauliZ]

theorem pauli1_mul_23 : pauli1 2 * pauli1 3 = Complex.I • pauli1 1 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauli1, pauliX, pauliY, pauliZ]

theorem pauli1_mul_32 : pauli1 3 * pauli1 2 = (-Complex.I) • pauli1 1 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauli1, pauliX, pauliY, pauliZ]

theorem pauli1_mul_31 : pauli1 3 * pauli1 1 = Complex.I • pauli1 2 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauli1, pauliX, pauliY, pauliZ]

theorem pauli1_mul_13 : pauli1 1 * pauli1 3 = (-Complex.I) • pauli1 2 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauli1, pauliX, pauliY, pauliZ]

/-! ### The embedded `su(2)` brackets `⁅Pₐ, P_b⁆ = 2i P_c` on `Fin (2ⁿ)` -/

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lift a single-site Pauli-string product to the `Fin (2ⁿ)` matrices. -/
theorem pauliMat_siteP_mul (j : Fin n) {a b c : Fin 4} {ph : ℂ}
    (h : pauli1 a * pauli1 b = ph • pauli1 c) :
    pauliMat (siteP j a) * pauliMat (siteP j b) = ph • pauliMat (siteP j c) := by
  rw [pauliMat, pauliMat, pauliMat, Matrix.submatrix_mul_equiv, pauliStr_siteP_mul j h]
  ext p q
  simp [Matrix.submatrix_apply, Matrix.smul_apply]

theorem pauliMat_bracket_12 (j : Fin n) :
    ⁅pauliMat (siteP j 1), pauliMat (siteP j 2)⁆ = (2 * Complex.I) • pauliMat (siteP j 3) := by
  rw [Ring.lie_def, pauliMat_siteP_mul j pauli1_mul_12, pauliMat_siteP_mul j pauli1_mul_21,
    ← sub_smul, show Complex.I - -Complex.I = 2 * Complex.I from by ring]

theorem pauliMat_bracket_23 (j : Fin n) :
    ⁅pauliMat (siteP j 2), pauliMat (siteP j 3)⁆ = (2 * Complex.I) • pauliMat (siteP j 1) := by
  rw [Ring.lie_def, pauliMat_siteP_mul j pauli1_mul_23, pauliMat_siteP_mul j pauli1_mul_32,
    ← sub_smul, show Complex.I - -Complex.I = 2 * Complex.I from by ring]

theorem pauliMat_bracket_31 (j : Fin n) :
    ⁅pauliMat (siteP j 3), pauliMat (siteP j 1)⁆ = (2 * Complex.I) • pauliMat (siteP j 2) := by
  rw [Ring.lie_def, pauliMat_siteP_mul j pauli1_mul_31, pauliMat_siteP_mul j pauli1_mul_13,
    ← sub_smul, show Complex.I - -Complex.I = 2 * Complex.I from by ring]

/-! ### The qubit-`j` ideal `su(2)` as a `DLAHermBasis` -/

/-- The three Hermitian generators `{Xⱼ, Yⱼ, Zⱼ}` of the qubit-`j` ideal, embedded in `Fin (2ⁿ)`. -/
noncomputable def embSet (j : Fin n) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {pauliMat (siteP j 1), pauliMat (siteP j 2), pauliMat (siteP j 3)}

/-- The skew-Hermitian single-qubit-gate generators `{iXⱼ, iYⱼ, iZⱼ}` of the qubit-`j` ideal. -/
noncomputable def embGens (j : Fin n) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {Complex.I • pauliMat (siteP j 1), Complex.I • pauliMat (siteP j 2),
    Complex.I • pauliMat (siteP j 3)}

theorem pauliMat1_mem_embSet (j : Fin n) : pauliMat (siteP j 1) ∈ embSet j := by simp [embSet]
theorem pauliMat2_mem_embSet (j : Fin n) : pauliMat (siteP j 2) ∈ embSet j := by simp [embSet]
theorem pauliMat3_mem_embSet (j : Fin n) : pauliMat (siteP j 3) ∈ embSet j := by simp [embSet]

/-- The bracket of two qubit-`j` `su(2)` generators lands in `span {Xⱼ, Yⱼ, Zⱼ}`. -/
theorem emb_lie_mem_span (j : Fin n) ⦃x y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ⦄
    (hx : x ∈ Submodule.span ℂ (embSet j)) (hy : y ∈ Submodule.span ℂ (embSet j)) :
    ⁅x, y⁆ ∈ Submodule.span ℂ (embSet j) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      simp only [embSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      have h1 : pauliMat (siteP j 1) ∈ Submodule.span ℂ (embSet j) :=
        Submodule.subset_span (pauliMat1_mem_embSet j)
      have h2 : pauliMat (siteP j 2) ∈ Submodule.span ℂ (embSet j) :=
        Submodule.subset_span (pauliMat2_mem_embSet j)
      have h3 : pauliMat (siteP j 3) ∈ Submodule.span ℂ (embSet j) :=
        Submodule.subset_span (pauliMat3_mem_embSet j)
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | (rw [lie_self]; exact zero_mem _)
          | (rw [pauliMat_bracket_12]; exact Submodule.smul_mem _ _ h3)
          | (rw [pauliMat_bracket_23]; exact Submodule.smul_mem _ _ h1)
          | (rw [pauliMat_bracket_31]; exact Submodule.smul_mem _ _ h2)
          | (rw [← lie_skew, pauliMat_bracket_12]; exact neg_mem (Submodule.smul_mem _ _ h3))
          | (rw [← lie_skew, pauliMat_bracket_23]; exact neg_mem (Submodule.smul_mem _ _ h1))
          | (rw [← lie_skew, pauliMat_bracket_31]; exact neg_mem (Submodule.smul_mem _ _ h2))
    | zero => rw [lie_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [lie_add]; exact add_mem hb hc
    | smul r b _ hb => rw [lie_smul]; exact Submodule.smul_mem _ _ hb
  | zero => rw [zero_lie]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_lie]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_lie]; exact Submodule.smul_mem _ _ ha

/-- `span {Xⱼ, Yⱼ, Zⱼ}` as a Lie subalgebra — the embedded `su(2)` of the qubit-`j` ideal. -/
noncomputable def embLie (j : Fin n) : LieSubalgebra ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) where
  toSubmodule := Submodule.span ℂ (embSet j)
  lie_mem' := fun hx hy => emb_lie_mem_span j hx hy

theorem embGens_subset_embLie (j : Fin n) : embGens j ⊆ (embLie j : Set _) := by
  intro a ha
  simp only [embGens, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  have hmem : ∀ P ∈ embSet j, Complex.I • P ∈ embLie j := fun P hP =>
    Submodule.smul_mem _ Complex.I (Submodule.subset_span hP)
  rcases ha with rfl | rfl | rfl
  · exact hmem _ (pauliMat1_mem_embSet j)
  · exact hmem _ (pauliMat2_mem_embSet j)
  · exact hmem _ (pauliMat3_mem_embSet j)

/-- The dynamical Lie algebra of `{iXⱼ, iYⱼ, iZⱼ}` is, as a submodule, `span {Xⱼ, Yⱼ, Zⱼ}`. -/
theorem emb_dla_toSubmodule (j : Fin n) :
    (dynamicalLieAlgebra (embGens j)).toSubmodule = Submodule.span ℂ (embSet j) := by
  apply le_antisymm
  · intro x hx
    exact dynamicalLieAlgebra_minimal (embGens j) (embGens_subset_embLie j) hx
  · rw [Submodule.span_le]
    intro a ha
    simp only [embSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    have hgen : embGens j ⊆ (dynamicalLieAlgebra (embGens j) : Set _) :=
      generators_subset_dynamicalLieAlgebra (embGens j)
    have key : ∀ P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ, (-Complex.I) • (Complex.I • P) = P :=
      fun P => by rw [smul_smul]; simp [Complex.I_mul_I]
    rcases ha with rfl | rfl | rfl
    · have := Submodule.smul_mem _ (-Complex.I)
        (hgen (show Complex.I • pauliMat (siteP j 1) ∈ embGens j by simp [embGens]))
      rwa [key] at this
    · have := Submodule.smul_mem _ (-Complex.I)
        (hgen (show Complex.I • pauliMat (siteP j 2) ∈ embGens j by simp [embGens]))
      rwa [key] at this
    · have := Submodule.smul_mem _ (-Complex.I)
        (hgen (show Complex.I • pauliMat (siteP j 3) ∈ embGens j by simp [embGens]))
      rwa [key] at this

/-- The normalized Hermitian basis `{Xⱼ, Yⱼ, Zⱼ}/√(2ⁿ)` of the qubit-`j` ideal (`Pauli i.succ`). -/
noncomputable def embB (j : Fin n) (i : Fin 3) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  rtNinv n • pauliMat (siteP j i.succ)

theorem siteP_inj (j : Fin n) {x y : Fin 4} (h : siteP j x = siteP j y) : x = y := by
  have := congrFun h j; rwa [siteP_same, siteP_same] at this

theorem embB_isHermitian (j : Fin n) (i : Fin 3) : (embB j i)ᴴ = embB j i := by
  rw [embB, Matrix.conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]

theorem embB_ortho (j : Fin n) (i k : Fin 3) :
    hsInner (embB j i) (embB j k) = if i = k then 1 else 0 := by
  rw [embB, embB, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply, rtNinv_conj,
    ← mul_assoc, rtNinv_mul_self, pauliMat_hsInner]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, if_pos rfl, one_div, inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero))]
  · rw [if_neg hik, if_neg (fun h => hik (Fin.succ_injective 3 (siteP_inj j h))), mul_zero]

theorem emb_range_span (j : Fin n) :
    Submodule.span ℂ (Set.range (embB j)) = Submodule.span ℂ (embSet j) := by
  have hrt : rtNinv n ≠ 0 := by
    intro h; have hm := rtNinv_mul_self n; rw [h, mul_zero] at hm
    exact one_div_ne_zero (pow_ne_zero n (two_ne_zero)) hm.symm
  have key : ∀ P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ, (rtNinv n)⁻¹ • (rtNinv n • P) = P :=
    fun P => by rw [smul_smul, inv_mul_cancel₀ hrt, one_smul]
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    rw [embB]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    fin_cases i
    · exact pauliMat1_mem_embSet j
    · exact pauliMat2_mem_embSet j
    · exact pauliMat3_mem_embSet j
  · rw [Submodule.span_le]
    intro a ha
    simp only [embSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    have hmem : ∀ i : Fin 3, embB j i ∈ Submodule.span ℂ (Set.range (embB j)) := fun i =>
      Submodule.subset_span ⟨i, rfl⟩
    rcases ha with rfl | rfl | rfl
    · have h0 := Submodule.smul_mem (Submodule.span ℂ (Set.range (embB j))) (rtNinv n)⁻¹ (hmem 0)
      rwa [show embB j 0 = rtNinv n • pauliMat (siteP j 1) from rfl, key] at h0
    · have h1 := Submodule.smul_mem (Submodule.span ℂ (Set.range (embB j))) (rtNinv n)⁻¹ (hmem 1)
      rwa [show embB j 1 = rtNinv n • pauliMat (siteP j 2) from rfl, key] at h1
    · have h2 := Submodule.smul_mem (Submodule.span ℂ (Set.range (embB j))) (rtNinv n)⁻¹ (hmem 2)
      rwa [show embB j 2 = rtNinv n • pauliMat (siteP j 3) from rfl, key] at h2

/-- **The qubit-`j` ideal `su(2)` as a `DLAHermBasis`** (dimension `3`), embedded in `Fin (2ⁿ)`. -/
noncomputable def su2EmbHermBasis (j : Fin n) : DLAHermBasis (embGens j) where
  dim := 3
  B := embB j
  herm := embB_isHermitian j
  ortho := embB_ortho j
  span_eq := by rw [emb_range_span, emb_dla_toSubmodule]

@[simp] theorem su2EmbHermBasis_dim (j : Fin n) : (su2EmbHermBasis j).dim = 3 := rfl

@[simp] theorem su2EmbHermBasis_B (j : Fin n) : (su2EmbHermBasis j).B = embB j := rfl

theorem su2EmbHermBasis_dim_pos (j : Fin n) : 0 < (su2EmbHermBasis j).dim := by
  rw [su2EmbHermBasis_dim]; norm_num

theorem embB_zero (j : Fin n) : embB j 0 = rtNinv n • pauliMat (siteP j 1) := rfl

/-! ### Cross-ideal orthogonality of `g = su(2)^{⊕n}` -/

theorem siteP_ne_cross {i j : Fin n} (hij : i ≠ j) {x y : Fin 4} (hx : x ≠ 0) :
    siteP i x ≠ siteP j y := by
  intro hcontra
  have hval := congrFun hcontra i
  rw [siteP_same, siteP_ne y hij] at hval
  exact hx hval

theorem emb_cross_ortho {i j : Fin n} (hij : i ≠ j) (a b : Fin 3) :
    hsInner ((su2EmbHermBasis i).B a) ((su2EmbHermBasis j).B b) = 0 := by
  change hsInner (embB i a) (embB j b) = 0
  rw [embB, embB, hsInner_smul_left, hsInner_smul_right, pauliMat_hsInner,
    if_neg (siteP_ne_cross hij (Fin.succ_ne_zero a)), mul_zero, mul_zero]

/-- Pauli labels on distinct sites have zero symplectic pairing. -/
theorem pauliOmega_siteP_cross {i j : Fin n} (hij : i ≠ j) (a b : Fin 4) :
    pauliOmega (siteP i a) (siteP j b) = 0 := by
  rw [pauliOmega]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hki : k = i
  · subst hki
    rw [siteP_same, siteP_ne b hij, omega4_comm, omega4_zero_left]
  · rw [siteP_ne a hki, omega4_zero_left]

/-- Pauli matrices supported on distinct sites commute. -/
theorem pauliMat_siteP_cross_lie_zero {i j : Fin n} (hij : i ≠ j) (a b : Fin 4) :
    ⁅pauliMat (siteP i a), pauliMat (siteP j b)⁆ = 0 := by
  rw [pauliMat_bracket_closed, pauliPhase_sub_eq_zero (pauliOmega_siteP_cross hij a b),
    zero_smul]

/-- Embedded normalized single-site basis elements on distinct sites commute. -/
theorem embB_cross_lie_zero {i j : Fin n} (hij : i ≠ j) (a b : Fin 3) :
    ⁅embB i a, embB j b⁆ = 0 := by
  rw [embB, embB, smul_lie, lie_smul, pauliMat_siteP_cross_lie_zero hij,
    smul_zero]
  simp

/-- The bracket of two elements from site spans lands in the join of all site spans. -/
theorem emb_span_pair_lie_mem_iSup (i j : Fin n)
    {x y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hx : x ∈ Submodule.span ℂ (embSet i)) (hy : y ∈ Submodule.span ℂ (embSet j)) :
    ⁅x, y⁆ ∈ ⨆ k : Fin n, Submodule.span ℂ (embSet k) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
      induction hy using Submodule.span_induction with
      | mem b hb =>
          by_cases hij : i = j
          · subst j
            exact Submodule.mem_iSup_of_mem i
              (emb_lie_mem_span i (Submodule.subset_span ha) (Submodule.subset_span hb))
          · simp only [embSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
            rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
              rw [pauliMat_siteP_cross_lie_zero hij] <;> exact zero_mem _
      | zero =>
          rw [lie_zero]
          exact zero_mem _
      | add b c _ _ hb hc =>
          rw [lie_add]
          exact add_mem hb hc
      | smul r b _ hb =>
          rw [lie_smul]
          exact Submodule.smul_mem _ _ hb
  | zero =>
      rw [zero_lie]
      exact zero_mem _
  | add a b _ _ ha hb =>
      rw [add_lie]
      exact add_mem ha hb
  | smul r a _ ha =>
      rw [smul_lie]
      exact Submodule.smul_mem _ _ ha

/-- The joined single-site spans are closed under the matrix commutator. -/
theorem emb_iSup_lie_mem {x y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hx : x ∈ ⨆ j : Fin n, Submodule.span ℂ (embSet j))
    (hy : y ∈ ⨆ j : Fin n, Submodule.span ℂ (embSet j)) :
    ⁅x, y⁆ ∈ ⨆ j : Fin n, Submodule.span ℂ (embSet j) := by
  refine Submodule.iSup_induction
    (fun j : Fin n => Submodule.span ℂ (embSet j))
    (motive := fun x' => ⁅x', y⁆ ∈ ⨆ j : Fin n, Submodule.span ℂ (embSet j))
    hx ?mem_x ?zero_x ?add_x
  · intro i x hx
    refine Submodule.iSup_induction
      (fun j : Fin n => Submodule.span ℂ (embSet j))
      (motive := fun y' => ⁅x, y'⁆ ∈ ⨆ j : Fin n, Submodule.span ℂ (embSet j))
      hy ?mem_y ?zero_y ?add_y
    · intro j y hy
      exact emb_span_pair_lie_mem_iSup i j hx hy
    · rw [lie_zero]
      exact zero_mem _
    · intro y z hy hz
      rw [lie_add]
      exact add_mem hy hz
  · rw [zero_lie]
    exact zero_mem _
  · intro x z hx hz
    rw [add_lie]
    exact add_mem hx hz

/-- The joined single-site spans as a Lie subalgebra. -/
noncomputable def embUnionLie (n : Nat) :
    LieSubalgebra ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) where
  toSubmodule := ⨆ j : Fin n, Submodule.span ℂ (embSet j)
  lie_mem' := fun hx hy => emb_iSup_lie_mem hx hy

/-- The DLA generated by the union of the site generators is exactly the join of the site spans. -/
theorem emb_iSup_span_eq_iUnion_dla (n : Nat) :
    (⨆ j : Fin n, Submodule.span ℂ (embSet j)) =
      (dynamicalLieAlgebra (⋃ j : Fin n, embGens j)).toSubmodule := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    rw [← emb_dla_toSubmodule j]
    intro x hx
    exact (LieSubalgebra.lieSpan_mono (Set.subset_iUnion (fun j : Fin n => embGens j) j)) hx
  · intro x hx
    exact dynamicalLieAlgebra_minimal (⋃ j : Fin n, embGens j) (K := embUnionLie n)
      (by
        intro A hA
        rw [Set.mem_iUnion] at hA
        obtain ⟨j, hA⟩ := hA
        exact Submodule.mem_iSup_of_mem j (embGens_subset_embLie j hA)) hx

/-! ### Embedded `su(2)` structure constants and the per-ideal Schur one-dimensionality (H2) -/

/-- Cyclic structure constant of the embedded normalized `su(2)` basis on qubit `j`:
`⁅Bₖ, Bᵢ⁆ = (2i/√(2ⁿ)) • Bₗ` for the positive cyclic `(k, i, l)`. The scalar
`f = 2 i · rtNinv n` is carried opaque (only `f ≠ 0` matters downstream). -/
theorem embB_lie_01 (j : Fin n) :
    ⁅embB j 0, embB j 1⁆ = (2 * Complex.I * rtNinv n) • embB j 2 := by
  change ⁅rtNinv n • pauliMat (siteP j 1), rtNinv n • pauliMat (siteP j 2)⁆
    = (2 * Complex.I * rtNinv n) • (rtNinv n • pauliMat (siteP j 3))
  rw [smul_lie, lie_smul, pauliMat_bracket_12, smul_smul, smul_smul, smul_smul]
  congr 1; ring

theorem embB_lie_12 (j : Fin n) :
    ⁅embB j 1, embB j 2⁆ = (2 * Complex.I * rtNinv n) • embB j 0 := by
  change ⁅rtNinv n • pauliMat (siteP j 2), rtNinv n • pauliMat (siteP j 3)⁆
    = (2 * Complex.I * rtNinv n) • (rtNinv n • pauliMat (siteP j 1))
  rw [smul_lie, lie_smul, pauliMat_bracket_23, smul_smul, smul_smul, smul_smul]
  congr 1; ring

theorem embB_lie_20 (j : Fin n) :
    ⁅embB j 2, embB j 0⁆ = (2 * Complex.I * rtNinv n) • embB j 1 := by
  change ⁅rtNinv n • pauliMat (siteP j 3), rtNinv n • pauliMat (siteP j 1)⁆
    = (2 * Complex.I * rtNinv n) • (rtNinv n • pauliMat (siteP j 2))
  rw [smul_lie, lie_smul, pauliMat_bracket_31, smul_smul, smul_smul, smul_smul]
  congr 1; ring

/-- Anti-cyclic embedded brackets, by skew-symmetry. -/
theorem embB_lie_10 (j : Fin n) :
    ⁅embB j 1, embB j 0⁆ = (-(2 * Complex.I * rtNinv n)) • embB j 2 := by
  rw [neg_smul, ← embB_lie_01]; exact (lie_skew (embB j 1) (embB j 0)).symm

theorem embB_lie_21 (j : Fin n) :
    ⁅embB j 2, embB j 1⁆ = (-(2 * Complex.I * rtNinv n)) • embB j 0 := by
  rw [neg_smul, ← embB_lie_12]; exact (lie_skew (embB j 2) (embB j 1)).symm

theorem embB_lie_02 (j : Fin n) :
    ⁅embB j 0, embB j 2⁆ = (-(2 * Complex.I * rtNinv n)) • embB j 1 := by
  rw [neg_smul, ← embB_lie_20]; exact (lie_skew (embB j 0) (embB j 2)).symm

/-- The embedded `su(2)` structure constant is nonzero. -/
theorem emb_f_ne_zero : (2 * Complex.I * rtNinv n) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (rtNinv_ne_zero n)

/-- **Per-ideal Schur one-dimensionality `(gⱼ⊗gⱼ)^{gⱼ} = span{Cⱼ}` for the embedded qubit-`j`
`su(2)` (discharge of H2).** Mirrors `su2HermBasis_schur`: the doubled-action invariance equations
(`doubledAd_pairing`) force the `3×3` coefficient matrix `cᵢₗ = ⟪Bᵢ⊗ₖBₗ, X⟫` to be a scalar `λ·I`,
whence `X = λ·Cⱼ`. No abstract Schur lemma is used. -/
theorem su2EmbHermBasis_schur (j : Fin n) :
    gTensorGInvariant (su2EmbHermBasis j)
      = Submodule.span ℂ {(su2EmbHermBasis j).casimir} := by
  refine le_antisymm ?_ (spanC_le_gTensorGInvariant (su2EmbHermBasis j))
  intro X hX
  rw [gTensorGInvariant, Submodule.mem_inf] at hX
  obtain ⟨hAd, hgT⟩ := hX
  have hdAd : ∀ k : Fin 3, doubledAd ((su2EmbHermBasis j).B k) X = 0 := by
    intro k
    rw [adCommutantGG, Submodule.mem_iInf] at hAd
    exact LinearMap.mem_ker.mp (hAd k)
  have heq : ∀ k a b : Fin 3,
      (∑ i, hsInner (embB j a) ⁅embB j k, embB j i⁆ * hsInner (embB j i ⊗ₖ embB j b) X)
      + ∑ l, hsInner (embB j b) ⁅embB j k, embB j l⁆ * hsInner (embB j a ⊗ₖ embB j l) X = 0 := by
    intro k a b
    have hp := doubledAd_pairing (su2EmbHermBasis j) hgT k a b
    rw [hdAd k, hsInner_zero_right] at hp
    exact hp.symm
  -- the 6 off-diagonal coefficients vanish
  have hc21 : hsInner (embB j 2 ⊗ₖ embB j 1) X = 0 := by
    have h := heq 2 2 0
    simp only [Fin.sum_univ_three, embB_lie_20 j, embB_lie_21 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left emb_f_ne_zero
  have hc12 : hsInner (embB j 1 ⊗ₖ embB j 2) X = 0 := by
    have h := heq 2 0 2
    simp only [Fin.sum_univ_three, embB_lie_20 j, embB_lie_21 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left emb_f_ne_zero
  have hc02 : hsInner (embB j 0 ⊗ₖ embB j 2) X = 0 := by
    have h := heq 0 0 1
    simp only [Fin.sum_univ_three, embB_lie_01 j, embB_lie_02 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left emb_f_ne_zero
  have hc20 : hsInner (embB j 2 ⊗ₖ embB j 0) X = 0 := by
    have h := heq 0 1 0
    simp only [Fin.sum_univ_three, embB_lie_01 j, embB_lie_02 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left emb_f_ne_zero
  have hc10 : hsInner (embB j 1 ⊗ₖ embB j 0) X = 0 := by
    have h := heq 1 1 2
    simp only [Fin.sum_univ_three, embB_lie_12 j, embB_lie_10 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left emb_f_ne_zero
  have hc01 : hsInner (embB j 0 ⊗ₖ embB j 1) X = 0 := by
    have h := heq 1 2 1
    simp only [Fin.sum_univ_three, embB_lie_12 j, embB_lie_10 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, neg_mul] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left emb_f_ne_zero
  -- the diagonal coefficients are all equal
  have hc0011 : hsInner (embB j 0 ⊗ₖ embB j 0) X = hsInner (embB j 1 ⊗ₖ embB j 1) X := by
    have h := heq 2 0 1
    simp only [Fin.sum_univ_three, embB_lie_20 j, embB_lie_21 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul] at h
    exact mul_left_cancel₀ emb_f_ne_zero (by linear_combination h)
  have hc1122 : hsInner (embB j 1 ⊗ₖ embB j 1) X = hsInner (embB j 2 ⊗ₖ embB j 2) X := by
    have h := heq 0 1 2
    simp only [Fin.sum_univ_three, embB_lie_01 j, embB_lie_02 j, lie_self,
      hsInner_smul_right, hsInner_zero_right, embB_ortho j, Fin.reduceEq, if_true, if_false,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul] at h
    exact mul_left_cancel₀ emb_f_ne_zero (by linear_combination h)
  -- assemble X = c₀₀ • Cⱼ
  rw [Submodule.mem_span_singleton]
  refine ⟨hsInner (embB j 0 ⊗ₖ embB j 0) X, ?_⟩
  have hcoord : X = ∑ i : Fin 3, ∑ l : Fin 3,
      hsInner (embB j i ⊗ₖ embB j l) X • (embB j i ⊗ₖ embB j l) :=
    gTensorG_coord (su2EmbHermBasis j) hgT
  rw [show (su2EmbHermBasis j).casimir = ∑ i : Fin 3, embB j i ⊗ₖ embB j i from rfl,
    Finset.smul_sum]
  conv_rhs => rw [hcoord]
  -- expand both `Fin 3` sums into literal `0/1/2` terms (no `fin_cases`, so no `Fin.mk` artifacts)
  simp only [Fin.sum_univ_three, hc01, hc02, hc10, hc12, hc20, hc21, zero_smul, add_zero, zero_add]
  -- the surviving diagonal coefficients are all equal to `c₀₀`
  rw [← hc1122, ← hc0011]

/-! ### The local observable `O = X₀` and the state `ρ = |0⟩⟨0|^{⊗n}` -/

/-- The local observable `O = X₀` (Pauli `X` on qubit `0`). -/
noncomputable def localObs (hn : 0 < n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  pauliMat (siteP ⟨0, hn⟩ 1)

theorem localObs_herm (hn : 0 < n) : (localObs hn)ᴴ = localObs hn := pauliMat_isHermitian _

/-- The initial state `ρ = |0⟩⟨0|^{⊗n}`, the all-zeros computational-basis projector (the `(0,0)`
matrix unit, written through the register reindexing to match `pauliMat`). -/
noncomputable def localState : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (Matrix.single (0 : Fin n → Fin 2) 0 1).submatrix
    finFunctionFinEquiv.symm finFunctionFinEquiv.symm

theorem localState_herm : (localState (n := n))ᴴ = localState := by
  unfold localState
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_single, star_one]

/-! ### Per-ideal `g`-purities for the local case -/

theorem hrtNormSq (n : ℕ) : (Complex.normSq (rtNinv n) : ℂ) = (2 ^ n : ℂ)⁻¹ := by
  rw [← Complex.mul_conj, starRingEnd_apply, rtNinv_conj, rtNinv_mul_self, one_div]

theorem hrtNormSqInv (n : ℕ) : (Complex.normSq ((rtNinv n)⁻¹) : ℂ) = (2 ^ n : ℂ) := by
  rw [Complex.normSq_inv, Complex.ofReal_inv, hrtNormSq, inv_inv]

/-- `g`-purity of the `g`-purity of a scalar multiple: `P_g(c·H) = |c|² P_g(H)`. -/
theorem gPurity_smul {N : ℕ} {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (c : ℂ) (H : Matrix (Fin N) (Fin N) ℂ) :
    b.gPurity (c • H) = (Complex.normSq c : ℂ) * b.gPurity H := by
  simp only [DLAHermBasis.gPurity]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsInner_smul_right, Complex.normSq_mul, Complex.ofReal_mul]

/-- `⟪M, |0⟩⟨0|⟫ = conj(M₀₀)` (over the register index). -/
theorem hsInner_single_one {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    hsInner M (Matrix.single i j 1) = (starRingEnd ℂ) (M i j) := by
  rw [hsInner, Matrix.trace_mul_comm, Matrix.trace_single_mul, one_smul, Matrix.conjTranspose_apply,
    starRingEnd_apply]

/-- The reindexing preserves the Hilbert–Schmidt inner product. -/
theorem hsInner_submatrix_ffe (A B : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    hsInner (A.submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm)
        (B.submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm) = hsInner A B := by
  rw [hsInner, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, trace_submatrix_ffe,
    ← hsInner]

theorem hsInner_pauliMat_localState (σ : Fin n → Fin 4) :
    hsInner (pauliMat σ) localState = (starRingEnd ℂ) (∏ l, pauli1 (σ l) 0 0) := by
  rw [pauliMat, localState, hsInner_submatrix_ffe, hsInner_single_one, pauliStr, Matrix.of_apply]
  simp only [Pi.zero_apply]

theorem prod_pauli1_siteP_00 (j : Fin n) (a : Fin 4) :
    (∏ l, pauli1 (siteP j a l) 0 0) = pauli1 a 0 0 := by
  rw [← Finset.mul_prod_erase Finset.univ (fun l => pauli1 (siteP j a l) 0 0) (Finset.mem_univ j),
    siteP_same]
  rw [Finset.prod_eq_one fun l hl => ?_, mul_one]
  rw [siteP_ne a (Finset.ne_of_mem_erase hl), pauli1_zero, Matrix.one_apply_eq]

theorem pauli1_succ_00 (a : Fin 3) : pauli1 a.succ 0 0 = if a = 2 then (1 : ℂ) else 0 := by
  fin_cases a <;> simp [pauli1, pauliX, pauliY, pauliZ]

/-- The `g`-purity over a qubit-`j` `su(2)` ideal, expanded as an explicit 3-term sum. -/
theorem gPurity_su2Emb (j : Fin n) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    (su2EmbHermBasis j).gPurity H
      = (Complex.normSq (hsInner (embB j 0) H) : ℂ)
        + (Complex.normSq (hsInner (embB j 1) H) : ℂ)
        + (Complex.normSq (hsInner (embB j 2) H) : ℂ) := by
  rw [show (su2EmbHermBasis j).gPurity H
      = ∑ i : Fin 3, (Complex.normSq (hsInner (embB j i) H) : ℂ) from rfl, Fin.sum_univ_three]

/-- `P_{g₀}(X₀) = 2ⁿ` (the distinguished ideal carries the local observable). -/
theorem gPurity_localObs_diag (hn : 0 < n) :
    (su2EmbHermBasis (⟨0, hn⟩ : Fin n)).gPurity (localObs hn) = (2 ^ n : ℂ) := by
  have hO : localObs hn = (rtNinv n)⁻¹ • embB (⟨0, hn⟩ : Fin n) 0 := by
    rw [embB_zero, localObs, smul_smul, inv_mul_cancel₀ (rtNinv_ne_zero n), one_smul]
  rw [hO, gPurity_smul, ← su2EmbHermBasis_B, DLAHermBasis.gPurity_basis_elem, mul_one,
    hrtNormSqInv]

/-- `P_{gⱼ}(X₀) = 0` for `j ≠ 0` (the local observable is orthogonal to the other ideals). -/
theorem gPurity_localObs_offdiag (hn : 0 < n) (j : Fin n) (hj : j ≠ ⟨0, hn⟩) :
    (su2EmbHermBasis j).gPurity (localObs hn) = 0 := by
  have h0 : ∀ a : Fin 3, hsInner (embB j a) (localObs hn) = 0 := fun a => by
    rw [embB, localObs, hsInner_smul_left, pauliMat_hsInner,
      if_neg (siteP_ne_cross hj (Fin.succ_ne_zero a)), mul_zero]
  rw [gPurity_su2Emb, h0 0, h0 1, h0 2]
  simp

/-- `P_{gⱼ}(ρ) = 2⁻ⁿ` for every ideal `j` (only the `Zⱼ` component of `ρ` survives). -/
theorem gPurity_localState (j : Fin n) :
    (su2EmbHermBasis j).gPurity localState = (2 ^ n : ℂ)⁻¹ := by
  have hterm : ∀ a : Fin 3,
      (Complex.normSq (hsInner (embB j a) localState) : ℂ)
        = if a = 2 then (2 ^ n : ℂ)⁻¹ else 0 := by
    intro a
    have he : hsInner (embB j a) localState = rtNinv n * (if a = 2 then 1 else 0) := by
      rw [embB, hsInner_smul_left, hsInner_pauliMat_localState, prod_pauli1_siteP_00,
        pauli1_succ_00, starRingEnd_apply, rtNinv_conj, apply_ite (starRingEnd ℂ), map_one,
        map_zero]
    rw [he, Complex.normSq_mul, Complex.ofReal_mul, hrtNormSq]
    split_ifs with h <;> simp [Complex.normSq_one, Complex.normSq_zero]
  rw [gPurity_su2Emb, hterm 0, hterm 1, hterm 2]
  simp

/-! ### The reductive bundle and the `Var = 1/3` headline -/

/-- The reductive bundle for the single-qubit-gate family `g = su(2)^{⊕n}` with `O = X₀`. The
per-ideal Schur hypotheses (H2) are discharged by `su2EmbHermBasis_schur`. This is the generic
`RagoneReductive.consistencyWitness`: a satisfiable reductive bundle with a diagonal hand-set second
moment, separate from the product-Clifford physical twirl used by `GSimLocal`. -/
noncomputable def rLocal (hn : 0 < n) :
    RagoneReductive (localState (n := n)) (localObs hn) :=
  RagoneReductive.consistencyWitness n embGens su2EmbHermBasis
    (fun _ _ hij a b => emb_cross_ortho hij a b)
    localState_herm (localObs_herm hn) su2EmbHermBasis_dim_pos su2EmbHermBasis_schur

/-- **Locality `⟹` no barren plateau (closed form).** The loss variance of the single-qubit-gate
family with the *local* observable `O = X₀` is exactly `1/3`, independent of the qubit count `n`
[RBS+23, Arxiv_Final.tex:838-840], derived from `RagoneReductive.totalVariance_eq`: the per-ideal
sum collapses to the single `j = 0` term `P_{g₀}(ρ)·P_{g₀}(O)/3 = (2⁻ⁿ·2ⁿ)/3 = 1/3`. -/
theorem localObs_totalVariance_eq (hn : 0 < n) :
    (rLocal hn).variance = 1 / 3 := by
  have key : ((rLocal hn).variance : ℂ) = 1 / 3 := by
    rw [(rLocal hn).totalVariance_eq localState_herm (localObs_herm hn)
      su2EmbHermBasis_dim_pos]
    change (∑ j : Fin n, (su2EmbHermBasis j).gPurity localState
        * (su2EmbHermBasis j).gPurity (localObs hn) / ((su2EmbHermBasis j).dim : ℂ)) = 1 / 3
    have hterm : ∀ j : Fin n, (su2EmbHermBasis j).gPurity localState
          * (su2EmbHermBasis j).gPurity (localObs hn) / ((su2EmbHermBasis j).dim : ℂ)
        = if j = ⟨0, hn⟩ then 1 / 3 else 0 := by
      intro j
      by_cases hj : j = ⟨0, hn⟩
      · subst hj
        rw [gPurity_localState, gPurity_localObs_diag, if_pos rfl, su2EmbHermBasis_dim,
          inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero))]
        norm_num
      · rw [gPurity_localObs_offdiag hn j hj, mul_zero, zero_div, if_neg hj]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hcast : ((rLocal hn).variance : ℂ) = ((1 / 3 : ℝ) : ℂ) := by
    rw [key]; push_cast; ring
  exact_mod_cast hcast

/-- **Locality `⟹` no barren plateau.** Since the loss variance is the positive constant `1/3` for
every qubit count (here indexed so that `m` corresponds to `m+1` qubits), it does not concentrate
exponentially: the single-qubit-gate family with a local observable has **no** barren plateau
[RBS+23, Arxiv_Final.tex:837]. -/
theorem localObs_not_hasBarrenPlateau :
    ¬ HasBarrenPlateau
        (fun m => (rLocal (n := m + 1) (Nat.succ_pos m)).variance) := by
  rintro ⟨base, hbase, C, hC, hbound⟩
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (3 * C) hbase
  have hb := hbound m
  simp only [] at hb
  rw [localObs_totalVariance_eq (Nat.succ_pos m), sub_zero,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at hb
  have hbpos : 0 < base ^ m := pow_pos (lt_trans one_pos hbase) m
  rw [le_div_iff₀ hbpos] at hb
  nlinarith [hm, hb]

end QuantumAlg
