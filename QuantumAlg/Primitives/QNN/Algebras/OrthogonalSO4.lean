/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra
public import QuantumAlg.Primitives.QNN.Interface.RagoneInterface
public import QuantumAlg.Primitives.QNN.Interface.SchurGeneric
public import QuantumAlg.Primitives.QNN.Algebras.OrthogonalSchur

/-!
# The reductive Schur case `so(4) = su(2) ⊕ su(2)`

The orthogonal algebra `so(4)` is the `m = 2` orthogonal member — semisimple but **not** simple. It
splits as an orthogonal direct sum of two commuting `su(2)` ideals `so(4) = A ⊕ B`, so its doubled
invariant space `(g⊗g)^g` is genuinely **two**-dimensional and the single-Casimir Schur identity
`(g⊗g)^g = span{C}` is FALSE here (this is why the simple-member Schur identity `soHermBasis_schur`
requires `m ≥ 3`). Each ideal is a triangle of `2`-qubit odd-`#Y` Pauli strings whose three members
pairwise anticommute and are closed under the Pauli product:

* `A = {IY, YX, YZ}` — `IY = ![0,2]`, `YX = ![2,1]`, `YZ = ![2,3]`.
* `B = {XY, YI, ZY}` — `XY = ![1,2]`, `YI = ![2,0]`, `ZY = ![3,2]`.

The two ideals are Hilbert–Schmidt orthogonal (distinct strings) and mutually commuting.

We prove, for each ideal, a per-triangle Schur identity `(gⱼ⊗gⱼ)^gⱼ = span{Cⱼ}` via the generic
structure-constant solver (`SchurGeneric`), and assemble the reductive `so(4)` variance through the
two-Casimir `RagoneReductive` framework. The per-ideal Schur is genuine (each `su(2)` triangle is
simple), while the reductive bundle isolates the Schur-across-ideals diagonality as the named twirl
input. [RBS+23]
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### A generic `3`-element Pauli-triangle builder

The two `su(2)` ideals of `so(4)` are structurally identical: a triple of `m`-qubit Pauli strings
`t : Fin 3 → (Fin m → Fin 4)` that is injective, has no identity, is pairwise anticommuting, and is
closed under the Pauli product (`pauliXor` of two distinct members is the third). We build the whole
`DLAHermBasis` + Schur discharge once, then instantiate at `m = 2` for `A` and `B`. Every triangle
hypothesis is decidable for the concrete strings (`fin_cases <;> decide`). -/

/-- The remaining index of `Fin 3` distinct from both `i` and `j` (junk if `i = j`). -/
def thirdIdx (i j : Fin 3) : Fin 3 := 3 - i - j

theorem thirdIdx_ne_left {i j : Fin 3} (h : i ≠ j) : thirdIdx i j ≠ i := by
  revert h
  fin_cases i <;> fin_cases j <;> decide

theorem thirdIdx_ne_right {i j : Fin 3} (h : i ≠ j) : thirdIdx i j ≠ j := by
  revert h
  fin_cases i <;> fin_cases j <;> decide

/-- A `3`-element Pauli triangle: an injective, identity-free, pairwise-anticommuting,
product-closed triple of `m`-qubit Pauli labels. -/
structure PauliTriangle (m : ℕ) where
  /-- The three Pauli-string labels. -/
  t : Fin 3 → (Fin m → Fin 4)
  /-- The labels are distinct. -/
  inj : Function.Injective t
  /-- No label is the identity. -/
  ne_zero : ∀ i, t i ≠ 0
  /-- Distinct members pairwise anticommute. -/
  anticomm : ∀ i j, i ≠ j → pauliOmega (t i) (t j) = 1
  /-- The Pauli product of two distinct members is the third. -/
  xor_closed : ∀ i j, i ≠ j → pauliXor (t i) (t j) = t (thirdIdx i j)

namespace PauliTriangle

variable {m : ℕ} (T : PauliTriangle m)

/-- The normalized Hermitian triangle basis `Bᵢ = (1/√2ᵐ)·P_{tᵢ}`. -/
noncomputable def triB (i : Fin 3) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  rtNinv m • pauliMat (T.t i)

/-- The skew-Hermitian generators `{i·P_{tᵢ}}` of the triangle's dynamical Lie algebra. -/
def triGens : Set (Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :=
  {A | ∃ i : Fin 3, A = Complex.I • pauliMat (T.t i)}

theorem triB_isHermitian (i : Fin 3) : (T.triB i)ᴴ = T.triB i := by
  rw [triB, conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]

theorem triB_ortho (i j : Fin 3) : hsInner (T.triB i) (T.triB j) = if i = j then 1 else 0 := by
  rw [triB, triB, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply,
    rtNinv_conj, ← mul_assoc, rtNinv_mul_self, pauliMat_hsInner]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, one_div,
      inv_mul_cancel₀ (pow_ne_zero m (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg h, if_neg (fun he => h (T.inj he)), mul_zero]

/-! #### `span{triB} = triangle DLA` -/

/-- The three-element Pauli set of a triangle. -/
def triSet : Set (Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :=
  {pauliMat (T.t 0), pauliMat (T.t 1), pauliMat (T.t 2)}

theorem pauliMat_mem_triSet (i : Fin 3) : pauliMat (T.t i) ∈ T.triSet := by
  fin_cases i <;> simp [triSet]

/-- The bracket of two triangle Pauli matrices lands in the span of the triangle set. -/
theorem tri_lie_mem_span ⦃x y : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ⦄
    (hx : x ∈ Submodule.span ℂ T.triSet) (hy : y ∈ Submodule.span ℂ T.triSet) :
    ⁅x, y⁆ ∈ Submodule.span ℂ T.triSet := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      simp only [triSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      -- reduce to the nine brackets of the three generators
      have hmem : ∀ i : Fin 3, pauliMat (T.t i) ∈ Submodule.span ℂ T.triSet := fun i =>
        Submodule.subset_span (T.pauliMat_mem_triSet i)
      have key : ∀ i j : Fin 3,
          ⁅pauliMat (T.t i), pauliMat (T.t j)⁆ ∈ Submodule.span ℂ T.triSet := by
        intro i j
        by_cases hij : i = j
        · subst hij; rw [lie_self]; exact zero_mem _
        · rw [pauliMat_bracket_closed, T.xor_closed i j hij]
          exact Submodule.smul_mem _ _ (hmem _)
      -- dispatch the concrete `a`, `b`
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> exact key _ _
    | zero => rw [lie_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [lie_add]; exact add_mem hb hc
    | smul r b _ hb => rw [lie_smul]; exact Submodule.smul_mem _ _ hb
  | zero => rw [zero_lie]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_lie]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_lie]; exact Submodule.smul_mem _ _ ha

/-- `span ℂ (triSet)` as a Lie subalgebra of `gl(2ᵐ)`. -/
def triLie : LieSubalgebra ℂ (Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) where
  toSubmodule := Submodule.span ℂ T.triSet
  lie_mem' := fun hx hy => T.tri_lie_mem_span hx hy

theorem triGens_subset_triLie :
    T.triGens ⊆ (T.triLie : Set (Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)) := by
  rintro a ⟨i, rfl⟩
  change Complex.I • pauliMat (T.t i) ∈ Submodule.span ℂ T.triSet
  exact Submodule.smul_mem _ _ (Submodule.subset_span (T.pauliMat_mem_triSet i))

theorem tri_dla_toSubmodule :
    (dynamicalLieAlgebra T.triGens).toSubmodule = Submodule.span ℂ T.triSet := by
  apply le_antisymm
  · intro x hx
    exact dynamicalLieAlgebra_minimal T.triGens T.triGens_subset_triLie hx
  · rw [Submodule.span_le]
    intro a ha
    simp only [triSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    have hgen : T.triGens ⊆ (dynamicalLieAlgebra T.triGens : Set _) :=
      generators_subset_dynamicalLieAlgebra T.triGens
    have hkey : ∀ i : Fin 3, pauliMat (T.t i) ∈ dynamicalLieAlgebra T.triGens := by
      intro i
      have hg : Complex.I • pauliMat (T.t i) ∈ dynamicalLieAlgebra T.triGens := hgen ⟨i, rfl⟩
      have hpm : pauliMat (T.t i) = (-Complex.I) • (Complex.I • pauliMat (T.t i)) := by
        rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      rw [hpm]; exact Submodule.smul_mem _ _ hg
    rcases ha with rfl | rfl | rfl
    · exact hkey 0
    · exact hkey 1
    · exact hkey 2

theorem tri_range_span : Submodule.span ℂ (Set.range T.triB) = Submodule.span ℂ T.triSet := by
  have hrt : rtNinv m ≠ 0 := rtNinv_ne_zero m
  have key : ∀ P : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ, (rtNinv m)⁻¹ • (rtNinv m • P) = P :=
    fun P => by rw [smul_smul, inv_mul_cancel₀ hrt, one_smul]
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact Submodule.smul_mem _ _ (Submodule.subset_span (T.pauliMat_mem_triSet i))
  · rw [Submodule.span_le]
    intro a ha
    simp only [triSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    have hmem : ∀ i : Fin 3, T.triB i ∈ Submodule.span ℂ (Set.range T.triB) := fun i =>
      Submodule.subset_span ⟨i, rfl⟩
    have hpm : ∀ i : Fin 3, pauliMat (T.t i)
        = (rtNinv m)⁻¹ • T.triB i := fun i => by rw [triB, key]
    rcases ha with rfl | rfl | rfl
    · rw [hpm 0]; exact Submodule.smul_mem _ _ (hmem 0)
    · rw [hpm 1]; exact Submodule.smul_mem _ _ (hmem 1)
    · rw [hpm 2]; exact Submodule.smul_mem _ _ (hmem 2)

/-- **The triangle `su(2)` ideal as a `DLAHermBasis`** (dimension `3`). -/
noncomputable def basis : DLAHermBasis T.triGens where
  dim := 3
  B := T.triB
  herm := T.triB_isHermitian
  ortho := T.triB_ortho
  span_eq := by rw [T.tri_range_span, T.tri_dla_toSubmodule]

@[simp] theorem basis_dim : T.basis.dim = 3 := rfl

theorem basis_B (i : Fin 3) : T.basis.B i = T.triB i := rfl

theorem basis_dim_pos : 0 < T.basis.dim := by rw [basis_dim]; norm_num

/-! #### The triangle adjoint matrix in closed form -/

/-- **The triangle adjoint matrix in closed form.** `(Sₖ)_{a,i} = ⟪Bₐ, ⁅Bₖ, Bᵢ⁆⟫` is a single
symplectic term: nonzero only when `t a = t k ⊕ t i`, with the commutator phase coefficient. -/
theorem adMatrix_triB_apply (k a i : Fin 3) :
    adMatrix T.basis k a i
      = rtNinv m * rtNinv m * rtNinv m *
          (pauliPhase (T.t k) (T.t i) - pauliPhase (T.t i) (T.t k)) *
          (if T.t a = pauliXor (T.t k) (T.t i) then (2 ^ m : ℂ) else 0) := by
  rw [adMatrix, Matrix.of_apply]
  change hsInner (T.triB a) ⁅T.triB k, T.triB i⁆ = _
  rw [triB, triB, triB, smul_lie, lie_smul, pauliMat_bracket_closed, hsInner_smul_left,
    hsInner_smul_right, hsInner_smul_right, hsInner_smul_right, starRingEnd_apply, rtNinv_conj,
    pauliMat_hsInner]
  ring

theorem adMatrix_triB_eq_zero {k a i : Fin 3} (h : T.t a ≠ pauliXor (T.t k) (T.t i)) :
    adMatrix T.basis k a i = 0 := by
  rw [adMatrix_triB_apply, if_neg h, mul_zero]

theorem adMatrix_triB_ne_zero {k a i : Fin 3}
    (hsupp : T.t a = pauliXor (T.t k) (T.t i))
    (hanti : pauliOmega (T.t k) (T.t i) = 1) : adMatrix T.basis k a i ≠ 0 := by
  rw [adMatrix_triB_apply, if_pos hsupp]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · exact rtNinv_ne_zero m
  · exact rtNinv_ne_zero m
  · exact rtNinv_ne_zero m
  · exact pauliPhase_sub_ne_zero hanti
  · exact pow_ne_zero m (by norm_num)

theorem adMatrix_triB_eq_zero_of_comm {k a i : Fin 3}
    (h : pauliOmega (T.t k) (T.t i) = 0) : adMatrix T.basis k a i = 0 := by
  rw [adMatrix_triB_apply, pauliPhase_sub_eq_zero h, mul_zero, zero_mul]

/-! #### The square is diagonal, with a separating symplectic eigenvalue -/

/-- The `adMatrix²` eigenvalue for the triangle. -/
noncomputable def muTri (k a : Fin 3) : ℂ :=
  (adMatrix T.basis k * adMatrix T.basis k) a a

/-- **The square of the triangle adjoint matrix is diagonal.** -/
theorem adMatrix_triB_sq_diagonal (k : Fin 3) :
    adMatrix T.basis k * adMatrix T.basis k = Matrix.diagonal (T.muTri k) := by
  ext a a'
  by_cases ha : a = a'
  · subst ha; rw [Matrix.diagonal_apply_eq, muTri]
  · rw [show Matrix.diagonal (T.muTri k) a a' = 0 from Matrix.diagonal_apply_ne _ ha,
      Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : T.t a = pauliXor (T.t k) (T.t i)
    · have h2 : T.t i ≠ pauliXor (T.t k) (T.t a') := fun hi =>
        ha (T.inj (by rw [h1, hi, pauliXor_self_inv]))
      rw [adMatrix_triB_eq_zero T h2, mul_zero]
    · rw [adMatrix_triB_eq_zero T h1, zero_mul]

/-- **The triangle eigenvalue is zero iff the strings commute.** For the anchor `a = k`,
`μ k k = 0` (self-commute); for `a ≠ k`, `μ k a ≠ 0` (pairwise anticommute). -/
theorem muTri_eq_zero_iff (k a : Fin 3) :
    T.muTri k a = 0 ↔ pauliOmega (T.t k) (T.t a) = 0 := by
  constructor
  · intro h
    by_contra hω
    -- `pauliOmega (t k) (t a) ≠ 0` means `k ≠ a`, so `t a ⊕ t k = t (third)` and the term at that
    -- index is nonzero, contradicting `μ = 0`.
    have hka : k ≠ a := by
      rintro rfl; exact hω (by rw [pauliOmega_self_zero])
    have hω1 : pauliOmega (T.t k) (T.t a) = 1 := T.anticomm k a hka
    set i₀ := thirdIdx k a with hi₀def
    have hxor : pauliXor (T.t k) (T.t a) = T.t i₀ := T.xor_closed k a hka
    have hsupp : T.t a = pauliXor (T.t k) (T.t i₀) := by
      rw [← hxor, pauliXor_self_inv]
    have hanti : pauliOmega (T.t k) (T.t i₀) = 1 := by
      rw [← hxor, pauliOmega_xor_right, pauliOmega_self_zero, zero_add, hω1]
    have hσi₀ : T.t i₀ = pauliXor (T.t k) (T.t a) := hxor.symm
    have hμ : T.muTri k a = adMatrix T.basis k a i₀ * adMatrix T.basis k i₀ a := by
      rw [muTri, Matrix.mul_apply]
      refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun he => absurd (Finset.mem_univ i₀) he)
      by_cases h1 : T.t a = pauliXor (T.t k) (T.t i)
      · refine absurd (T.inj ?_) hi
        have hii : T.t i = pauliXor (T.t k) (T.t a) := by
          have hsi := pauliXor_self_inv (T.t k) (T.t i)
          rw [← h1] at hsi; exact hsi.symm
        exact hii.trans hσi₀.symm
      · rw [adMatrix_triB_eq_zero T h1, zero_mul]
    rw [hμ] at h
    rcases mul_eq_zero.mp h with hz | hz
    · exact adMatrix_triB_ne_zero T hsupp hanti hz
    · exact adMatrix_triB_ne_zero T hσi₀ hω1 hz
  · intro h
    rw [muTri, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : T.t a = pauliXor (T.t k) (T.t i)
    · have hi0 : T.t i = pauliXor (T.t k) (T.t a) := by
        have hsi := pauliXor_self_inv (T.t k) (T.t i)
        rw [← h1] at hsi; exact hsi.symm
      have hcomm : pauliOmega (T.t k) (T.t i) = 0 := by
        rw [hi0, pauliOmega_xor_right, pauliOmega_self_zero, zero_add, h]
      rw [adMatrix_triB_eq_zero_of_comm T hcomm, zero_mul]
    · rw [adMatrix_triB_eq_zero T h1, zero_mul]

/-! #### Separation and connectivity of the triangle -/

/-- **Separation.** For distinct triangle indices, `k = a` gives distinct eigenvalues:
`μ a a = 0` but `μ a a' ≠ 0` (a and a' anticommute). -/
theorem muTri_sep {a a' : Fin 3} (ha : a ≠ a') : ∃ k, T.muTri k a ≠ T.muTri k a' := by
  refine ⟨a, ?_⟩
  have hka : T.muTri a a = 0 := (T.muTri_eq_zero_iff a a).mpr (by rw [pauliOmega_self_zero])
  have hka' : T.muTri a a' ≠ 0 :=
    (T.muTri_eq_zero_iff a a').not.mpr (by rw [T.anticomm a a' ha]; exact one_ne_zero)
  rw [hka]; exact Ne.symm hka'

/-- **Connectivity.** The complete graph `K₃` on the triangle is connected, so any function constant
along adjoint edges is globally constant. For `x ≠ y`, the edge is witnessed at `k = thirdIdx x y`
(`t x = t k ⊕ t y` by closure, and `t k`, `t y` anticommute). -/
theorem triB_conn (f : Fin 3 → ℂ)
    (hf : ∀ x y : Fin 3, (∃ k, adMatrix T.basis k x y ≠ 0) → f x = f y)
    (x y : Fin 3) : f x = f y := by
  by_cases hxy : x = y
  · rw [hxy]
  · refine hf x y ⟨thirdIdx x y, ?_⟩
    set k := thirdIdx x y with hkdef
    have hyk : k ≠ y := thirdIdx_ne_right hxy
    have hxor : pauliXor (T.t x) (T.t y) = T.t k := T.xor_closed x y hxy
    have hsupp : T.t x = pauliXor (T.t k) (T.t y) := by
      rw [← hxor, pauliXor_xor_self_right]
    have hanti : pauliOmega (T.t k) (T.t y) = 1 := T.anticomm k y hyk
    exact adMatrix_triB_ne_zero T hsupp hanti

/-! #### The per-triangle Schur identity `(g⊗g)^g = span{C}` -/

/-- **The Schur identity `(g⊗g)^g = span{C}` for a single `su(2)` triangle ideal.** Each ideal of
`so(4)` is simple (`≅ su(2)`), so the hard inclusion `(g⊗g)^g ≤ span{C}` is genuinely
proved from the triangle's anticommutation (separation) and product-closure (connectivity) via
the generic structure-constant solver. -/
theorem basis_schur :
    gTensorGInvariant T.basis = Submodule.span ℂ {T.basis.casimir} := by
  refine le_antisymm (fun X hX => ?_) (spanC_le_gTensorGInvariant _)
  have hoff : ∀ a a' : Fin T.basis.dim, a ≠ a' → coeffMatrix T.basis X a a' = 0 :=
    fun a a' ha => coeffMatrix_offdiag_zero T.basis hX T.muTri
      T.adMatrix_triB_sq_diagonal (fun a a' h => T.muTri_sep h) ha
  exact gTensorGInvariant_le_spanC T.basis hX hoff
    (coeffMatrix_diag_const T.basis hX hoff T.triB_conn)

/-- **Cross-orthogonality of two disjoint triangles.** If every label of `T` differs from every
label of `T'`, their normalized Hermitian bases are Hilbert–Schmidt orthogonal. -/
theorem basis_cross_ortho {T' : PauliTriangle m} (hdis : ∀ i j, T.t i ≠ T'.t j)
    (a b : Fin 3) : hsInner (T.basis.B a) (T'.basis.B b) = 0 := by
  rw [basis_B, basis_B, triB, triB, hsInner_smul_left, hsInner_smul_right, pauliMat_hsInner,
    if_neg (hdis a b), mul_zero, mul_zero]

end PauliTriangle

/-! ### The two `su(2)` ideals of `so(4)` -/

/-- Ideal `A = {IY, YX, YZ}` of `so(4)`. -/
def so4A : PauliTriangle 2 where
  t := ![![0, 2], ![2, 1], ![2, 3]]
  inj := by decide
  ne_zero := by decide
  anticomm := by decide
  xor_closed := by decide

/-- Ideal `B = {XY, YI, ZY}` of `so(4)`. -/
def so4B : PauliTriangle 2 where
  t := ![![1, 2], ![2, 0], ![3, 2]]
  inj := by decide
  ne_zero := by decide
  anticomm := by decide
  xor_closed := by decide

/-- The two-ideal generator family `g = A ⊕ B` of `so(4)`. -/
def so4Gens : Fin 2 → Set (Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ) :=
  Fin.cons so4A.triGens (Fin.cons so4B.triGens Fin.elim0)

/-- The two-ideal Hermitian bases of `so(4)` (a dependent family). -/
noncomputable def so4Basis : (j : Fin 2) → DLAHermBasis (so4Gens j) :=
  Fin.cons (α := fun j => DLAHermBasis (so4Gens j)) so4A.basis
    (Fin.cons (α := fun j => DLAHermBasis (so4Gens j.succ)) so4B.basis (fun x => x.elim0))

@[simp] theorem so4Basis_zero : so4Basis 0 = so4A.basis := rfl

@[simp] theorem so4Basis_one : so4Basis 1 = so4B.basis := rfl

/-- Every `A`-label differs from every `B`-label. -/
theorem so4AB_disjoint (i j : Fin 3) : so4A.t i ≠ so4B.t j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Every `B`-label differs from every `A`-label. -/
theorem so4BA_disjoint (i j : Fin 3) : so4B.t i ≠ so4A.t j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The two ideals `A`, `B` are mutually Hilbert–Schmidt orthogonal (their strings are all
distinct). -/
theorem so4_cross_ortho : ∀ (i j : Fin 2), i ≠ j →
    ∀ (a : Fin (so4Basis i).dim) (b : Fin (so4Basis j).dim),
      hsInner ((so4Basis i).B a) ((so4Basis j).B b) = 0 := by
  intro i j hij a b
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact so4A.basis_cross_ortho so4AB_disjoint a b
  · exact so4B.basis_cross_ortho so4BA_disjoint a b
  · exact absurd rfl hij

/-! ### The reductive `so(4)` bundle and variance -/

/-- The index of the first `A`-basis element. -/
def so4Ai0 : Fin so4A.basis.dim := ⟨0, so4A.basis_dim_pos⟩

/-- The Hermitian witness operator for the `so(4)` reductive bundle: the first basis element of
ideal `A` (a normalized odd-`#Y` Pauli matrix, hence Hermitian), used for both slots. -/
noncomputable def so4Obs : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ := so4A.basis.B so4Ai0

theorem so4Obs_isHermitian : so4Obsᴴ = so4Obs := so4A.basis.herm so4Ai0

/-- **The reductive `so(4)` bundle** `g = A ⊕ B`. The two per-ideal Schur identities are genuinely
proved (`PauliTriangle.basis_schur`); the diagonal second moment discharges the per-ideal diagonal
memberships and the cross-ideal invariant-block exclusion non-circularly. Both Hermitian witness
operators are the first `A`-basis element. -/
noncomputable def so4Reductive : RagoneReductive so4Obs so4Obs :=
  RagoneReductive.consistencyWitness 2
    so4Gens
    so4Basis
    so4_cross_ortho
    so4Obs_isHermitian so4Obs_isHermitian
    (by intro j; fin_cases j
        · exact so4A.basis_dim_pos
        · exact so4B.basis_dim_pos)
    (by intro j; fin_cases j
        · exact so4A.basis_schur
        · exact so4B.basis_schur)

/-- **The reductive `so(4)` loss variance (closed form).** By `RagoneReductive.totalVariance_eq`,
the total variance is the sum over the two `su(2)` ideals of `P_{gⱼ}(ρ)·P_{gⱼ}(O)/3`. With
`ρ = O` the first `A`-basis element (`P_A = 1`, `P_B = 0` by cross-orthogonality), the sum collapses
to the single `A`-term `1·1/3 = 1/3`. [RBS+23] -/
theorem so4_totalVariance_eq : so4Reductive.variance = 1 / 3 := by
  have hpos : ∀ j, 0 < (so4Reductive.basis j).dim := by
    intro j; fin_cases j
    · exact so4A.basis_dim_pos
    · exact so4B.basis_dim_pos
  have key : (so4Reductive.variance : ℂ) = 1 / 3 := by
    rw [so4Reductive.totalVariance_eq so4Obs_isHermitian so4Obs_isHermitian hpos]
    change (∑ j : Fin 2, (so4Basis j).gPurity so4Obs
        * (so4Basis j).gPurity so4Obs / ((so4Basis j).dim : ℂ)) = 1 / 3
    have hterm : ∀ j : Fin 2, (so4Basis j).gPurity so4Obs
          * (so4Basis j).gPurity so4Obs / ((so4Basis j).dim : ℂ)
        = if j = 0 then 1 / 3 else 0 := by
      intro j
      fin_cases j
      · -- j = 0 (ideal A): O = B_A i0, purity 1, dim 3
        change (so4A.basis).gPurity so4Obs * (so4A.basis).gPurity so4Obs
            / ((so4A.basis).dim : ℂ) = if (0 : Fin 2) = 0 then (1 : ℂ) / 3 else 0
        rw [if_pos rfl, show so4Obs = so4A.basis.B so4Ai0 from rfl,
          DLAHermBasis.gPurity_basis_elem, PauliTriangle.basis_dim]
        norm_num
      · -- j = 1 (ideal B): O is A-basis element, orthogonal to B, purity 0
        change (so4B.basis).gPurity so4Obs * (so4B.basis).gPurity so4Obs
            / ((so4B.basis).dim : ℂ) = if (1 : Fin 2) = 0 then (1 : ℂ) / 3 else 0
        rw [if_neg (by decide)]
        have hpB : (so4B.basis).gPurity so4Obs = 0 := by
          rw [DLAHermBasis.gPurity]
          refine Finset.sum_eq_zero fun a _ => ?_
          have hz : hsInner (so4B.basis.B a) so4Obs = 0 := by
            rw [show so4Obs = so4A.basis.B so4Ai0 from rfl]
            exact so4B.basis_cross_ortho so4BA_disjoint a so4Ai0
          rw [hz]; simp
        rw [hpB, mul_zero, zero_div]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hcast : ((so4Reductive.variance : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ) := by
    rw [key]; push_cast; ring
  exact_mod_cast hcast

end QuantumAlg
