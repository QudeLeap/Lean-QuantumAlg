/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.TransferInstance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.UnitaryGroup
public import QuantumAlg.Util.LinearIsometry

/-!
# Matrix trace norm

This file provides the trace-norm surface needed by the qDRIFT
formalization: zero, homogeneity, unitary invariance, the Hermitian
eigenvalue formula, polar-decomposition duality, and the triangle inequality.
The induced trace norm for quantum superoperators is defined in Analysis.
-/

@[expose] public section

namespace Matrix

noncomputable section

open scoped ComplexOrder MatrixOrder

variable {m n k R : Type*}
variable [RCLike R]

/-- An isometry matrix has orthonormal columns, `Uᴴ * U = 1`. -/
def Isometry [Fintype m] [DecidableEq n] (U : Matrix m n R) : Prop :=
  Uᴴ * U = 1

/-- The trace norm of a matrix, `Tr sqrt(Aᴴ A)`. -/
def traceNorm [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n R) : ℝ :=
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace

/-- The singular values of a square matrix, indexed like the matrix columns.

They are the square roots of the eigenvalues of `Aᴴ * A`. No ordering is
imposed by this definition. -/
def singularValues [Fintype n] [DecidableEq n] (A : Matrix n n R) : n → ℝ :=
  fun i => Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- Singular values are nonnegative. -/
lemma singularValues_nonneg [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i : n) :
    0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

@[simp]
lemma traceNorm_zero [Fintype m] [Fintype n] [DecidableEq n] :
    traceNorm (0 : Matrix m n R) = 0 := by
  simp [traceNorm]

/-- The trace norm is unchanged by negation. -/
@[simp]
lemma traceNorm_neg [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n R) :
    traceNorm (-A) = traceNorm A := by
  simp [traceNorm]

lemma traceNorm_eq_neg_self [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n R) :
    traceNorm (-A) = traceNorm A :=
  traceNorm_neg A

/-- The trace norm is nonnegative. -/
lemma traceNorm_nonneg [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n R) :
    0 ≤ A.traceNorm := by
  unfold traceNorm
  exact And.left <| RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg

/-- The trace norm vanishes exactly on the zero matrix. -/
lemma traceNorm_zero_iff [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) :
    A.traceNorm = 0 ↔ A = 0 := by
  constructor
  · intro h
    let B : Matrix n n R := CFC.sqrt (Aᴴ * A)
    have hB_nonneg : 0 ≤ B := by
      exact CFC.sqrt_nonneg (Aᴴ * A)
    have hB_pos : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hB_nonneg
    have hB_trace : B.trace = 0 := by
      have hreal : RCLike.re B.trace = 0 := by
        simpa [B, traceNorm] using h
      have hstar : star B.trace = B.trace := by
        rw [← Matrix.trace_conjTranspose, hB_pos.1]
      have hself : IsSelfAdjoint B.trace := by
        rwa [isSelfAdjoint_iff]
      simpa using (RCLike.re_eq_ofReal_of_isSelfAdjoint hself).mp hreal
    have hB_zero : B = 0 := hB_pos.trace_eq_zero_iff.mp hB_trace
    have hAA_zero : Aᴴ * A = 0 := by
      simpa [B, hB_zero] using
        (CFC.nnrpow_sqrt_two (Aᴴ * A)
          (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A))).symm
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hAA_zero
  · rintro rfl
    simp

/-- The trace norm is homogeneous under scalar multiplication. -/
lemma traceNorm_smul [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) (c : R) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by
  have h :
      (c • A)ᴴ * (c • A) = (‖c‖ ^ 2 : R) • (Aᴴ * A) := by
    ext i j
    simp only [conjTranspose_apply, smul_apply, smul_eq_mul, Matrix.mul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    calc
      star (c * (A x i)) * (c * (A x j))
          = ((starRingEnd R) c * c) * (star (A x i) * A x j) := by
        rw [star_mul, RCLike.star_def]
        ring_nf
      _ = (‖c‖ ^ 2 : R) * (star (A x i) * A x j) := by
        rw [RCLike.star_def, RCLike.conj_mul]
      _ = ↑‖c‖ ^ 2 * (star (A x i) * A x j) := by
        rfl
  rw [traceNorm, h]
  have hre :
      RCLike.re (trace (‖c‖ • CFC.sqrt (Aᴴ * A))) = ‖c‖ * traceNorm A := by
    simp [RCLike.smul_re, traceNorm]
  convert hre using 3
  rw [RCLike.real_smul_eq_coe_smul (K := R) ‖c‖]
  by_cases hc : c = 0
  · subst c
    simp
  · set M := Aᴴ * A
    have hM : M.PosSemidef := by
      exact posSemidef_conjTranspose_mul_self A
    rw [sq]
    rw [← smul_smul]
    apply CFC.sqrt_unique
    · simp only [algebraMap_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      rw [CFC.sqrt_mul_sqrt_self M hM.nonneg]
    · exact le_trans (by norm_num)
        (smul_le_smul_of_nonneg_left (CFC.sqrt_nonneg M)
          (by exact_mod_cast norm_nonneg c))

/-- Square unitary matrices are isometries. -/
lemma isometry_of_mem_unitaryGroup [Fintype n] [DecidableEq n] {U : Matrix n n R}
    (hU : U ∈ unitaryGroup n R) : Isometry U := by
  simpa [Isometry, star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hU)

/-- The trace norm is invariant under left multiplication by an isometry. -/
lemma traceNorm_isometry_left [Fintype m] [Fintype n] [Fintype k] [DecidableEq m]
    [DecidableEq n] {A : Matrix n m R} {U : Matrix k n R}
    (hU : Isometry U) : traceNorm (U * A) = traceNorm A := by
  have harg : (U * A)ᴴ * (U * A) = Aᴴ * A := by
    rw [conjTranspose_mul]
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U A]
    rw [hU]
    simp
  unfold traceNorm
  rw [harg]

/-- The trace norm is invariant under left multiplication by a square unitary. -/
lemma traceNorm_unitary_left [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix n m R} {U : Matrix n n R}
    (hU : U ∈ unitaryGroup n R) : traceNorm (U * A) = traceNorm A :=
  traceNorm_isometry_left (isometry_of_mem_unitaryGroup hU)

open scoped Classical in
/-- Functional-calculus square roots commute with isometry conjugation. -/
lemma cfc_sqrt_isometry_conj [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix n n R} (hA : 0 ≤ A) {U : Matrix m n R} (hU : Isometry U) :
    CFC.sqrt (U * A * Uᴴ) = U * CFC.sqrt A * Uᴴ := by
  classical
  have h_conj (B : Matrix n n R) (hB : 0 ≤ B) : 0 ≤ U * B * Uᴴ := by
    rw [Matrix.nonneg_iff_posSemidef] at hB ⊢
    exact hB.mul_mul_conjTranspose_same U
  have hUA := h_conj A hA
  have hUsqrt := h_conj (CFC.sqrt A) (CFC.sqrt_nonneg A)
  apply (CFC.sqrt_eq_iff _ _ hUA hUsqrt).mpr
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, ← Matrix.mul_assoc Uᴴ]
  rw [show Uᴴ * U = 1 from hU]
  simp only [one_mul]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc U, CFC.sqrt_mul_sqrt_self A hA]

/-- The trace norm is invariant under right multiplication by an isometry adjoint. -/
lemma traceNorm_isometry_right [Fintype m] [Fintype n] [Fintype k] [DecidableEq m]
    [DecidableEq k] {A : Matrix n m R} {U : Matrix k m R}
    (hU : Isometry U) : traceNorm (A * Uᴴ) = traceNorm A := by
  classical
  unfold traceNorm
  congr 1
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  have hA := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  calc
    (CFC.sqrt (U * Aᴴ * (A * Uᴴ))).trace
        = (CFC.sqrt (U * (Aᴴ * A) * Uᴴ)).trace := by
      congr 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ A Uᴴ]
      rw [← Matrix.mul_assoc U (Aᴴ * A) Uᴴ]
    _ = (U * CFC.sqrt (Aᴴ * A) * Uᴴ).trace := by
      rw [cfc_sqrt_isometry_conj hA hU]
    _ = (CFC.sqrt (Aᴴ * A)).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
      simp [show Uᴴ * U = 1 from hU]

/-- The trace norm is invariant under left and right isometries. -/
lemma traceNorm_isometry_conj [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix n n R} {U V : Matrix m n R}
    (hU : Isometry U) (hV : Isometry V) :
    traceNorm (U * A * Vᴴ) = traceNorm A := by
  rw [traceNorm_isometry_right hV, traceNorm_isometry_left hU]

/-- Square unitary conjugation preserves the trace norm. -/
lemma traceNorm_unitary_conj [Fintype n] [DecidableEq n]
    {A : Matrix n n R} {U : Matrix.unitaryGroup n R} :
    traceNorm (U.val * A * U.valᴴ) = traceNorm A := by
  have hU : Isometry U.val := isometry_of_mem_unitaryGroup U.2
  exact traceNorm_isometry_conj hU hU

/-- For Hermitian matrices, the trace norm is the sum of absolute eigenvalues. -/
lemma traceNorm_Hermitian_eq_sum_abs_eigenvalues [Fintype n] [DecidableEq n]
    {A : Matrix n n R} (hA : A.IsHermitian) :
    A.traceNorm = ∑ i, |hA.eigenvalues i| := by
  obtain ⟨U, D, hD, hA_eq, h_eig⟩ :
      ∃ U : Matrix.unitaryGroup n R, ∃ D : Matrix n n R,
        D.IsDiag ∧ A = U.val * D * U.valᴴ ∧
          ∀ i, D i i = hA.eigenvalues i := by
    refine ⟨hA.eigenvectorUnitary, Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues),
      isDiag_diagonal _, ?_, ?_⟩
    · simpa [Matrix.mul_assoc, star_eq_conjTranspose] using hA.spectral_theorem
    simp [Matrix.diagonal, Function.comp_apply]
  nth_rw 1 [hA_eq]
  rw [traceNorm_unitary_conj]
  unfold traceNorm
  rw [← Matrix.IsDiag.diagonal_diag hD]
  simp only [diagonal_conjTranspose, diagonal_mul_diagonal, Pi.star_apply, diag_apply,
    RCLike.star_def, RCLike.conj_ofReal, h_eig]
  set B : Matrix n n R :=
    Matrix.diagonal fun i => (hA.eigenvalues i : R) * (hA.eigenvalues i : R)
  change RCLike.re (CFC.sqrt B).trace = ∑ i, |hA.eigenvalues i|
  have hsqrt :
      CFC.sqrt B = Matrix.diagonal fun i => ((|hA.eigenvalues i| : ℝ) : R) := by
    apply CFC.sqrt_unique
    · rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq]
        rw [show B i i = (hA.eigenvalues i : R) * (hA.eigenvalues i : R) by
          simp [B, Matrix.diagonal_apply_eq]]
        have hsq :
            (|hA.eigenvalues i| : ℝ) * |hA.eigenvalues i| =
              hA.eigenvalues i * hA.eigenvalues i := by
          simp
        rw [← map_mul, ← map_mul]
        exact congrArg (fun x : ℝ => (x : R)) hsq
      · simp [B, Matrix.diagonal, hij]
    · apply Matrix.PosSemidef.nonneg
      rw [Matrix.posSemidef_diagonal_iff]
      exact_mod_cast fun i => abs_nonneg (hA.eigenvalues i)
  rw [hsqrt, Matrix.trace_diagonal]
  simp

/-- A positive semidefinite matrix has trace norm equal to the real part of its trace. -/
lemma PosSemidef.traceNorm_eq_re_trace [Fintype n] [DecidableEq n]
    {A : Matrix n n R} (hA : A.PosSemidef) :
    A.traceNorm = RCLike.re A.trace := by
  rw [traceNorm_Hermitian_eq_sum_abs_eigenvalues hA.1]
  calc
    (∑ i, |hA.1.eigenvalues i|)
        = ∑ i, hA.1.eigenvalues i := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_of_nonneg (hA.eigenvalues_nonneg i)
    _ = RCLike.re A.trace := by
      rw [hA.1.trace_eq_sum_eigenvalues]
      simp

/-- A unitary multiplier cannot make the real part of the trace of a positive
semidefinite matrix larger than its trace. -/
lemma PosSemidef.re_trace_unitary_mul_le_trace [Fintype n] [DecidableEq n]
    {P : Matrix n n R} (hP : P.PosSemidef) (U : Matrix.unitaryGroup n R) :
    RCLike.re (((U : Matrix n n R) * P).trace) ≤ RCLike.re P.trace := by
  let V : Matrix.unitaryGroup n R := hP.1.eigenvectorUnitary
  let D : Matrix n n R := Matrix.diagonal (RCLike.ofReal ∘ hP.1.eigenvalues)
  let W : Matrix.unitaryGroup n R := V⁻¹ * U * V
  have hP_spectral : P = (V : Matrix n n R) * D * (V : Matrix n n R)ᴴ := by
    simpa [V, D, Matrix.mul_assoc, Matrix.star_eq_conjTranspose] using hP.1.spectral_theorem
  have htrace :
      RCLike.re (((U : Matrix n n R) * P).trace) =
        ∑ i, hP.1.eigenvalues i * RCLike.re ((W : Matrix n n R) i i) := by
    have hUP :
        (U : Matrix n n R) * P =
          (U : Matrix n n R) * ((V : Matrix n n R) * D * (V : Matrix n n R)ᴴ) := by
      rw [hP_spectral]
    rw [hUP]
    have hcycle :
        ((U : Matrix n n R) * ((V : Matrix n n R) * D * (V : Matrix n n R)ᴴ)).trace =
          (((W : Matrix n n R) * D).trace) := by
      rw [Matrix.trace_mul_cycle'
        (A := (U : Matrix n n R)) (B := (V : Matrix n n R) * D)
        (C := (V : Matrix n n R)ᴴ)]
      simp [W, V, D, Matrix.mul_assoc, Matrix.UnitaryGroup.inv_val,
        Matrix.star_eq_conjTranspose]
    rw [hcycle]
    simp [D, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, mul_comm]
  calc
    RCLike.re (((U : Matrix n n R) * P).trace)
        = ∑ i, hP.1.eigenvalues i * RCLike.re ((W : Matrix n n R) i i) := htrace
    _ ≤ ∑ i, hP.1.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i _
      have hentry_norm : ‖(W : Matrix n n R) i i‖ ≤ 1 :=
        entry_norm_bound_of_unitary W.2 i i
      have hentry_re : RCLike.re ((W : Matrix n n R) i i) ≤ 1 :=
        (RCLike.re_le_norm ((W : Matrix n n R) i i)).trans hentry_norm
      have heig_nonneg : 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg i
      calc
        hP.1.eigenvalues i * RCLike.re ((W : Matrix n n R) i i)
            ≤ hP.1.eigenvalues i * 1 :=
          mul_le_mul_of_nonneg_left hentry_re heig_nonneg
        _ = hP.1.eigenvalues i := by ring
    _ = RCLike.re P.trace := by
      rw [hP.1.trace_eq_sum_eigenvalues]
      simp

open scoped Classical in
/-- The square root `sqrt(Aᴴ * A)` and `A` have the same kernel as linear maps. -/
lemma ker_mulVecLin_cfc_sqrt_conjTranspose_mul_self [Fintype n]
    (A : Matrix n n R) :
    LinearMap.ker (CFC.sqrt (Aᴴ * A)).mulVecLin =
      LinearMap.ker A.mulVecLin := by
  let P : Matrix n n R := CFC.sqrt (Aᴴ * A)
  have hP_pos : P.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have hP_sq : Pᴴ * P = Aᴴ * A := by
    rw [hP_pos.1]
    exact CFC.sqrt_mul_sqrt_self (Aᴴ * A)
      (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A))
  calc
    LinearMap.ker P.mulVecLin = LinearMap.ker (Pᴴ * P).mulVecLin := by
      rw [Matrix.ker_mulVecLin_conjTranspose_mul_self P]
    _ = LinearMap.ker (Aᴴ * A).mulVecLin := by rw [hP_sq]
    _ = LinearMap.ker A.mulVecLin :=
      Matrix.ker_mulVecLin_conjTranspose_mul_self A

/-- The first-isomorphism-law identification between the ranges of
`sqrt(Aᴴ * A)` and `A`.

This is the linear skeleton of the polar-decomposition partial isometry:
it is the map induced by `sqrt(Aᴴ * A) x ↦ A x`. -/
noncomputable def polarRangeLinearEquiv [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    LinearMap.range (CFC.sqrt (Aᴴ * A)).mulVecLin ≃ₗ[R]
      LinearMap.range A.mulVecLin :=
  let P : Matrix n n R := CFC.sqrt (Aᴴ * A)
  P.mulVecLin.quotKerEquivRange.symm.trans <|
    (Submodule.quotEquivOfEq (LinearMap.ker P.mulVecLin) (LinearMap.ker A.mulVecLin)
      (ker_mulVecLin_cfc_sqrt_conjTranspose_mul_self A)).trans
      A.mulVecLin.quotKerEquivRange

@[simp]
lemma polarRangeLinearEquiv_apply_image [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (x : n → R) :
    ((polarRangeLinearEquiv A)
      ⟨(CFC.sqrt (Aᴴ * A)).mulVec x, ⟨x, rfl⟩⟩ : n → R) = A.mulVec x := by
  let P : Matrix n n R := CFC.sqrt (Aᴴ * A)
  change
    ↑(A.mulVecLin.quotKerEquivRange
        ((Submodule.quotEquivOfEq (LinearMap.ker P.mulVecLin) (LinearMap.ker A.mulVecLin)
          (ker_mulVecLin_cfc_sqrt_conjTranspose_mul_self A))
            (P.mulVecLin.quotKerEquivRange.symm ⟨P.mulVec x, ⟨x, rfl⟩⟩))) =
      A.mulVec x
  have hquot :
      P.mulVecLin.quotKerEquivRange.symm ⟨P.mulVec x, ⟨x, rfl⟩⟩ =
        (LinearMap.ker P.mulVecLin).mkQ x :=
    LinearMap.quotKerEquivRange_symm_apply_image P.mulVecLin x ⟨x, rfl⟩
  rw [hquot]
  simp

open scoped Classical in
/-- The positive square root `sqrt(Aᴴ * A)` preserves the vector quadratic form
needed for the polar-decomposition partial isometry on its range. -/
lemma dotProduct_mulVec_cfc_sqrt_conjTranspose_mul_self [Fintype n]
    (A : Matrix n n R) (x : n → R) :
    star ((CFC.sqrt (Aᴴ * A)).mulVec x) ⬝ᵥ ((CFC.sqrt (Aᴴ * A)).mulVec x) =
      star (A.mulVec x) ⬝ᵥ A.mulVec x := by
  let P : Matrix n n R := CFC.sqrt (Aᴴ * A)
  have hP_pos : P.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have hP_sq : Pᴴ * P = Aᴴ * A := by
    rw [hP_pos.1]
    exact CFC.sqrt_mul_sqrt_self (Aᴴ * A)
      (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A))
  change star (P.mulVec x) ⬝ᵥ P.mulVec x = star (A.mulVec x) ⬝ᵥ A.mulVec x
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  rw [hP_sq]

open scoped Classical in
/-- The positive square root `sqrt(Aᴴ * A)` and `A` have the same pointwise
L2 action norm on Euclidean space. -/
lemma norm_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self [Fintype n]
    (A : Matrix n n R) (x : EuclideanSpace R n) :
    ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A)) x‖ =
      ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_eq_re_inner (𝕜 := R), norm_sq_eq_re_inner (𝕜 := R)]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toEuclideanCLM]
  simpa [dotProduct, mul_comm] using congrArg RCLike.re
    (dotProduct_mulVec_cfc_sqrt_conjTranspose_mul_self A x.ofLp)

open scoped Classical in
/-- The Euclidean-space operators induced by `sqrt(Aᴴ * A)` and `A` have the
same kernel. -/
lemma ker_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self [Fintype n]
    (A : Matrix n n R) :
    LinearMap.ker
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap =
      LinearMap.ker ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply norm_eq_zero.mp
    have hzero :
        ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A)) x‖ = 0 := by
      simpa using congrArg norm hx
    exact (norm_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self A x).symm.trans hzero
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply norm_eq_zero.mp
    have hzero : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A x‖ = 0 := by
      simpa using congrArg norm hx
    exact (norm_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self A x).trans hzero

open scoped Classical in
/-- The Euclidean-space version of `polarRangeLinearEquiv`, using the
continuous-linear-map model of matrices. -/
noncomputable def polarEuclideanRangeLinearEquiv [Fintype n] (A : Matrix n n R) :
    LinearMap.range
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap ≃ₗ[R]
      LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap :=
  let TP := ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap
  let TA := ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap
  TP.quotKerEquivRange.symm.trans <|
    (Submodule.quotEquivOfEq (LinearMap.ker TP) (LinearMap.ker TA)
      (ker_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self A)).trans
      TA.quotKerEquivRange

open scoped Classical in
@[simp]
lemma polarEuclideanRangeLinearEquiv_apply_image [Fintype n]
    (A : Matrix n n R) (x : EuclideanSpace R n) :
    ((polarEuclideanRangeLinearEquiv A)
      ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A)) x, ⟨x, rfl⟩⟩ :
        EuclideanSpace R n) =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A x := by
  let TP := ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap
  let TA := ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap
  change
    ↑(TA.quotKerEquivRange
        ((Submodule.quotEquivOfEq (LinearMap.ker TP) (LinearMap.ker TA)
          (ker_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self A))
            (TP.quotKerEquivRange.symm ⟨TP x, ⟨x, rfl⟩⟩))) =
      TA x
  have hquot :
      TP.quotKerEquivRange.symm ⟨TP x, ⟨x, rfl⟩⟩ =
        (LinearMap.ker TP).mkQ x :=
    LinearMap.quotKerEquivRange_symm_apply_image TP x ⟨x, rfl⟩
  rw [hquot]
  simp

open scoped Classical in
/-- The polar range map is an isometry on Euclidean-space ranges. -/
noncomputable def polarEuclideanRangeLinearIsometryEquiv [Fintype n]
    (A : Matrix n n R) :
    LinearMap.range
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap ≃ₗᵢ[R]
      LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap :=
  { polarEuclideanRangeLinearEquiv A with
    norm_map' := by
      rintro ⟨_, x, rfl⟩
      simp [norm_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self] }

open scoped Classical in
/-- The source and target ranges of the polar range isometry have equal
finite dimension. -/
lemma finrank_range_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self [Fintype n]
    (A : Matrix n n R) :
    Module.finrank R
        (LinearMap.range
          ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap) =
      Module.finrank R
        (LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap) :=
  (polarEuclideanRangeLinearIsometryEquiv A).toLinearEquiv.finrank_eq

open scoped Classical in
/-- The orthogonal complements of the two polar ranges have equal finite
dimension, so the polar range isometry can be extended by any isometry between
the complements. -/
lemma finrank_orthogonal_range_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self [Fintype n]
    (A : Matrix n n R) :
    Module.finrank R
        (LinearMap.range
          ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap)ᗮ =
      Module.finrank R
        (LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap)ᗮ := by
  let KP : Submodule R (EuclideanSpace R n) :=
    LinearMap.range
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap
  let KA : Submodule R (EuclideanSpace R n) :=
    LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap
  have hsumP : Module.finrank R KP + Module.finrank R KPᗮ =
      Module.finrank R (EuclideanSpace R n) :=
    Submodule.finrank_add_finrank_orthogonal KP
  have hsumA : Module.finrank R KA + Module.finrank R KAᗮ =
      Module.finrank R (EuclideanSpace R n) :=
    Submodule.finrank_add_finrank_orthogonal KA
  have hrange : Module.finrank R KP = Module.finrank R KA := by
    simpa [KP, KA] using
      finrank_range_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self A
  change Module.finrank R KPᗮ = Module.finrank R KAᗮ
  apply Nat.add_left_cancel (n := Module.finrank R KA)
  calc
    Module.finrank R KA + Module.finrank R KPᗮ
        = Module.finrank R KP + Module.finrank R KPᗮ := by rw [hrange]
    _ = Module.finrank R (EuclideanSpace R n) := hsumP
    _ = Module.finrank R KA + Module.finrank R KAᗮ := hsumA.symm

open scoped Classical in
/-- An arbitrary isometry between the orthogonal complements of the two polar
ranges. This is the complement piece needed to extend the polar range isometry
to a full-space unitary/isometry. -/
noncomputable def polarEuclideanOrthogonalRangeLinearIsometryEquiv [Fintype n]
    (A : Matrix n n R) :
    (LinearMap.range
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap)ᗮ
        ≃ₗᵢ[R]
      (LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap)ᗮ :=
  LinearIsometryEquiv.ofFinrankEq
    (finrank_orthogonal_range_toEuclideanCLM_cfc_sqrt_conjTranspose_mul_self A)

open scoped Classical in
/-- The L2-product isometry combining the polar range isometry and an arbitrary
isometry between the orthogonal complements. -/
noncomputable def polarEuclideanProductLinearIsometryEquiv [Fintype n]
    (A : Matrix n n R) :
    WithLp 2
        (LinearMap.range
            ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap ×
          (LinearMap.range
            ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap)ᗮ)
        ≃ₗᵢ[R]
      WithLp 2
        (LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap ×
          (LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap)ᗮ) :=
  LinearIsometryEquiv.withLpProdCongr
    (p := 2)
    (polarEuclideanRangeLinearIsometryEquiv A)
    (polarEuclideanOrthogonalRangeLinearIsometryEquiv A)

open scoped Classical in
/-- A full-space Euclidean isometry extending the polar range isometry.

On the range of `sqrt(Aᴴ * A)` this sends `sqrt(Aᴴ * A) x` to `A x`;
on the orthogonal complement it uses an arbitrary finite-dimensional isometry. -/
noncomputable def polarEuclideanFullLinearIsometryEquiv [Fintype n]
    (A : Matrix n n R) :
    EuclideanSpace R n ≃ₗᵢ[R] EuclideanSpace R n :=
  let KP : Submodule R (EuclideanSpace R n) :=
    LinearMap.range
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap
  let KA : Submodule R (EuclideanSpace R n) :=
    LinearMap.range ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A).toLinearMap
  let eRange : KP ≃ₗᵢ[R] KA := polarEuclideanRangeLinearIsometryEquiv A
  let eOrth : KPᗮ ≃ₗᵢ[R] KAᗮ := polarEuclideanOrthogonalRangeLinearIsometryEquiv A
  KP.orthogonalDecomposition.trans <|
    (LinearIsometryEquiv.withLpProdCongr (p := 2) eRange eOrth).trans
      KA.orthogonalDecomposition.symm

open scoped Classical in
@[simp]
lemma polarEuclideanFullLinearIsometryEquiv_apply_range [Fintype n]
    (A : Matrix n n R) (x : EuclideanSpace R n) :
    polarEuclideanFullLinearIsometryEquiv A
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A)) x) =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A x := by
  let KP : Submodule R (EuclideanSpace R n) :=
    LinearMap.range
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A))).toLinearMap
  let y : EuclideanSpace R n :=
    (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A)) x
  have hy : y ∈ KP := ⟨x, rfl⟩
  have hproj : KP.orthogonalProjectionOnto y = ⟨y, hy⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y, hy⟩
  have horth : KPᗮ.orthogonalProjectionOnto y = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal KP hy
  suffices
      ((polarEuclideanRangeLinearIsometryEquiv A)
        ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A)) x, ⟨x, rfl⟩⟩ :
          EuclideanSpace R n) =
        (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A x by
    simpa [polarEuclideanFullLinearIsometryEquiv, KP, y, hproj, horth] using this
  exact polarEuclideanRangeLinearEquiv_apply_image A x

open scoped Classical in
/-- The matrix form of the finite-dimensional polar isometry. -/
noncomputable def polarUnitary [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.unitaryGroup n R :=
  ⟨(polarEuclideanFullLinearIsometryEquiv A).toMatrix
      (EuclideanSpace.basisFun n R).toBasis (EuclideanSpace.basisFun n R).toBasis,
    LinearIsometryEquiv.toMatrix_mem_unitaryGroup
      (polarEuclideanFullLinearIsometryEquiv A)
      (EuclideanSpace.basisFun n R) (EuclideanSpace.basisFun n R)⟩

open scoped Classical in
@[simp]
lemma toEuclideanCLM_polarUnitary [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (polarUnitary A : Matrix n n R) =
      (polarEuclideanFullLinearIsometryEquiv A : EuclideanSpace R n →L[R] EuclideanSpace R n) := by
  ext x
  simp [polarUnitary, Matrix.toEuclideanCLM]

open scoped Classical in
/-- Matrix-level polar decomposition produced by the finite-dimensional range
isometry: `A = U * sqrt(Aᴴ * A)`. -/
lemma polarUnitary_mul_cfc_sqrt_conjTranspose_mul_self [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    (polarUnitary A : Matrix n n R) * CFC.sqrt (Aᴴ * A) = A := by
  apply (Matrix.toEuclideanCLM (n := n) (𝕜 := R)).injective
  rw [map_mul]
  change
    (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (polarUnitary A : Matrix n n R) *
        (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) (CFC.sqrt (Aᴴ * A)) =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := R)) A
  rw [toEuclideanCLM_polarUnitary]
  apply ContinuousLinearMap.ext
  intro x
  exact polarEuclideanFullLinearIsometryEquiv_apply_range A x

open scoped Classical in
/-- Rearranged polar decomposition: the positive factor is `Uᴴ * A`. -/
lemma cfc_sqrt_conjTranspose_mul_self_eq_polarUnitary_conjTranspose_mul
    [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    CFC.sqrt (Aᴴ * A) = (polarUnitary A : Matrix n n R)ᴴ * A := by
  calc
    CFC.sqrt (Aᴴ * A) =
        1 * CFC.sqrt (Aᴴ * A) := by rw [one_mul]
    _ = star (polarUnitary A).1 * (polarUnitary A).1 * CFC.sqrt (Aᴴ * A) := by
      rw [Matrix.UnitaryGroup.star_mul_self (polarUnitary A)]
    _ = star (polarUnitary A).1 *
        ((polarUnitary A : Matrix n n R) * CFC.sqrt (Aᴴ * A)) := by
      rw [mul_assoc]
    _ = (polarUnitary A : Matrix n n R)ᴴ * A := by
      have hpolar :
          (polarUnitary A : Matrix n n R) *
              CFC.sqrt (Aᴴ * A) = A :=
        polarUnitary_mul_cfc_sqrt_conjTranspose_mul_self A
      rw [hpolar]
      rw [Matrix.star_eq_conjTranspose]

open scoped Classical in
/-- The polar unitary attains the trace-norm pairing. This is the forward
bridge needed for the usual trace-duality proof of the triangle inequality. -/
lemma traceNorm_eq_re_trace_polarUnitary [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    traceNorm A =
      RCLike.re (((polarUnitary A : Matrix n n R)ᴴ * A).trace) := by
  rw [traceNorm, cfc_sqrt_conjTranspose_mul_self_eq_polarUnitary_conjTranspose_mul A]

open scoped Classical in
/-- The trace-norm polar pairing dominates every unitary trace pairing. -/
lemma re_trace_unitary_conjTranspose_mul_le_traceNorm [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (U : Matrix.unitaryGroup n R) :
    RCLike.re (((U : Matrix n n R)ᴴ * A).trace) ≤ traceNorm A := by
  let P : Matrix n n R := CFC.sqrt (Aᴴ * A)
  have hU_conj_mem : ((U : Matrix n n R)ᴴ) ∈ Matrix.unitaryGroup n R := by
    rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact Matrix.UnitaryGroup.star_mul_self U
  let W : Matrix.unitaryGroup n R :=
    ⟨(U : Matrix n n R)ᴴ * (polarUnitary A : Matrix n n R),
      (Matrix.unitaryGroup n R).mul_mem hU_conj_mem (polarUnitary A).2⟩
  have hP_pos : P.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have htrace :
      (((U : Matrix n n R)ᴴ * A).trace) = (((W : Matrix n n R) * P).trace) := by
    rw [← polarUnitary_mul_cfc_sqrt_conjTranspose_mul_self A]
    simp [W, P, Matrix.mul_assoc]
  calc
    RCLike.re (((U : Matrix n n R)ᴴ * A).trace)
        = RCLike.re (((W : Matrix n n R) * P).trace) := by rw [htrace]
    _ ≤ RCLike.re P.trace :=
      hP_pos.re_trace_unitary_mul_le_trace W
    _ = traceNorm A := rfl

open scoped Classical in
/-- The trace norm satisfies the triangle inequality on square matrices. -/
lemma traceNorm_add_le [Fintype n] [DecidableEq n] (A B : Matrix n n R) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  let U : Matrix.unitaryGroup n R := polarUnitary (A + B)
  calc
    traceNorm (A + B)
        = RCLike.re (((U : Matrix n n R)ᴴ * (A + B)).trace) := by
      exact traceNorm_eq_re_trace_polarUnitary (A + B)
    _ = RCLike.re (((U : Matrix n n R)ᴴ * A).trace) +
        RCLike.re (((U : Matrix n n R)ᴴ * B).trace) := by
      simp [Matrix.mul_add]
    _ ≤ traceNorm A + traceNorm B :=
      add_le_add
        (re_trace_unitary_conjTranspose_mul_le_traceNorm A U)
        (re_trace_unitary_conjTranspose_mul_le_traceNorm B U)

/-- The trace norm satisfies the subtraction triangle inequality. -/
lemma traceNorm_sub_le [Fintype n] [DecidableEq n] (A B : Matrix n n R) :
    traceNorm (A - B) ≤ traceNorm A + traceNorm B := by
  simpa [sub_eq_add_neg] using traceNorm_add_le A (-B)

/-- Finite sums satisfy the trace-norm triangle inequality. -/
lemma traceNorm_finset_sum_le [Fintype n] [DecidableEq n]
    {ι : Type*} (s : Finset ι) (f : ι → Matrix n n R) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (traceNorm_add_le (f a) (∑ i ∈ s, f i)).trans
        (add_le_add le_rfl ih)

/-- Sums over a finite type satisfy the trace-norm triangle inequality. -/
lemma traceNorm_sum_le [Fintype n] [DecidableEq n]
    {ι : Type*} [Fintype ι] (f : ι → Matrix n n R) :
    traceNorm (∑ i, f i) ≤ ∑ i, traceNorm (f i) := by
  classical
  simpa using traceNorm_finset_sum_le (s := Finset.univ) f

end

end Matrix

/-- A square complex matrix viewed with the trace norm instead of the ambient
L2/operator norm instance on `Matrix`. -/
structure TraceNormedMatrix (n : Type*) where
  /-- The underlying square complex matrix. -/
  val : Matrix n n ℂ

namespace TraceNormedMatrix

variable {n : Type*}

/-- Forget the trace-normed wrapper. -/
def equiv (n : Type*) : TraceNormedMatrix n ≃ Matrix n n ℂ where
  toFun A := A.val
  invFun A := ⟨A⟩
  left_inv A := by cases A; rfl
  right_inv A := rfl

instance : Coe (TraceNormedMatrix n) (Matrix n n ℂ) where
  coe A := A.val

@[ext]
lemma ext {A B : TraceNormedMatrix n} (h : (A : Matrix n n ℂ) = B) : A = B := by
  cases A
  cases B
  simp at h
  simp [h]

instance : AddCommGroup (TraceNormedMatrix n) :=
  (equiv n).addCommGroup

instance : Module ℂ (TraceNormedMatrix n) :=
  (equiv n).module ℂ

/-- Forget the trace-normed wrapper as a linear equivalence. -/
def linearEquiv (n : Type*) : TraceNormedMatrix n ≃ₗ[ℂ] Matrix n n ℂ :=
  (equiv n).linearEquiv ℂ

@[simp]
lemma val_add (A B : TraceNormedMatrix n) :
    ((A + B : TraceNormedMatrix n) : Matrix n n ℂ) = A + B :=
  by
    change (equiv n) (A + B) = (equiv n) A + (equiv n) B
    rw [Equiv.add_def]
    simp [equiv]

@[simp]
lemma val_smul (c : ℂ) (A : TraceNormedMatrix n) :
    ((c • A : TraceNormedMatrix n) : Matrix n n ℂ) = c • (A : Matrix n n ℂ) :=
  by
    change (equiv n) (c • A) = c • (equiv n) A
    rw [Equiv.smul_def]
    simp [equiv]

@[simp]
lemma val_zero : ((0 : TraceNormedMatrix n) : Matrix n n ℂ) = 0 :=
  by
    change (equiv n) (0 : TraceNormedMatrix n) = 0
    rw [Equiv.zero_def]
    simp [equiv]

@[simp]
lemma val_neg (A : TraceNormedMatrix n) :
    ((-A : TraceNormedMatrix n) : Matrix n n ℂ) = -(A : Matrix n n ℂ) :=
  by
    change (equiv n) (-A) = -(equiv n) A
    rw [Equiv.neg_def]
    simp [equiv]

@[simp]
lemma val_sub (A B : TraceNormedMatrix n) :
    ((A - B : TraceNormedMatrix n) : Matrix n n ℂ) =
      (A : Matrix n n ℂ) - (B : Matrix n n ℂ) :=
  by
    simp [sub_eq_add_neg]

@[simp]
lemma val_sum {ι : Type*} (s : Finset ι) (f : ι → TraceNormedMatrix n) :
    ((∑ i ∈ s, f i : TraceNormedMatrix n) : Matrix n n ℂ) =
      ∑ i ∈ s, (f i : Matrix n n ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      simp [ha, ih]

lemma val_univ_sum {ι : Type*} [Fintype ι] (f : ι → TraceNormedMatrix n) :
    ((∑ i, f i : TraceNormedMatrix n) : Matrix n n ℂ) =
      ∑ i, (f i : Matrix n n ℂ) := by
  classical
  simp

noncomputable instance [Fintype n] [DecidableEq n] : Norm (TraceNormedMatrix n) where
  norm A := Matrix.traceNorm (A : Matrix n n ℂ)

@[simp]
lemma norm_def [Fintype n] [DecidableEq n] (A : TraceNormedMatrix n) :
    ‖A‖ = Matrix.traceNorm (A : Matrix n n ℂ) :=
  rfl

/-- The trace norm supplies a normed-space core on square complex matrices. -/
lemma normedSpaceCore [Fintype n] [DecidableEq n] :
    NormedSpace.Core ℂ (TraceNormedMatrix n) where
  norm_nonneg A := by
    simpa using Matrix.traceNorm_nonneg (A := (A : Matrix n n ℂ))
  norm_smul c A := by
    simpa using Matrix.traceNorm_smul (A := (A : Matrix n n ℂ)) c
  norm_triangle A B := by
    simpa using
      Matrix.traceNorm_add_le (A := (A : Matrix n n ℂ)) (B := (B : Matrix n n ℂ))
  norm_eq_zero_iff A := by
    constructor
    · intro h
      apply ext
      simpa using (Matrix.traceNorm_zero_iff (A := (A : Matrix n n ℂ))).mp h
    · intro h
      subst h
      simp

noncomputable instance [Fintype n] [DecidableEq n] :
    NormedAddCommGroup (TraceNormedMatrix n) :=
  NormedAddCommGroup.ofCore (normedSpaceCore (n := n))

noncomputable instance [Fintype n] [DecidableEq n] :
    NormedSpace ℂ (TraceNormedMatrix n) :=
  NormedSpace.ofCore (normedSpaceCore (n := n))

instance [Finite n] : Module.Finite ℂ (TraceNormedMatrix n) := by
  classical
  exact Module.Finite.equiv (linearEquiv n).symm

instance [Finite n] : FiniteDimensional ℂ (TraceNormedMatrix n) :=
  inferInstance

end TraceNormedMatrix
