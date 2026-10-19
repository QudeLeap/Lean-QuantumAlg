/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Primitives.PhaseKickback.Basic
import all QuantumAlg.Primitives.QSP.SingleQubit
import all QuantumAlg.Util.Complex
import all QuantumAlg.Util.Polynomial.Complement.Laurent.Witness
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.List.Enum

/-!
# QPP spectral support

Source-facing spectral decomposition and operator extensionality used by QPP.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open NormalizedVector Module.End

noncomputable section

variable {n : ℕ}
variable {U : UnitaryOperator (Qubits n)}

/-! ### Source spectral decomposition interface -/

/-- Hermitian real part `U + U†` used to build a joint spectral decomposition. -/
def QPP.hermitianRealPart {R : Register}
    (U : HilbertOperator R) : HilbertOperator R :=
  U + U.conjTranspose

/-- Hermitian imaginary part `i(U† - U)` used with the real part. -/
def QPP.hermitianImagPart {R : Register}
    (U : HilbertOperator R) : HilbertOperator R :=
  Complex.I • (U.conjTranspose - U)

lemma QPP.hermitianRealPart_isHermitian {R : Register}
    (U : HilbertOperator R) :
    (QPP.hermitianRealPart U).IsHermitian := by
  simpa [QPP.hermitianRealPart] using Matrix.isHermitian_add_transpose_self U

lemma QPP.hermitianImagPart_isHermitian {R : Register}
    (U : HilbertOperator R) :
    (QPP.hermitianImagPart U).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp [QPP.hermitianImagPart]
  ring_nf

lemma QPP.hermitianParts_commute_of_unitary {R : Register}
    (U : UnitaryOperator R) :
    Commute
      (QPP.hermitianRealPart (U : HilbertOperator R))
      (QPP.hermitianImagPart (U : HilbertOperator R)) := by
  rw [Commute, SemiconjBy]
  have hstar_mul :
      (U : HilbertOperator R).conjTranspose * (U : HilbertOperator R) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp U.property
  have hmul_star :
      (U : HilbertOperator R) * (U : HilbertOperator R).conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp U.property
  ext i j
  simp [QPP.hermitianRealPart, QPP.hermitianImagPart,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    hstar_mul, hmul_star]
  ring

lemma QPP.commute_toEuclideanLin_of_matrix_commute
    {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (h : Commute A B) :
    Commute (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) := by
  rw [Commute, SemiconjBy] at h ⊢
  ext v i
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, h]

/-- Joint eigenspace of the Hermitian real and imaginary parts of a unitary. -/
def QPP.jointEigenSubspace {R : Register} (U : UnitaryOperator R)
    (i :
      Eigenvalues (Matrix.toEuclideanLin (QPP.hermitianRealPart (U : HilbertOperator R))) ×
        Eigenvalues (Matrix.toEuclideanLin (QPP.hermitianImagPart (U : HilbertOperator R)))) :
    Submodule ℂ (HilbertVector R) :=
  eigenspace (Matrix.toEuclideanLin (QPP.hermitianRealPart (U : HilbertOperator R)))
      (i.1 : ℂ) ⊓
    eigenspace (Matrix.toEuclideanLin (QPP.hermitianImagPart (U : HilbertOperator R)))
      (i.2 : ℂ)

lemma QPP.jointEigenOrthogonalFamily {R : Register}
    (U : UnitaryOperator R) :
    OrthogonalFamily ℂ
      (fun i =>
        QPP.jointEigenSubspace U i)
      (fun i => (QPP.jointEigenSubspace U i).subtypeₗᵢ) := by
  classical
  refine OrthogonalFamily.of_pairwise ?_
  intro i j hij v hv w hw
  rcases ne_or_eq i.1 j.1 with hfirst | hfirst
  · let hsym :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (QPP.hermitianRealPart_isHermitian (U : HilbertOperator R))
    exact hsym.orthogonalFamily_eigenspaces'.pairwise hfirst hv.1 w hw.1
  · have hsecond : i.2 ≠ j.2 := by
      intro h
      exact hij (Prod.ext hfirst h)
    let hsym :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (QPP.hermitianImagPart_isHermitian (U : HilbertOperator R))
    exact hsym.orthogonalFamily_eigenspaces'.pairwise hsecond hv.2 w hw.2

lemma QPP.jointEigen_iSup_eq_top {R : Register}
    (U : UnitaryOperator R) :
    (iSup (QPP.jointEigenSubspace U)) = ⊤ := by
  classical
  let linA : HilbertVector R →ₗ[ℂ] HilbertVector R :=
    Matrix.toEuclideanLin (QPP.hermitianRealPart (U : HilbertOperator R))
  let linB : HilbertVector R →ₗ[ℂ] HilbertVector R :=
    Matrix.toEuclideanLin (QPP.hermitianImagPart (U : HilbertOperator R))
  have hlinA :
      linA =
        Matrix.toEuclideanLin (QPP.hermitianRealPart (U : HilbertOperator R)) := rfl
  have hlinB :
      linB =
        Matrix.toEuclideanLin (QPP.hermitianImagPart (U : HilbertOperator R)) := rfl
  let hA : linA.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (QPP.hermitianRealPart_isHermitian (U : HilbertOperator R))
  let hB : linB.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (QPP.hermitianImagPart_isHermitian (U : HilbertOperator R))
  let hAB : Commute linA linB := by
    simpa [hlinA, hlinB] using
      QPP.commute_toEuclideanLin_of_matrix_commute
        (QPP.hermitianParts_commute_of_unitary U)
  have hfull :
      (⨆ a : ℂ, ⨆ b : ℂ, eigenspace linA a ⊓ eigenspace linB b) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB
  refine le_antisymm le_top ?_
  rw [← hfull]
  refine iSup_le ?_
  intro a
  refine iSup_le ?_
  intro b
  by_cases ha : HasEigenvalue linA a
  · by_cases hb : HasEigenvalue linB b
    · let ia :
          Eigenvalues (Matrix.toEuclideanLin
            (QPP.hermitianRealPart (U : HilbertOperator R))) :=
          ⟨a, by simpa [hlinA] using ha⟩
      let ib :
          Eigenvalues (Matrix.toEuclideanLin
            (QPP.hermitianImagPart (U : HilbertOperator R))) :=
          ⟨b, by simpa [hlinB] using hb⟩
      calc
        eigenspace linA a ⊓ eigenspace linB b =
            QPP.jointEigenSubspace U (ia, ib) := by
          simp [QPP.jointEigenSubspace, ia, ib, hlinA, hlinB]
        _ ≤ iSup (QPP.jointEigenSubspace U) :=
          le_iSup (QPP.jointEigenSubspace U) (ia, ib)
    · have hbot : eigenspace linB b = ⊥ :=
        not_not.mp (Module.End.hasEigenvalue_iff.not.mp hb)
      rw [hbot, inf_bot_eq]
      exact bot_le
  · have hbot : eigenspace linA a = ⊥ :=
      not_not.mp (Module.End.hasEigenvalue_iff.not.mp ha)
    rw [hbot, bot_inf_eq]
    exact bot_le

/-- The joint eigenspaces form an internal direct-sum decomposition. -/
lemma QPP.jointEigenInternal {R : Register}
    (U : UnitaryOperator R) :
    DirectSum.IsInternal (QPP.jointEigenSubspace U) := by
  classical
  exact (QPP.jointEigenOrthogonalFamily U).isInternal_iff.mpr (by
    rw [QPP.jointEigen_iSup_eq_top U]
    exact Submodule.top_orthogonal_eq_bot)

/-- Orthonormal basis subordinate to the joint eigenspace decomposition. -/
def QPP.jointEigenBasis (U : UnitaryOperator (Qubits n)) :
    OrthonormalBasis (Fin (2 ^ n)) ℂ (HilbertVector (Qubits n)) :=
  (QPP.jointEigenInternal U).subordinateOrthonormalBasis
    (by simp [HilbertVector])
    (QPP.jointEigenOrthogonalFamily U)

/-- Joint eigenvalue index attached to a vector of `jointEigenBasis`. -/
def QPP.jointEigenIndex (U : UnitaryOperator (Qubits n))
    (j : Fin (2 ^ n)) :
    Eigenvalues (Matrix.toEuclideanLin
      (QPP.hermitianRealPart (U : HilbertOperator (Qubits n)))) ×
      Eigenvalues (Matrix.toEuclideanLin
        (QPP.hermitianImagPart (U : HilbertOperator (Qubits n)))) :=
  (QPP.jointEigenInternal U).subordinateOrthonormalBasisIndex
    (by simp [HilbertVector])
    j
    (QPP.jointEigenOrthogonalFamily U)

/-- Unitary eigenvalue reconstructed from the joint real/imaginary eigenvalues. -/
def QPP.jointEigenvalue (U : UnitaryOperator (Qubits n))
    (j : Fin (2 ^ n)) : ℂ :=
  (((QPP.jointEigenIndex U j).1 : ℂ) +
    Complex.I * ((QPP.jointEigenIndex U j).2 : ℂ)) / 2

lemma QPP.applyVec_eq_hermitianParts (U : UnitaryOperator (Qubits n))
    (ψ : HilbertVector (Qubits n)) :
    U.applyVec ψ =
      ((2 : ℂ)⁻¹) •
        (HilbertOperator.applyVec
            (QPP.hermitianRealPart (U : HilbertOperator (Qubits n))) ψ +
          Complex.I •
            HilbertOperator.applyVec
              (QPP.hermitianImagPart (U : HilbertOperator (Qubits n))) ψ) := by
  have hop :
      (U : HilbertOperator (Qubits n)) =
        ((2 : ℂ)⁻¹) •
          (QPP.hermitianRealPart (U : HilbertOperator (Qubits n)) +
            Complex.I •
              QPP.hermitianImagPart (U : HilbertOperator (Qubits n))) := by
    ext i j
    simp only [QPP.hermitianRealPart, QPP.hermitianImagPart,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [← mul_assoc, Complex.I_mul_I]
    ring_nf
  change HilbertOperator.applyVec (U : HilbertOperator (Qubits n)) ψ = _
  conv_lhs => rw [hop]
  rw [HilbertOperator.smul_applyVec, HilbertOperator.add_applyVec]
  simp [HilbertOperator.smul_applyVec]

lemma QPP.jointEigenBasis_gate_eigen
    (U : UnitaryOperator (Qubits n)) (j : Fin (2 ^ n)) :
    U.applyVec (QPP.jointEigenBasis U j) =
      QPP.jointEigenvalue U j • QPP.jointEigenBasis U j := by
  have hmem :
      QPP.jointEigenBasis U j ∈
        QPP.jointEigenSubspace U (QPP.jointEigenIndex U j) :=
    (QPP.jointEigenInternal U).subordinateOrthonormalBasis_subordinate
      (by simp [HilbertVector])
      j
      (QPP.jointEigenOrthogonalFamily U)
  have hreal :
      HilbertOperator.applyVec
          (QPP.hermitianRealPart (U : HilbertOperator (Qubits n)))
          (QPP.jointEigenBasis U j) =
        ((QPP.jointEigenIndex U j).1 : ℂ) •
          QPP.jointEigenBasis U j := by
    have hlin := Module.End.mem_eigenspace_iff.mp hmem.1
    simpa [Matrix.toLpLin_apply, HilbertOperator.applyVec] using hlin
  have himag :
      HilbertOperator.applyVec
          (QPP.hermitianImagPart (U : HilbertOperator (Qubits n)))
          (QPP.jointEigenBasis U j) =
        ((QPP.jointEigenIndex U j).2 : ℂ) •
          QPP.jointEigenBasis U j := by
    have hlin := Module.End.mem_eigenspace_iff.mp hmem.2
    simpa [Matrix.toLpLin_apply, HilbertOperator.applyVec] using hlin
  rw [QPP.applyVec_eq_hermitianParts, hreal, himag]
  ext i
  simp [QPP.jointEigenvalue, PiLp.smul_apply, PiLp.add_apply]
  ring

lemma QPP.jointEigenvalue_norm_eq_one
    (U : UnitaryOperator (Qubits n)) (j : Fin (2 ^ n)) :
    ‖QPP.jointEigenvalue U j‖ = 1 := by
  have hnorm :=
    U.norm_applyVec (QPP.jointEigenBasis U j)
  change ‖U.applyVec (QPP.jointEigenBasis U j)‖ =
    ‖QPP.jointEigenBasis U j‖ at hnorm
  rw [QPP.jointEigenBasis_gate_eigen, norm_smul,
    (QPP.jointEigenBasis U).orthonormal.norm_eq_one j] at hnorm
  simpa using hnorm

/-- Source-facing spectral decomposition certificate for the QPP theorem.
Wang's theorem is stated for
`U = \sum_j e^{i\tau_j} |\chi_j><\chi_j|`; this structure records the
orthonormal eigenbasis and eigenphases used by the Lean proof
[WZYW23, arxiv_v3.tex:641,650-666]. -/
structure QPP.PhaseDecomposition (U : UnitaryOperator (Qubits n)) where
  /-- Eigenphase assigned to each source eigenbasis vector. -/
  phase : Fin (2 ^ n) → ℝ
  /-- Orthonormal eigenbasis used by the QPP proof. -/
  basis : OrthonormalBasis (Fin (2 ^ n)) ℂ (HilbertVector (Qubits n))
  eigen :
    ∀ j : Fin (2 ^ n),
      U.applyVec (basis j) =
        Complex.exp ((phase j : ℂ) * Complex.I) • basis j

namespace QPP.PhaseDecomposition

/-- The eigenbasis vector as a metadata-free normalized vector. -/
def pure (decomp : QPP.PhaseDecomposition (n := n) U)
    (j : Fin (2 ^ n)) : NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector (decomp.basis j)
    (decomp.basis.orthonormal.norm_eq_one j)

@[simp]
lemma pure_coe (decomp : QPP.PhaseDecomposition (n := n) U)
    (j : Fin (2 ^ n)) :
    ((decomp.pure j : NormalizedVector (Qubits n)) : HilbertVector (Qubits n)) =
      decomp.basis j :=
  rfl

/-- Eigenphase equation for the normalized pure-state wrapper. -/
lemma eigen_pure (decomp : QPP.PhaseDecomposition (n := n) U)
    (j : Fin (2 ^ n)) :
    U.applyVec (decomp.pure j : HilbertVector (Qubits n)) =
      Complex.exp ((decomp.phase j : ℂ) * Complex.I) •
        (decomp.pure j : HilbertVector (Qubits n)) := by
  simpa using decomp.eigen j

end QPP.PhaseDecomposition

/-- Every finite-dimensional unitary operator admits the source-facing phase
decomposition used in Wang's QPP theorem: an orthonormal eigenbasis with
eigenvalues written as `e^{iτ}` [WZYW23, arxiv_v3.tex:635-646]. -/
noncomputable def QPP.phaseDecomposition (U : UnitaryOperator (Qubits n)) :
    QPP.PhaseDecomposition U where
  phase := fun j => Complex.arg (QPP.jointEigenvalue U j)
  basis := QPP.jointEigenBasis U
  eigen := by
    intro j
    rw [QPP.jointEigenBasis_gate_eigen]
    rw [QuantumAlg.exp_arg_of_norm_eq_one _
      (QPP.jointEigenvalue_norm_eq_one U j)]

/-- An eigenstate of a unitary operator is an eigenstate of every power. -/
lemma QPP.gate_applyVec_pow_eigenstate {U : UnitaryOperator (Qubits n)}
    {u : NormalizedVector (Qubits n)} {lam : ℂ}
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      lam • (u : HilbertVector (Qubits n))) (m : ℕ) :
    HilbertOperator.applyVec ((U : HilbertOperator (Qubits n)) ^ m)
        (u : HilbertVector (Qubits n)) =
      lam ^ m • (u : HilbertVector (Qubits n)) := by
  have huOp : HilbertOperator.applyVec (U : HilbertOperator (Qubits n))
      (u : HilbertVector (Qubits n)) = lam • (u : HilbertVector (Qubits n)) := hu
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, HilbertOperator.one_applyVec, one_smul]
  | succ m ih =>
      rw [pow_succ, HilbertOperator.mul_applyVec, huOp,
        HilbertOperator.applyVec_smul, ih, smul_smul,
        ← pow_succ']

namespace QPP.Decomposition

/-- Namespace-local spelling of the source-facing QPP phase decomposition. -/
abbrev PhaseDecomposition (U : UnitaryOperator (Qubits n)) :=
  QuantumAlg.QSP.MultiQubit.QPP.PhaseDecomposition U

/-- Namespace-local constructor for the source-facing QPP phase decomposition. -/
noncomputable abbrev phaseDecomposition (U : UnitaryOperator (Qubits n)) :
    PhaseDecomposition U :=
  QuantumAlg.QSP.MultiQubit.QPP.phaseDecomposition U

end QPP.Decomposition



end

end QSP.MultiQubit

end QuantumAlg

end
