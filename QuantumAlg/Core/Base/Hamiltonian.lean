/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Basic
public import QuantumAlg.Core.Base.Gate.OperatorNorm
import all QuantumAlg.Core.Base.Gate.OperatorNorm
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hamiltonians on finite registers

A `Hamiltonian R` is a Hermitian raw operator on the register `R`. This module
owns the qudit-agnostic vocabulary every Hamiltonian problem statement needs:
the Hermitian-closed operations (`+`, `-`, real scaling, finite sums), the
operator norm, and the spectral words `eigenvalues`, `groundEnergy`,
`spectralGap`, `IsGroundState`.

Concrete Hamiltonian families (Pauli sums, lattice models) live in
`QuantumAlg.Components`; the time-evolution oracle lives in
`QuantumAlg.Components.Oracle.TimeEvolution`; product-formula error analysis
lives in `QuantumAlg.Analysis`.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

/-- A Hamiltonian on a finite register is a Hermitian Hilbert-space operator. -/
abbrev Hamiltonian (R : Register) : Type :=
  { H : HilbertOperator R // H.IsHermitian }

namespace Hamiltonian

variable {R : Register}

instance : Coe (Hamiltonian R) (HilbertOperator R) := ⟨Subtype.val⟩

theorem coe_mk (H : HilbertOperator R) (hH : H.IsHermitian) :
    (((⟨H, hH⟩ : Hamiltonian R) : HilbertOperator R)) = H :=
  rfl

theorem isHermitian (H : Hamiltonian R) : (H : HilbertOperator R).IsHermitian :=
  H.2

@[ext]
theorem ext {H₁ H₂ : Hamiltonian R} (h : (H₁ : HilbertOperator R) = H₂) : H₁ = H₂ :=
  Subtype.ext h

/-! ## Hermitian-closed operations -/

/-- The sum of two Hamiltonian operators is again Hermitian. -/
def add (H₁ H₂ : Hamiltonian R) : Hamiltonian R :=
  ⟨(H₁ : HilbertOperator R) + (H₂ : HilbertOperator R), H₁.2.add H₂.2⟩

@[simp]
theorem coe_add (H₁ H₂ : Hamiltonian R) :
    ((add H₁ H₂ : Hamiltonian R) : HilbertOperator R)
      = (H₁ : HilbertOperator R) + (H₂ : HilbertOperator R) :=
  rfl

instance : Zero (Hamiltonian R) := ⟨⟨0, Matrix.isHermitian_zero⟩⟩

instance : Add (Hamiltonian R) := ⟨add⟩

instance : Neg (Hamiltonian R) := ⟨fun H => ⟨-(H : HilbertOperator R), H.2.neg⟩⟩

instance : Sub (Hamiltonian R) :=
  ⟨fun H₁ H₂ => ⟨(H₁ : HilbertOperator R) - (H₂ : HilbertOperator R), H₁.2.sub H₂.2⟩⟩

theorem isSelfAdjoint_ofReal (c : ℝ) : IsSelfAdjoint (c : ℂ) := by
  rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]

instance : SMul ℝ (Hamiltonian R) :=
  ⟨fun c H => ⟨(c : ℂ) • (H : HilbertOperator R), H.2.smul (isSelfAdjoint_ofReal c)⟩⟩

@[simp]
theorem coe_zero : ((0 : Hamiltonian R) : HilbertOperator R) = 0 :=
  rfl

@[simp]
theorem coe_hAdd (H₁ H₂ : Hamiltonian R) :
    ((H₁ + H₂ : Hamiltonian R) : HilbertOperator R)
      = (H₁ : HilbertOperator R) + (H₂ : HilbertOperator R) :=
  rfl

@[simp]
theorem coe_neg (H : Hamiltonian R) :
    ((-H : Hamiltonian R) : HilbertOperator R) = -(H : HilbertOperator R) :=
  rfl

@[simp]
theorem coe_sub (H₁ H₂ : Hamiltonian R) :
    ((H₁ - H₂ : Hamiltonian R) : HilbertOperator R)
      = (H₁ : HilbertOperator R) - (H₂ : HilbertOperator R) :=
  rfl

@[simp]
theorem coe_smul (c : ℝ) (H : Hamiltonian R) :
    ((c • H : Hamiltonian R) : HilbertOperator R) = (c : ℂ) • (H : HilbertOperator R) :=
  rfl

theorem isHermitian_sum_coe {ι : Type} [Fintype ι] (family : ι → Hamiltonian R) :
    (∑ i, (family i : HilbertOperator R)).IsHermitian :=
  Finset.sum_induction _ (fun A : HilbertOperator R => A.IsHermitian)
    (fun _ _ hA hB => hA.add hB) Matrix.isHermitian_zero (fun i _ => (family i).2)

/-- The Hamiltonian sum of a finite family of terms. -/
def sum {ι : Type} [Fintype ι] (family : ι → Hamiltonian R) : Hamiltonian R :=
  ⟨∑ i, (family i : HilbertOperator R), isHermitian_sum_coe family⟩

@[simp]
theorem coe_sum {ι : Type} [Fintype ι] (family : ι → Hamiltonian R) :
    ((sum family : Hamiltonian R) : HilbertOperator R) = ∑ i, (family i : HilbertOperator R) :=
  rfl

/-- The operator norm of a Hamiltonian. -/
def opNorm (H : Hamiltonian R) : ℝ :=
  HilbertOperator.opNorm (H : HilbertOperator R)

@[simp]
theorem opNorm_eq (H : Hamiltonian R) : H.opNorm = HilbertOperator.opNorm (H : HilbertOperator R) :=
  rfl

theorem opNorm_nonneg (H : Hamiltonian R) : 0 ≤ H.opNorm :=
  HilbertOperator.opNorm_nonneg _

theorem opNorm_sum_le {ι : Type} [Fintype ι] (family : ι → Hamiltonian R) :
    (sum family).opNorm ≤ ∑ i, (family i).opNorm :=
  HilbertOperator.opNorm_sum_le _

/-! ## Spectrum -/

/-- The real eigenvalues of a Hamiltonian, indexed by the register basis. -/
def eigenvalues (H : Hamiltonian R) : R.Index → ℝ :=
  H.2.eigenvalues

/-- A choice of orthonormal eigenvector basis. -/
def eigenvectorBasis (H : Hamiltonian R) : OrthonormalBasis R.Index ℂ (HilbertVector R) :=
  H.2.eigenvectorBasis

/-- `ψ` is an eigenvector of `H` with real eigenvalue `E`: `H ψ = E ψ`. -/
def IsEigenvector (H : Hamiltonian R) (E : ℝ) (ψ : HilbertVector R) : Prop :=
  (H : HilbertOperator R).mulVec ψ.ofLp = (E : ℂ) • ψ.ofLp

theorem isEigenvector_eigenvectorBasis (H : Hamiltonian R) (i : R.Index) :
    H.IsEigenvector (H.eigenvalues i) (H.eigenvectorBasis i) := by
  unfold IsEigenvector eigenvalues eigenvectorBasis
  rw [H.2.mulVec_eigenvectorBasis i]
  ext j
  simp [Complex.real_smul]

theorem norm_eigenvectorBasis (H : Hamiltonian R) (i : R.Index) :
    ‖H.eigenvectorBasis i‖ = 1 :=
  H.eigenvectorBasis.orthonormal.1 i

/-- The ground energy: the least eigenvalue. -/
def groundEnergy [Nonempty R.Index] (H : Hamiltonian R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty H.eigenvalues

theorem groundEnergy_le_eigenvalue [Nonempty R.Index] (H : Hamiltonian R) (i : R.Index) :
    H.groundEnergy ≤ H.eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_eigenvalue_eq_groundEnergy [Nonempty R.Index] (H : Hamiltonian R) :
    ∃ i, H.eigenvalues i = H.groundEnergy := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty H.eigenvalues
  exact ⟨i, hi.symm⟩

/-- `ψ` is a normalized ground state of `H`. -/
def IsGroundState [Nonempty R.Index] (H : Hamiltonian R) (ψ : HilbertVector R) : Prop :=
  ‖ψ‖ = 1 ∧ H.IsEigenvector H.groundEnergy ψ

theorem exists_groundState [Nonempty R.Index] (H : Hamiltonian R) :
    ∃ ψ : HilbertVector R, H.IsGroundState ψ := by
  obtain ⟨i, hi⟩ := H.exists_eigenvalue_eq_groundEnergy
  refine ⟨H.eigenvectorBasis i, H.norm_eigenvectorBasis i, ?_⟩
  rw [← hi]
  exact H.isEigenvector_eigenvectorBasis i

/-- The excited part of the spectrum: eigenvalue indices strictly above the
ground energy. -/
def excitedIndices [Nonempty R.Index] (H : Hamiltonian R) : Finset R.Index :=
  Finset.univ.filter fun i => H.groundEnergy < H.eigenvalues i

/-- The spectral gap: the least positive distance from the ground energy to
another eigenvalue, or `0` if the spectrum is a single point. -/
def spectralGap [Nonempty R.Index] (H : Hamiltonian R) : ℝ :=
  if h : H.excitedIndices.Nonempty then
    H.excitedIndices.inf' h H.eigenvalues - H.groundEnergy
  else 0

theorem spectralGap_nonneg [Nonempty R.Index] (H : Hamiltonian R) : 0 ≤ H.spectralGap := by
  unfold spectralGap
  split_ifs with h
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf' h H.eigenvalues
    rw [hmin, sub_nonneg]
    exact H.groundEnergy_le_eigenvalue i
  · exact le_rfl

theorem spectralGap_pos [Nonempty R.Index] (H : Hamiltonian R)
    (h : H.excitedIndices.Nonempty) : 0 < H.spectralGap := by
  unfold spectralGap
  rw [dif_pos h]
  obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf' h H.eigenvalues
  rw [hmin, sub_pos]
  exact (Finset.mem_filter.mp hi).2

/-- Every excited eigenvalue is at least one gap above the ground energy. -/
theorem groundEnergy_add_spectralGap_le [Nonempty R.Index] (H : Hamiltonian R) (i : R.Index)
    (hi : H.groundEnergy < H.eigenvalues i) :
    H.groundEnergy + H.spectralGap ≤ H.eigenvalues i := by
  have hmem : i ∈ H.excitedIndices := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have hne : H.excitedIndices.Nonempty := ⟨i, hmem⟩
  unfold spectralGap
  rw [dif_pos hne, add_sub_cancel]
  exact Finset.inf'_le _ hmem

end Hamiltonian

end

end QuantumAlg

end
