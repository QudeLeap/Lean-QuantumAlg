/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Density

/-!
# Computational-basis measurement instruments

A readout function partitions the full computational basis into outcomes.
The corresponding branch keeps every matrix index, including any unmeasured
reference system. The unnormalized update is `P ρ P`; its trace is the outcome
probability [dW19, qcnotes.tex:5409]. No outcome discards quantum storage.
-/

@[expose] public section

open scoped ComplexOrder

namespace QuantumAlg
namespace ZMeasurement

noncomputable section

variable {R : Register} {Outcome : Type} [DecidableEq Outcome]

/-- Projector onto one readout fiber. Measuring only a subsystem uses its
basis-coordinate projection as the readout [dW19, qcnotes.tex:5420]. -/
def projector (readout : R.Index → Outcome) (outcome : Outcome) : HilbertOperator R :=
  Matrix.diagonal (fun i => if readout i = outcome then 1 else 0)

/-- The projector's left and right actions retain precisely one readout fiber. -/
lemma projector_sandwich_entry (readout : R.Index → Outcome) (outcome : Outcome)
    (A : HilbertOperator R) (i j : R.Index) :
    (projector readout outcome * A * (projector readout outcome).conjTranspose) i j =
      if readout i = outcome ∧ readout j = outcome then A i j else 0 := by
  by_cases hi : readout i = outcome <;> by_cases hj : readout j = outcome <;>
    simp [projector, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_conjTranspose, hi, hj]

/-- Unnormalized probability-bearing measurement branch.
This is the numerator of the normalized update in [dW19, qcnotes.tex:5412]. -/
def branch (readout : R.Index → Outcome) (outcome : Outcome)
    (ρ : DensityOperator R) : DensityOperator R where
  matrix := projector readout outcome * ρ.matrix * (projector readout outcome).conjTranspose
  positive := ρ.positive.mul_mul_conjTranspose_same (projector readout outcome)
  trace_le_one := by
    apply le_trans _ ρ.trace_le_one
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [projector_sandwich_entry]
    by_cases h : readout i = outcome
    · simp [h]
    · simp only [h, false_and, ite_false, Complex.zero_re]
      exact (Complex.nonneg_iff.mp ρ.positive.diag_nonneg).1

/-- Entrywise branch semantics, retaining coherence within the selected fiber. -/
@[simp] lemma branch_matrix (readout : R.Index → Outcome) (outcome : Outcome)
    (ρ : DensityOperator R) (i j : R.Index) :
    (branch readout outcome ρ).matrix i j =
      if readout i = outcome ∧ readout j = outcome then ρ.matrix i j else 0 :=
  projector_sandwich_entry readout outcome ρ.matrix i j

/-- A branch's mass is the sum of its selected diagonal entries, including
all unmeasured subsystem indices. -/
lemma branch_mass (readout : R.Index → Outcome) (outcome : Outcome)
    (ρ : DensityOperator R) :
    (branch readout outcome ρ).mass =
      ∑ i, if readout i = outcome then (ρ.matrix i i).re else 0 := by
  simp only [DensityOperator.mass, Matrix.trace, Matrix.diag, Complex.re_sum,
    branch_matrix, and_self, apply_ite, Complex.zero_re]

/-- The complete measurement preserves total probability
[dW19, qcnotes.tex:5409]. -/
lemma sum_branch_mass [Fintype Outcome] (readout : R.Index → Outcome)
    (ρ : DensityOperator R) :
    ∑ outcome, (branch readout outcome ρ).mass = ρ.mass := by
  simp only [branch_mass]
  rw [Finset.sum_comm]
  simp [DensityOperator.mass, Matrix.trace]

/-- Repeating Z measurement cannot change the supported outcome. -/
lemma repeat_branch (readout : R.Index → Outcome) (first second : Outcome)
    (ρ : DensityOperator R) :
    branch readout second (branch readout first ρ) =
      if second = first then branch readout first ρ else DensityOperator.zero R := by
  apply DensityOperator.ext
  ext i j
  by_cases h : second = first
  · subst second
    simp only [ite_true, branch_matrix]
    split_ifs <;> rfl
  · simp only [h, ite_false, DensityOperator.zero_matrix, Matrix.zero_apply, branch_matrix]
    by_cases hi : readout i = second
    · have hfirst : readout i ≠ first := fun heq => h (hi.symm.trans heq)
      simp [hfirst]
    · simp [hi]

/-- An impossible input branch stays impossible. -/
@[simp] lemma branch_zero (readout : R.Index → Outcome) (outcome : Outcome) :
    branch readout outcome (DensityOperator.zero R) = DensityOperator.zero R := by
  apply DensityOperator.ext
  ext i j
  simp only [branch_matrix, DensityOperator.zero_matrix, Matrix.zero_apply, ite_self]

end

end ZMeasurement
end QuantumAlg
