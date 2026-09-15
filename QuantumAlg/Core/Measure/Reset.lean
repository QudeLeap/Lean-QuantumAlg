/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Core.Measure.Instrument
import all QuantumAlg.Core.Base.Gate.Unitary
import Mathlib.Algebra.Group.Fin.Basic

/-!
# State update for Z measurement followed by cyclic correction

The branch represented here is the concrete sequence: measure the selected
system in the computational basis, retain the observed classical value, then
apply cyclic subtraction by that value. The identities justify its state
update in any positive dimension, including dimension three.

The calculation uses the projective measurement rule
[dW19, qcnotes.tex:5409], its local two-register form
[dW19, qcnotes.tex:5420], and unitary conjugation
[dW19, qcnotes.tex:5405]. These internal proofs do not replace the execution
statements that store the measurement result and select the corresponding gate.
-/

section

namespace QuantumAlg.ZReset

noncomputable section

variable {dimension : ℕ+}

private instance positiveDimensionNeZero : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

private def cyclicReadback (outcome : Fin dimension) : Equiv.Perm (Fin dimension) where
  toFun i := i + outcome
  invFun i := i - outcome
  left_inv i := add_sub_cancel_right i outcome
  right_inv i := sub_add_cancel i outcome

/-- Cyclic subtraction by the previously observed classical value. -/
def correction (outcome : Fin dimension) : UnitaryOperator (Qudit dimension) :=
  UnitaryOperator.ofPerm (R := Qudit dimension) (cyclicReadback outcome)

/-- The selected unitary subtracts the observed value modulo the dimension. -/
theorem correction_apply_ket (outcome x : Fin dimension) :
    (correction outcome).apply (NormalizedVector.ket x) =
      NormalizedVector.ket (x - outcome) := by
  exact UnitaryOperator.ofPerm_apply_ket (R := Qudit dimension) (cyclicReadback outcome) x

/-- The observed computational-basis state is sent to zero. -/
theorem correction_measured_ket (outcome : Fin dimension) :
    (correction outcome).apply (NormalizedVector.ket outcome) =
      NormalizedVector.ket (R := Qudit dimension) 0 := by
  rw [correction_apply_ket, sub_self]

private theorem permutationDensityEntry {R : Register} (σ : Equiv.Perm R.Index)
    (ρ : DensityOperator R) (i j : R.Index) :
    (DensityOperator.applyUnitary (UnitaryOperator.ofPerm σ) ρ).matrix i j =
      ρ.matrix (σ i) (σ j) := by
  change (σ.permMatrix ℂ * ρ.matrix * (σ.permMatrix ℂ).conjTranspose) i j = _
  rw [Matrix.conjTranspose_permMatrix]
  change ((σ.toPEquiv.toMatrix : HilbertOperator R) * ρ.matrix *
    (σ.symm.toPEquiv.toMatrix : HilbertOperator R)) i j = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem shiftedLabelEqOutcome (outcome x : Fin dimension) :
    x + outcome = outcome ↔ x = 0 := by
  constructor
  · intro h
    exact add_right_cancel (show x + outcome = 0 + outcome by simpa using h)
  · intro h
    simp [h]

/-- State update after a Z outcome and the correction selected by that outcome. -/
def branch (outcome : Fin dimension) (ρ : DensityOperator (Qudit dimension)) :
    DensityOperator (Qudit dimension) :=
  DensityOperator.applyUnitary (correction outcome) (ZMeasurement.branch id outcome ρ)

/-- The branch retains its outcome probability at the zero basis state. -/
theorem reset_branch_entry (outcome : Fin dimension)
    (ρ : DensityOperator (Qudit dimension)) (i j : Fin dimension) :
    (branch outcome ρ).matrix i j =
      if i = 0 ∧ j = 0 then ρ.matrix outcome outcome else 0 := by
  rw [branch, correction, permutationDensityEntry]
  change (ZMeasurement.branch id outcome ρ).matrix (i + outcome) (j + outcome) = _
  rw [ZMeasurement.branch_matrix]
  simp only [id_eq, shiftedLabelEqOutcome]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

/-- Conditional unitary correction retains the measurement outcome probability. -/
theorem reset_branch_mass (outcome : Fin dimension)
    (ρ : DensityOperator (Qudit dimension)) :
    (branch outcome ρ).mass = (ρ.matrix outcome outcome).re := by
  rw [branch, DensityOperator.applyUnitary_mass, ZMeasurement.branch_mass]
  simp

/-- Summing this concrete sequence's outcomes gives the zero-basis projector,
weighted by the input's probability mass. -/
theorem reset_sumBranches_entry (ρ : DensityOperator (Qudit dimension))
    (i j : Fin dimension) :
    (∑ outcome, (branch outcome ρ).matrix) i j =
      if i = 0 ∧ j = 0 then ρ.matrix.trace else 0 := by
  simp only [Matrix.sum_apply, reset_branch_entry]
  by_cases h : i = 0 ∧ j = 0 <;> simp [h, Matrix.trace]

/-- A normalized input yields exactly the zero basis density matrix when the
outcomes of the concrete measurement-and-correction sequence are summed. -/
theorem reset_sumBranches_normalized (ρ : DensityOperator (Qudit dimension))
    (hρ : ρ.IsNormalized) :
    (∑ outcome, (branch outcome ρ).matrix) =
      (DensityOperator.ofPure (NormalizedVector.ket (R := Qudit dimension) 0)).matrix := by
  have htrace : ρ.matrix.trace = 1 := Complex.ext hρ ρ.trace_im_eq_zero
  ext i j
  rw [reset_sumBranches_entry]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [htrace, hi, hj, DensityOperator.ofPure_matrix, NormalizedVector.ket_apply]

/-- The same cyclic subtraction on the selected system leaves every reference
basis label unchanged. -/
private def referenceCorrection (Reference : Register) (outcome : Fin dimension) :
    UnitaryOperator (Register.prod (Qudit dimension) Reference) :=
  UnitaryOperator.ofPerm (R := Register.prod (Qudit dimension) Reference)
    ((cyclicReadback outcome).prodCongr (Equiv.refl Reference.Index))

/-- Local Z measurement and the correction selected from its observed result. -/
private def referenceBranch (Reference : Register) (outcome : Fin dimension)
    (ρ : DensityOperator (Register.prod (Qudit dimension) Reference)) :
    DensityOperator (Register.prod (Qudit dimension) Reference) :=
  DensityOperator.applyUnitary (referenceCorrection Reference outcome)
    (ZMeasurement.branch Prod.fst outcome ρ)

/-- The actual conditional reference block is retained, including off-diagonal
entries. The input need not be separable from the reference. -/
theorem reset_referenceBranch_entry (Reference : Register) (outcome : Fin dimension)
    (ρ : DensityOperator (Register.prod (Qudit dimension) Reference))
    (i j : Fin dimension) (s t : Reference.Index) :
    (referenceBranch Reference outcome ρ).matrix (i, s) (j, t) =
      if i = 0 ∧ j = 0 then ρ.matrix (outcome, s) (outcome, t) else 0 := by
  rw [referenceBranch, referenceCorrection, permutationDensityEntry]
  change (ZMeasurement.branch Prod.fst outcome ρ).matrix
    (i + outcome, s) (j + outcome, t) = _
  rw [ZMeasurement.branch_matrix]
  simp only [shiftedLabelEqOutcome]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

/-- Summing the observed outcomes preserves the reference marginal for the
concrete local measurement-and-correction sequence. -/
theorem reset_referenceSum_entry (Reference : Register)
    (ρ : DensityOperator (Register.prod (Qudit dimension) Reference))
    (i j : Fin dimension) (s t : Reference.Index) :
    (∑ outcome, (referenceBranch Reference outcome ρ).matrix) (i, s) (j, t) =
      if i = 0 ∧ j = 0 then ∑ outcome, ρ.matrix (outcome, s) (outcome, t) else 0 := by
  have hentry (outcome : Fin dimension) :
      (referenceBranch Reference outcome ρ).matrix (i, s) (j, t) =
        if i = 0 ∧ j = 0 then ρ.matrix (outcome, s) (outcome, t) else 0 :=
    reset_referenceBranch_entry Reference outcome ρ i j s t
  simp only [Matrix.sum_apply, hentry]
  by_cases h : i = 0 ∧ j = 0 <;> simp [h]

end

end QuantumAlg.ZReset

end
