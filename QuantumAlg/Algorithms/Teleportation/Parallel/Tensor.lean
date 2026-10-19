/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Channel
import all QuantumAlg.Algorithms.Teleportation.Parallel.Channel
import all QuantumAlg.Algorithms.Teleportation.Channel
import all QuantumAlg.Algorithms.Teleportation.Mathematics
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Tensor composition of the original teleportation instruments

The bank Kraus matrix is derived from the tensor products of the actual
one-block Bell insertion, Alice operator, measurement projector and Bob
correction [dW19, qcnotes.tex:785-804]. Distributivity of finite sums proves
their composition on arbitrary joint vectors. Factoring an operator's
entries never assumes that its input vector or density factors by block.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open scoped BigOperators

/-- Entries of a finite tensor family, with each original block label kept explicitly. -/
def tensorEntries {α β : Type} (count : Nat) (matrices : Fin count → Matrix α β ℂ) :
    Matrix (Fin count → α) (Fin count → β) ℂ := fun row column =>
  ∏ block : Fin count, matrices block (row block) (column block)

/-- Tensor products compose by the same finite intermediate-index sums as ordinary matrices. -/
lemma tensorEntries_mul {α β γ : Type} [Fintype β] (count : Nat)
    (first : Fin count → Matrix α β ℂ) (second : Fin count → Matrix β γ ℂ) :
    tensorEntries count first * tensorEntries count second =
      tensorEntries count (fun block => first block * second block) := by
  classical
  ext row column
  simp only [Matrix.mul_apply, tensorEntries]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun block middle =>
    first block (row block) middle * second block middle (column block))).symm

/-- Compose every original factor in the source order, with the insertion applied first. -/
def sourceBankKraus (count : Nat) (outcomes : Fin count → Bool × Bool) :
    Matrix (Fin count → Fin 2) (Fin count → Fin 2) ℂ :=
  tensorEntries count (fun block =>
      (teleportCorrection (outcomes block).1 (outcomes block).2 : HilbertOperator (Qubits 1))) *
    tensorEntries count (fun block =>
      aliceProjector (outcomes block).1 (outcomes block).2) *
    tensorEntries count (fun _ => (teleportBellMeasure : HilbertOperator (Qubits 3))) *
    tensorEntries count (fun _ => bellInsertion)

/-- The independently composed bank instrument is exactly the product of corrected branches. -/
lemma sourceBankKraus_eq (count : Nat) (outcomes : Fin count → Bool × Bool) :
    sourceBankKraus count outcomes = correctedBankKraus count outcomes := by
  rw [sourceBankKraus, tensorEntries_mul, tensorEntries_mul, tensorEntries_mul]
  rfl

/-- The entire original instrument is scalar identity, without any input-product assumption. -/
lemma sourceBankKraus_eq_scalar (count : Nat) (outcomes : Fin count → Bool × Bool) :
    sourceBankKraus count outcomes =
      ((2 : ℂ)⁻¹ ^ count) • (1 : HilbertOperator (inputRegister count)) :=
  (sourceBankKraus_eq count outcomes).trans (teleportation_correctedBankKraus_eq count outcomes)

end

end QuantumAlg.QuantumTeleportation.Parallel
