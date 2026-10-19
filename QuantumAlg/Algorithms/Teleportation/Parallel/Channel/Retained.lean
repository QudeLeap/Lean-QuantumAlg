/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Channel.Retained
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Projector
import all QuantumAlg.Algorithms.Teleportation.Parallel.Tensor
import all QuantumAlg.Algorithms.Teleportation.Channel
import all QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Exact source branches with Alice's measured systems retained

The source's square measurement projector factors through the selector and
its adjoint, preserving both measured quantum systems [dW19, qcnotes.tex:802].
Bob's correction therefore yields one half of the insertion of Alice's
actual measured label, with identity on the unknown input [dW19,
qcnotes.tex:792,804]. The tensor identity retains arbitrary joint input
columns and hence does not assume independence between teleported systems
or their external reference [dW19, qcnotes.tex:809].
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.RetainedSource

noncomputable section

open MeasurementInstrument ProjectorCoordinates RetainedAlice
open scoped BigOperators

private lemma selectHead_projector {B T : Type} [Fintype T]
    [DecidableEq B] [DecidableEq T] (label : B) :
    (selectHead (T := T) label).conjTranspose * selectHead label =
      Matrix.diagonal (fun entry : B × T => if entry.1 = label then (1 : ℂ) else 0) := by
  ext ⟨first, row⟩ ⟨second, column⟩
  by_cases left : label = first <;> by_cases right : label = second <;>
    by_cases same : row = column <;>
    simp_all [selectHead, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply] <;>
    aesop

/-- Alice's source selector, in the complete original integer basis. -/
def selector (label : Fin 4) : Matrix (Fin 2) (Fin 8) ℂ :=
  (selectHead (T := Fin 2) label).submatrix id
    ((finProdFinEquiv (m := 4) (n := 2)).symm : Fin 8 → Fin 4 × Fin 2)

/-- The square source projector keeps, rather than removes, Alice's measured factors. -/
lemma sourceProjector_eq_selector (label : Fin 4) :
    sourceProjector label = (selector label).conjTranspose * selector label := by
  let pair : Fin 8 ≃ Fin 4 × Fin 2 := (finProdFinEquiv (m := 4) (n := 2)).symm
  calc
    _ = Matrix.diagonal (fun entry : Fin 8 =>
        if (pair entry).1 = label then (1 : ℂ) else 0) := by
      apply congrArg Matrix.diagonal
      funext entry
      exact congrArg (fun value : Fin 4 => if value = label then (1 : ℂ) else 0)
        (binaryAlice_eq_head entry)
    _ = (Matrix.diagonal (fun entry : Fin 4 × Fin 2 =>
        if entry.1 = label then (1 : ℂ) else 0)).submatrix pair pair :=
      (Matrix.submatrix_diagonal_equiv
        (fun entry : Fin 4 × Fin 2 => if entry.1 = label then (1 : ℂ) else 0) pair).symm
    _ = ((selectHead (T := Fin 2) label).conjTranspose * selectHead label).submatrix
        pair pair :=
      congrArg (fun matrix : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ =>
        matrix.submatrix pair pair) (selectHead_projector label).symm
    _ = _ := (Matrix.submatrix_mul_equiv (selectHead (T := Fin 2) label).conjTranspose
      (selectHead label) pair (Equiv.refl (Fin 2)) pair).symm

private lemma correction_eq_controlled (operator : HilbertOperator (Qubits 1)) :
    HilbertOperator.tensor (1 : HilbertOperator (Qubits 2)) operator =
      (controlled (fun _ : Fin 4 => operator)).submatrix
        ((finProdFinEquiv (m := 4) (n := 2)).symm : Fin 8 → Fin 4 × Fin 2)
        (finProdFinEquiv (m := 4) (n := 2)).symm := by
  ext row column
  change (if ((finProdFinEquiv (m := 4) (n := 2)).symm row : Fin 4 × Fin 2).1 =
      ((finProdFinEquiv (m := 4) (n := 2)).symm column : Fin 4 × Fin 2).1 then (1 : ℂ) else 0) *
        operator ((finProdFinEquiv (m := 4) (n := 2)).symm row : Fin 4 × Fin 2).2
          ((finProdFinEquiv (m := 4) (n := 2)).symm column : Fin 4 × Fin 2).2 =
    if ((finProdFinEquiv (m := 4) (n := 2)).symm row : Fin 4 × Fin 2).1 =
      ((finProdFinEquiv (m := 4) (n := 2)).symm column : Fin 4 × Fin 2).1 then
        operator ((finProdFinEquiv (m := 4) (n := 2)).symm row : Fin 4 × Fin 2).2
          ((finProdFinEquiv (m := 4) (n := 2)).symm column : Fin 4 × Fin 2).2 else 0
  split <;> simp

/-- A correction on Bob commutes through reinsertion of Alice's actual measured label. -/
lemma correction_selector_insert (label : Fin 4) (operator : HilbertOperator (Qubits 1)) :
    HilbertOperator.tensor (1 : HilbertOperator (Qubits 2)) operator *
      (selector label).conjTranspose = (selector label).conjTranspose * operator := by
  let pair : Fin 8 ≃ Fin 4 × Fin 2 := (finProdFinEquiv (m := 4) (n := 2)).symm
  rw [correction_eq_controlled]
  calc
    _ = (controlled (fun _ : Fin 4 => operator) *
        (selectHead (T := Fin 2) label).conjTranspose).submatrix pair id :=
      Matrix.submatrix_mul_equiv (controlled (fun _ : Fin 4 => operator))
        (selectHead (T := Fin 2) label).conjTranspose pair pair id
    _ = ((selectHead (T := Fin 2) label).conjTranspose * operator).submatrix pair id :=
      congrArg (fun matrix : Matrix (Fin 4 × Fin 2) (Fin 2) ℂ => matrix.submatrix pair id)
        (controlled_insert label operator)
    _ = _ := (Matrix.submatrix_mul_equiv (selectHead (T := Fin 2) label).conjTranspose
      operator pair (Equiv.refl (Fin 2)) id).symm

/-- The four actual source factors, with all three output quantum systems retained. -/
def retainedSourceKraus (first second : Bool) : Matrix (Fin 8) (Fin 2) ℂ :=
  HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
      (teleportCorrection first second : HilbertOperator (Qubits 1)) *
    sourceProjector (outcomeValue first second) *
    (teleportBellMeasure : HilbertOperator (Qubits 3)) * bellInsertion

/-- The retained source branch is half of Alice's actual ket insertion and identity on Bob. -/
lemma retainedSourceKraus_eq (first second : Bool) :
    retainedSourceKraus first second =
      (2 : ℂ)⁻¹ • (selector (outcomeValue first second)).conjTranspose := by
  let label := outcomeValue first second
  let correction : HilbertOperator (Qubits 1) := teleportCorrection first second
  have selected : selector label = aliceProjector first second := by
    ext row column
    by_cases head : outcomeValue first second =
        ((finProdFinEquiv (m := 4) (n := 2)).symm column).1 <;>
      by_cases tail : row = ((finProdFinEquiv (m := 4) (n := 2)).symm column).2 <;>
      simp [selector, label, aliceProjector, selectHead, head, tail]
  calc
    _ = (HilbertOperator.tensor (1 : HilbertOperator (Qubits 2)) correction *
        (selector label).conjTranspose) *
        (selector label * (teleportBellMeasure : HilbertOperator (Qubits 3)) *
          bellInsertion) := by
      rw [retainedSourceKraus, sourceProjector_eq_selector]
      simp only [Matrix.mul_assoc, label, correction]
    _ = ((selector label).conjTranspose * correction) *
        (selector label * (teleportBellMeasure : HilbertOperator (Qubits 3)) *
          bellInsertion) := congrArg (fun matrix : Matrix (Fin 8) (Fin 2) ℂ =>
      matrix * (selector label * (teleportBellMeasure : HilbertOperator (Qubits 3)) *
        bellInsertion)) (correction_selector_insert label correction)
    _ = (selector label).conjTranspose * correctedKraus first second := by
      rw [correctedKraus, ← selected]
      simp only [Matrix.mul_assoc, correction]
    _ = _ := by
      rw [teleportation_correctedKraus_eq_half_identity, Matrix.mul_smul, Matrix.mul_one]

/-- Tensoring the retained branch identity allows arbitrary entangled input columns. -/
lemma tensor_retainedSourceKraus (count : Nat) (outcomes : Fin count → Bool × Bool) :
    tensorEntries count (fun block => retainedSourceKraus
      (outcomes block).1 (outcomes block).2) =
      ((2 : ℂ)⁻¹ ^ count) • tensorEntries count (fun block =>
        (selector (outcomeValue (outcomes block).1 (outcomes block).2)).conjTranspose) := by
  ext row column
  simp only [tensorEntries, retainedSourceKraus_eq, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end QuantumAlg.QuantumTeleportation.Parallel.RetainedSource
