/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ext

/-!
# Exact matrix identities for measured control and retained quantum banks

The identities retain arbitrary external reference systems and subnormalized
conditional states. They complement the existing computational-basis measurement
instrument with row-Kraus composition and explicit basis-bank factors.
-/

namespace QuantumAlg.MeasurementInstrument

noncomputable section

open scoped BigOperators ComplexConjugate

section Blocks

variable {B T I J : Type} [Fintype B] [Fintype T]
  [DecidableEq B] [DecidableEq T]

/-- Extract a measured head branch and discard its quantum basis factor. -/
public def selectHead (b : B) : Matrix T (B × T) Complex :=
  fun i x => if b = x.1 then if i = x.2 then 1 else 0 else 0

/-- A genuine block-controlled operator on a head and its tail. -/
public def controlled (U : B → Matrix T T Complex) : Matrix (B × T) (B × T) Complex :=
  fun x y => if x.1 = y.1 then U x.1 x.2 y.2 else 0

/-- The leading one-system gate leaves the tail untouched. -/
public def leading (H : Matrix B B Complex) : Matrix (B × T) (B × T) Complex :=
  fun x y => if x.2 = y.2 then H x.1 y.1 else 0

/-- Measuring after coherent control equals the selected feedback operation. -/
public lemma selectHead_controlled (b : B) (U : B → Matrix T T Complex) :
    selectHead b * controlled U = U b * selectHead b := by
  ext i x
  simp [Matrix.mul_apply, Fintype.sum_prod_type, selectHead, controlled,
    mul_ite, ite_mul]
  split <;> simp_all

/-- The phase case is the same exact Kraus identity, not merely a probability law. -/
public lemma selectHead_controlled_phase (b : B) (p : B → T → Complex) :
    selectHead b * controlled (fun c => Matrix.diagonal (p c)) =
      Matrix.diagonal (p b) * selectHead b :=
  selectHead_controlled b _

/-- One leading gate followed by a head measurement. -/
public def headKraus (H : Matrix B B Complex) (b : B) : Matrix T (B × T) Complex :=
  selectHead b * leading H

/-- One coherent recursion stage, with the rightmost factor executed first. -/
public def coherentStage (H : Matrix B B Complex)
    (U : B → Matrix T T Complex) (A : Matrix T T Complex) :
    Matrix (B × T) (B × T) Complex :=
  controlled (fun _ : B => A) * controlled U * leading H

/-- Move the head measurement before both operations preserving its basis value. -/
public lemma selectHead_stage (H : Matrix B B Complex)
    (U : B → Matrix T T Complex) (A : Matrix T T Complex) (b : B) :
    selectHead b * coherentStage H U A = A * U b * headKraus H b := by
  unfold coherentStage headKraus
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, selectHead_controlled]
  rw [Matrix.mul_assoc A (selectHead (T := T) b) (controlled U), selectHead_controlled]
  simp only [Matrix.mul_assoc]

/-- A final basis-measurement row. -/
public def rowKraus (A : Matrix I J Complex) (y : I) : Matrix Unit J Complex :=
  fun _ x => A y x

omit [Fintype T] [DecidableEq T] in
public lemma rowKraus_mul [Fintype I] (A : Matrix J I Complex)
    (D : Matrix I T Complex) (y : J) :
    rowKraus (A * D) y = rowKraus A y * D := by
  rfl

public lemma rowKraus_select (A : Matrix (B × T) I Complex) (b : B) (y : T) :
    rowKraus (selectHead b * A) y = rowKraus A (b, y) := by
  ext u x
  simp [rowKraus, Matrix.mul_apply, selectHead, Fintype.sum_prod_type, ite_mul]

/-- The row of a complete coherent stage is the adaptive composition of Kraus rows. -/
public lemma rowKraus_stage (H : Matrix B B Complex)
    (U : B → Matrix T T Complex) (A : Matrix T T Complex) (b : B) (y : T) :
    rowKraus (coherentStage H U A) (b, y) =
      rowKraus A y * U b * headKraus H b := by
  rw [← rowKraus_select, selectHead_stage, rowKraus_mul, rowKraus_mul]

/-- Diagonal feedback gives exactly the matrix recurrence used by the QFT source. -/
public lemma phaseStage_entry (H : Matrix B B Complex)
    (p : B → T → Complex) (A : Matrix T T Complex) (b c : B) (y x : T) :
    coherentStage H (fun a => Matrix.diagonal (p a)) A (b, y) (c, x) =
      A y x * p b x * H b c := by
  have result := congrArg (fun K : Matrix Unit (B × T) Complex => K () (c, x))
    (rowKraus_stage H (fun a => Matrix.diagonal (p a)) A b y)
  simpa [rowKraus, headKraus, selectHead, leading, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.diagonal, mul_ite, ite_mul] using result

end Blocks

section Reference

variable {I O R : Type} [Fintype I] [Fintype R] [DecidableEq R] [DecidableEq O]

/-- A scalar-output Kraus row tensored with identity on an arbitrary reference. -/
public def withReference (K : Matrix Unit I Complex) : Matrix R (I × R) Complex :=
  fun r x => K () x.1 * (if r = x.2 then 1 else 0)

/-- The unnormalized conditional reference state, valid even for entangled inputs. -/
public def referenceBranch (K : Matrix Unit I Complex)
    (ρ : Matrix (I × R) (I × R) Complex) : Matrix R R Complex :=
  withReference K * ρ * (withReference K).conjTranspose

/-- Common comparison interface: classical outcome plus the remaining reference. -/
public def cqInstrument (K : O → Matrix Unit I Complex)
    (ρ : Matrix (I × R) (I × R) Complex) : Matrix (O × R) (O × R) Complex :=
  fun x y => if x.1 = y.1 then referenceBranch (K x.1) ρ x.2 y.2 else 0

end Reference

section RetainedBank

variable {B I O R : Type} [Fintype I] [Fintype R]
  [DecidableEq B] [DecidableEq R] [DecidableEq O]

/-- Insert an explicitly retained quantum bank in a fixed computational basis state. -/
public def bankEmbedding (label : B) : Matrix (B × R) R Complex :=
  fun x r => if x.1 = label then if x.2 = r then 1 else 0 else 0

/-- A branch Kraus operator retaining the measured or reset quantum bank. -/
public def bankKraus (label : B) (K : Matrix Unit I Complex) :
    Matrix (B × R) (I × R) Complex :=
  bankEmbedding label * withReference K

/-- The complete conditional quantum state, with the bank still present. -/
public def bankBranch (label : B) (K : Matrix Unit I Complex)
    (ρ : Matrix (I × R) (I × R) Complex) : Matrix (B × R) (B × R) Complex :=
  bankKraus label K * ρ * (bankKraus label K).conjTranspose

omit [Fintype I] in
/-- This is the actual projector-after-transform Kraus matrix on the bank and reference. -/
public lemma bankKraus_coherent_entry (A : Matrix B I Complex) (y b : B)
    (i : I) (r s : R) :
    bankKraus y (rowKraus A y) (b, r) (i, s) =
      (if b = y then A y i else 0) * (if r = s then 1 else 0) := by
  simp [bankKraus, bankEmbedding, withReference, rowKraus, Matrix.mul_apply,
    mul_ite, ite_mul]
  by_cases h : b = y <;> simp [h]

/-- Both a retained measured bank and a reset bank factor through the same reference state. -/
public lemma bankBranch_factor (label : B) (K : Matrix Unit I Complex)
    (ρ : Matrix (I × R) (I × R) Complex) :
    bankBranch label K ρ =
      bankEmbedding label * referenceBranch K ρ * (bankEmbedding label).conjTranspose := by
  simp only [bankBranch, bankKraus, referenceBranch, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- Explicit computational-basis block: `|label><label|` tensored with the reference branch. -/
public lemma bankBranch_entry (label b c : B) (K : Matrix Unit I Complex)
    (ρ : Matrix (I × R) (I × R) Complex) (r s : R) :
    bankBranch label K ρ (b, r) (c, s) =
      if b = label ∧ c = label then referenceBranch K ρ r s else 0 := by
  rw [bankBranch_factor]
  by_cases hb : b = label
  · subst b
    by_cases hc : c = label
    · subst c
      simp [bankEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
        mul_ite, ite_mul]
    · simp [bankEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, hc]
  · simp [bankEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, hb]

/-- Full instrument: classical record, explicit quantum bank, and untouched reference. -/
public def retainedInstrument (label : O → B) (K : O → Matrix Unit I Complex)
    (ρ : Matrix (I × R) (I × R) Complex) :
    Matrix (O × (B × R)) (O × (B × R)) Complex :=
  fun x y => if x.1 = y.1 then bankBranch (label x.1) (K x.1) ρ x.2 y.2 else 0

/-- An explicit output-wire permutation, such as the final QFT bit reversal. -/
public def permuteOutput (e : O ≃ B) (A : Matrix O I Complex) : Matrix B I Complex :=
  fun b i => A (e.symm b) i

omit [DecidableEq O] in
/-- Applying the output permutation changes the retained bank basis label explicitly. -/
public lemma outputPermutation_branch_factor (e : O ≃ B)
    (A : Matrix O I Complex) (y : O)
    (ρ : Matrix (I × R) (I × R) Complex) :
    bankBranch (e y) (rowKraus (permuteOutput e A) (e y)) ρ =
      bankEmbedding (e y) * referenceBranch (rowKraus A y) ρ *
        (bankEmbedding (e y)).conjTranspose := by
  have row : rowKraus (permuteOutput e A) (e y) = rowKraus A y := by
    ext u i
    simp [rowKraus, permuteOutput]
  rw [row, bankBranch_factor]

end RetainedBank

section Conjugation

/-- Entrywise conjugation changes phase signs without reversing the recursion schedule. -/
public def conjugate {I J : Type} (A : Matrix I J Complex) : Matrix I J Complex :=
  fun i j => star (A i j)

public lemma conjugate_mul {I J K : Type} [Fintype J]
    (A : Matrix I J Complex) (D : Matrix J K Complex) :
    conjugate (A * D) = conjugate A * conjugate D := by
  ext i k
  simp only [conjugate, Matrix.mul_apply, star_sum, star_mul']

public lemma conjugate_controlled {B T : Type} [DecidableEq B]
    (U : B → Matrix T T Complex) :
    conjugate (controlled U) = controlled (fun b => conjugate (U b)) := by
  ext x y
  by_cases h : x.1 = y.1
  · simp [conjugate, controlled, h]
  · simp [conjugate, controlled, h]

public lemma conjugate_leading {B T : Type} [DecidableEq T]
    (H : Matrix B B Complex) :
    conjugate (leading (T := T) H) = leading (T := T) (conjugate H) := by
  ext x y
  by_cases h : x.2 = y.2
  · simp [conjugate, leading, h]
  · simp [conjugate, leading, h]

/-- A symmetric Fourier matrix has adjoint equal to entrywise conjugation. -/
public lemma conjugate_symmetric_eq_adjoint {I : Type} (F : Matrix I I Complex)
    (symmetric : ∀ i j, F i j = F j i) :
    conjugate F = F.conjTranspose := by
  ext i j
  exact congrArg star (symmetric i j)

end Conjugation

end

end QuantumAlg.MeasurementInstrument
