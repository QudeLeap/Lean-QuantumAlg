/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import all QuantumAlg.Primitives.QFT.Semiclassical.Mathematics
import all QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases

/-!
# Ordered coherent-partner Kraus factorization

Source-only candidate: no Lean acceptance is claimed. The old branch is derived
from the actual ordered controlled-operator product, all-bank Hadamards, and the
existing coherent Fourier row. Its factors keep their chronological order even
when the partner operators do not commute. Intermediate phases account for the
previously measured physical output bits. There is no branch-state or Fourier
identity certificate among the theorem premises.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

open QuantumAlg.MeasurementInstrument NormalizedVector
open scoped BigOperators Kronecker

variable {S : Register}

/-- The first chronological factor is rightmost; no factors are permuted. -/
def chronologicalProduct {P : Type} [Fintype P] [DecidableEq P] :
    List (Matrix P P ℂ) → Matrix P P ℂ
  | [] => 1
  | head :: tail => chronologicalProduct tail * head

/-- One coherent control selects identity or the given partner operator. -/
def selected (operator : HilbertOperator S) (bit : Fin 2) : HilbertOperator S :=
  if bit = 0 then 1 else operator

/-- Actual partner word for a computational-basis control-bank input. -/
def orderedWord (n : Nat) (operators : Fin n → HilbertOperator S) (input : Bits n) :
    HilbertOperator S :=
  chronologicalProduct (List.ofFn (fun index =>
    selected (operators index) (tupleCoordinates n input index)))

private lemma orderedWord_zero (operators : Fin 0 → HilbertOperator S)
    (input : Bits 0) : orderedWord 0 operators input = 1 := by
  simp [orderedWord, chronologicalProduct]

private lemma orderedWord_succ (n : Nat) (operators : Fin (n + 1) → HilbertOperator S)
    (head : Fin 2) (tail : Bits n) :
    orderedWord (n + 1) operators (head, tail) =
      orderedWord n (fun index => operators index.succ) tail * selected (operators 0) head :=
    by
  simp only [orderedWord, List.ofFn_succ, chronologicalProduct,
    tupleCoordinates_head, tupleCoordinates_tail]

private lemma controlled_one {B P : Type} [DecidableEq B] [DecidableEq P] :
    controlled (fun _ : B => (1 : Matrix P P ℂ)) = 1 := by
  ext row column
  simp only [controlled, Matrix.one_apply]
  by_cases first : row.1 = column.1 <;>
    by_cases second : row.2 = column.2 <;> simp [first, second, Prod.ext_iff]

private lemma controlled_mul {B P : Type} [Fintype B] [Fintype P]
    [DecidableEq B] (left right : B → Matrix P P ℂ) :
    controlled left * controlled right = controlled (fun bit => left bit * right bit) :=
    by
  classical
  ext row column
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, controlled]
  by_cases same : row.1 = column.1
  · rcases row with ⟨head, row⟩
    rcases column with ⟨other, column⟩
    dsimp at same
    subst other
    simp [ite_mul, mul_ite]
  · simp [same, ite_mul, mul_ite]

private lemma chronological_controlled {B P : Type} [Fintype B] [Fintype P]
    [DecidableEq B] [DecidableEq P] (choices : List (B → Matrix P P ℂ)) :
    chronologicalProduct (choices.map controlled) =
      controlled (fun bit => chronologicalProduct (choices.map (fun choice => choice bit))) :=
    by
  induction choices with
  | nil => simp only [List.map_nil, chronologicalProduct, controlled_one]
  | cons head tail ih =>
      simp only [List.map_cons, chronologicalProduct, ih, controlled_mul]

/-- The real chronological product of one addressed controlled operator per input bit. -/
def orderedControls (n : Nat) (operators : Fin n → HilbertOperator S) :
    Matrix (Bits n × S.Index) (Bits n × S.Index) ℂ :=
  chronologicalProduct (List.ofFn (fun index =>
    controlled (fun input : Bits n =>
      selected (operators index) (tupleCoordinates n input index))))

/-- Every basis-bank block keeps the full, possibly noncommuting, partner word. -/
lemma qftPartner_orderedControls_blocks (n : Nat)
    (operators : Fin n → HilbertOperator S) :
    orderedControls n operators = controlled (orderedWord n operators) := by
  have product := chronological_controlled (List.ofFn (fun index =>
    fun input : Bits n => selected (operators index) (tupleCoordinates n input index)))
  change chronologicalProduct (List.ofFn (fun index =>
    controlled (fun input : Bits n =>
      selected (operators index) (tupleCoordinates n input index)))) =
    controlled (fun input : Bits n => chronologicalProduct (List.ofFn (fun index =>
      selected (operators index) (tupleCoordinates n input index))))
  simpa only [List.map_ofFn, Function.comp_def] using product

/-- All-bank Hadamards, with identity feedback in the actual leading-wire recursion. -/
def bankHadamard (n : Nat) : Matrix (Bits n) (Bits n) ℂ :=
  coherent Gate.HOp (fun _ _ => 1) n

def zeroBits : (n : Nat) → Bits n
  | 0 => ()
  | n + 1 => (0, zeroBits n)

private lemma bankHadamard_zero_column (n : Nat) (input : Bits n) :
    bankHadamard n input (zeroBits n) = invSqrt2 ^ n := by
  induction n with
  | zero => cases input; rfl
  | succ n ih =>
      rcases input with ⟨head, tail⟩
      change coherentStage Gate.HOp (fun _ : Fin 2 => 1) (bankHadamard n)
        (head, tail) (0, zeroBits n) = _
      have entry := phaseStage_entry Gate.HOp (fun _ : Fin 2 => fun _ : Bits n => (1 : ℂ))
        (bankHadamard n) head 0 tail (zeroBits n)
      simp only [Matrix.diagonal_one, mul_one] at entry
      rw [entry, ih, pow_succ invSqrt2 n]
      fin_cases head <;> simp [Gate.HOp, UnitaryOperator.coe_ofMatrix]

/-- Literal preparation: zero bank, all Hadamards, then the ordered controlled partners. -/
def preparation (n : Nat) (operators : Fin n → HilbertOperator S) :
    Matrix (Bits n × S.Index) S.Index ℂ :=
  orderedControls n operators *
    ((bankHadamard n) ⊗ₖ (1 : HilbertOperator S)) * bankEmbedding (zeroBits n)

/-- Exact prepared columns retain every coherent partner input and exact amplitude. -/
lemma qftPartner_preparation_entry (n : Nat) (operators : Fin n → HilbertOperator S)
    (input : Bits n) (row column : S.Index) :
    preparation n operators (input, row) column =
      invSqrt2 ^ n * orderedWord n operators input row column := by
  have entry (blocks : Bits n → Matrix S.Index S.Index ℂ)
      (hadamards : Matrix (Bits n) (Bits n) ℂ) :
      ((controlled blocks * (hadamards ⊗ₖ (1 : Matrix S.Index S.Index ℂ)) *
        bankEmbedding (R := S.Index) (zeroBits n)) :
          Matrix (Bits n × S.Index) S.Index ℂ) (input, row) column =
          hadamards input (zeroBits n) * blocks input row column := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, controlled, bankEmbedding,
      Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_comm]
  unfold preparation
  rw [qftPartner_orderedControls_blocks]
  exact (entry (orderedWord n operators) (bankHadamard n)).trans
    (congrArg (fun coefficient : ℂ => coefficient * orderedWord n operators input row column)
      (bankHadamard_zero_column n input))

/-- Generalized contraction permits the native phases accumulated from earlier outcomes. -/
public def contraction (inverse : Bool) (n : Nat) (operators : Fin n → HilbertOperator S)
    (phases : Fin n → ℂ) (output : Bits n) : HilbertOperator S :=
  ∑ input : Bits n,
    (fourierRows inverse n output input * invSqrt2 ^ n * phaseBasis n phases input) •
      orderedWord n operators input

/-- The measured old bank is removed only after deriving the actual Fourier-row contraction. -/
public def oldKraus (inverse : Bool) (n : Nat) (operators : Fin n → HilbertOperator S)
    (output : Bits n) : HilbertOperator S :=
  withReference (rowKraus (fourierRows inverse n) output) * preparation n operators

/-- No operator is supplied as an external source certificate. -/
public lemma qftPartner_oldKraus_contraction (inverse : Bool) (n : Nat)
    (operators : Fin n → HilbertOperator S) (output : Bits n) :
    oldKraus inverse n operators output =
      contraction inverse n operators (fun _ => 1) output := by
  ext row column
  simp only [oldKraus, Matrix.mul_apply, Fintype.sum_prod_type, withReference, rowKraus,
    mul_ite, mul_one, mul_zero]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [contraction, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    phaseBasis_one, mul_one]
  apply Finset.sum_congr rfl
  intro input _
  rw [qftPartner_preparation_entry]
  ring

/-- Exact H/control/phase/H branch on the persistent partner. -/
public def halfSum (operator : HilbertOperator S) (phase : ℂ) (outcome : Fin 2) :
    HilbertOperator S :=
  (2 : ℂ)⁻¹ • (1 + ((-1 : ℂ) ^ outcome.val * phase) • operator)

private lemma contraction_zero (inverse : Bool) (operators : Fin 0 → HilbertOperator S)
    (phases : Fin 0 → ℂ) (output : Bits 0) :
    contraction inverse 0 operators phases output = 1 := by
  cases output
  let : Unique (Bits 0) := inferInstanceAs (Unique Unit)
  simp [contraction, fourierRows, coherent, orderedWord_zero, phaseBasis_zero]

private lemma fourierRows_succ (inverse : Bool) (n : Nat) (head bit : Fin 2)
    (output input : Bits n) :
    fourierRows inverse (n + 1) (head, output) (bit, input) =
      fourierRows inverse n output input *
        phaseBasis n (feedbackPhases inverse n head) input * Gate.HOp head bit := by
  exact phaseStage_entry Gate.HOp (fun branch => phaseBasis n (feedbackPhases inverse n branch))
    (fourierRows inverse n) head bit output input

private lemma sum_smul_right (coefficient : ℂ) (operator : HilbertOperator S)
    {T : Type} [Fintype T] (weights : T → ℂ) (words : T → HilbertOperator S) :
    (∑ input : T, (coefficient * weights input) • (words input * operator)) =
      (∑ input : T, weights input • words input) * (coefficient • operator) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro input _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

private lemma hadamard_halfSum (operator : HilbertOperator S) (phase : ℂ)
    (outcome : Fin 2) :
    (Gate.HOp outcome 0 * invSqrt2) • (1 : HilbertOperator S) +
      (Gate.HOp outcome 1 * invSqrt2 * phase) • operator =
        halfSum operator phase outcome := by
  fin_cases outcome <;>
    simp [Gate.HOp, UnitaryOperator.coe_ofMatrix, halfSum, smul_add,
      invSqrt2_mul_self, smul_smul]

/-- This recurrence preserves the operator order; it does not commute any partner gates. -/
public lemma qftPartner_contraction_succ (inverse : Bool) (n : Nat)
    (operators : Fin (n + 1) → HilbertOperator S) (phases : Fin (n + 1) → ℂ)
    (head : Fin 2) (tail : Bits n) :
    contraction inverse (n + 1) operators phases (head, tail) =
      contraction inverse n (fun index => operators index.succ)
        (fun index => phases index.succ * feedbackPhases inverse n head index) tail *
          halfSum (operators 0) (phases 0) head := by
  let weights (input : Bits n) : ℂ :=
    fourierRows inverse n tail input * invSqrt2 ^ n *
      phaseBasis n (fun index => phases index.succ * feedbackPhases inverse n head index) input
  let words (input : Bits n) : HilbertOperator S :=
    orderedWord n (fun index => operators index.succ) input
  have coefficient (bit : Fin 2) (input : Bits n) :
      fourierRows inverse (n + 1) (head, tail) (bit, input) * invSqrt2 ^ (n + 1) *
          phaseBasis (n + 1) phases (bit, input) =
        (Gate.HOp head bit * invSqrt2 * (if bit = 0 then 1 else phases 0)) * weights input :=
      by
    rw [fourierRows_succ, phaseBasis_succ, pow_succ invSqrt2 n]
    simp only [weights, phaseBasis_mul]
    ring
  have split : contraction inverse (n + 1) operators phases (head, tail) =
      ∑ bit : Fin 2, ∑ input : Bits n,
        (fourierRows inverse (n + 1) (head, tail) (bit, input) * invSqrt2 ^ (n + 1) *
          phaseBasis (n + 1) phases (bit, input)) •
            orderedWord (n + 1) operators (bit, input) := by
    change (∑ input : Fin 2 × Bits n,
      (fourierRows inverse (n + 1) (head, tail) input * invSqrt2 ^ (n + 1) *
        phaseBasis (n + 1) phases input) • orderedWord (n + 1) operators input) = _
    exact Fintype.sum_prod_type _
  rw [split, Fin.sum_univ_two]
  simp_rw [coefficient, orderedWord_succ]
  have nonzero : (1 : Fin 2) ≠ 0 := by decide
  simp only [selected, nonzero, ↓reduceIte, mul_one]
  have firstTerm :
      (∑ input : Bits n, ((Gate.HOp head 0 * invSqrt2) * weights input) • words input) =
        (∑ input : Bits n, weights input • words input) *
          ((Gate.HOp head 0 * invSqrt2) • (1 : HilbertOperator S)) := by
    simpa only [mul_one] using
      sum_smul_right (Gate.HOp head 0 * invSqrt2) (1 : HilbertOperator S) weights words
  change (∑ input : Bits n,
      ((Gate.HOp head 0 * invSqrt2) * weights input) • words input) +
    (∑ input : Bits n,
      ((Gate.HOp head 1 * invSqrt2 * phases 0) * weights input) •
        (words input * operators 0)) = _
  rw [firstTerm, sum_smul_right, ← mul_add, hadamard_halfSum]
  rfl

/-- Measured earlier bits update each later phase without altering the partner state. -/
public def updatedPhases (inverse : Bool) (n : Nat) (phases : Fin (n + 1) → ℂ)
    (head : Fin 2) : Fin n → ℂ :=
  fun index => phases index.succ * feedbackPhases inverse n head index

/-- Recycled-control half-sum product; each later factor acts on the previous posterior. -/
public def recycledKraus (inverse : Bool) : (n : Nat) →
    (Fin n → HilbertOperator S) → (Fin n → ℂ) → Bits n → HilbertOperator S
  | 0, _, _, _ => 1
  | n + 1, operators, phases, output =>
      recycledKraus inverse n (fun index => operators index.succ)
        (updatedPhases inverse n phases output.1) output.2 *
          halfSum (operators 0) (phases 0) output.1

/-- Arbitrary partner operators admit exact ordered branch factorization, including phase. -/
public lemma qftPartner_contraction_eq_recycled (inverse : Bool) :
    ∀ (n : Nat) (operators : Fin n → HilbertOperator S) (phases : Fin n → ℂ)
      (output : Bits n),
    contraction inverse n operators phases output =
      recycledKraus inverse n operators phases output := by
  intro n
  induction n with
  | zero => intro operators phases output; exact contraction_zero inverse operators phases output
  | succ n ih =>
      intro operators phases output
      rcases output with ⟨head, tail⟩
      rw [qftPartner_contraction_succ, ih]
      rfl

/-- The actual old all-bank execution and one recycled control induce the same partner Kraus. -/
public lemma qftPartner_oldKraus_eq_recycled (inverse : Bool) (n : Nat)
    (operators : Fin n → UnitaryOperator S) (output : Bits n) :
    oldKraus inverse n (fun index => (operators index : HilbertOperator S)) output =
      recycledKraus inverse n (fun index => (operators index : HilbertOperator S))
        (fun _ => 1) output := by
  rw [qftPartner_oldKraus_contraction, qftPartner_contraction_eq_recycled]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
