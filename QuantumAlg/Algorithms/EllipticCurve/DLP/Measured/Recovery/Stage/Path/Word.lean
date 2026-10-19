/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback

/-!
# Fixed actual paths and their coherent exponent-word matrices

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open StoredRecursion
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {B : Type} [Fintype B] [DecidableEq B]

private def memoryBlock (operator : Matrix (Bool × B) (Bool × B) ℂ)
    (final input : Bool) : Matrix B B ℂ :=
  operator.submatrix (Prod.mk final) (Prod.mk input)

omit [DecidableEq B] in
private lemma memoryBlock_mul (left right : Matrix (Bool × B) (Bool × B) ℂ)
    (final input : Bool) :
    memoryBlock (left * right) final input =
      ∑ memory : Bool, memoryBlock left final memory * memoryBlock right memory input := by
  ext row column
  simp only [memoryBlock, Matrix.submatrix_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]

private def transfer (r remaining : Nat) (action : Nat → Bool → Matrix B B ℂ) :
    Matrix (Bool × B) (Bool × B) ℂ :=
  fun row column => ∑ emitted : Bool,
    (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) column.1 emitted row.1 : ℂ) *
      action remaining emitted row.2 column.2

omit [Fintype B] [DecidableEq B] in
private lemma memoryBlock_transfer (r remaining : Nat)
    (action : Nat → Bool → Matrix B B ℂ) (final input : Bool) :
    memoryBlock (transfer r remaining action) final input =
      ∑ emitted : Bool,
        (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted final : ℂ) •
          action remaining emitted := by
  ext row column
  simp only [memoryBlock, transfer, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

private def transferProduct (r : Nat) (action : Nat → Bool → Matrix B B ℂ) :
    Nat → Matrix (Bool × B) (Bool × B) ℂ
  | 0 => 1
  | remaining + 1 => transferProduct r action remaining * transfer r remaining action

private lemma sum_generated_entry (r remaining : Nat)
    (action : Nat → Bool → Matrix B B ℂ) (input final emitted : Bool)
    (x : Nat) (bounded : x < 2 ^ remaining) :
    OrderedBankWord.generatedWord r action (remaining + 1) input
        (if emitted then 2 ^ remaining + x else x) final =
      (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted false : ℂ) •
        (OrderedBankWord.generatedWord r action remaining false x final *
          action remaining emitted) +
      (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted true : ℂ) •
        (OrderedBankWord.generatedWord r action remaining true x final *
          action remaining emitted) := by
  cases emitted with
  | false =>
      have high : decide (2 ^ remaining ≤ x) = false := by
        simp only [Nat.not_le_of_gt bounded, decide_false]
      simp only [Bool.false_eq_true, ↓reduceIte, OrderedBankWord.generatedWord,
        high, Nat.mod_eq_of_lt bounded]
  | true =>
      have high : decide (2 ^ remaining ≤ 2 ^ remaining + x) = true := by
        simp only [Nat.le_add_right, decide_true]
      simp only [↓reduceIte, OrderedBankWord.generatedWord, high,
        Nat.add_mod_left, Nat.mod_eq_of_lt bounded]

omit [DecidableEq B] in
private lemma sum_add_smul_mul (indices : Finset Nat) (left right : ℂ)
    (first second : Nat → Matrix B B ℂ) (last : Matrix B B ℂ) :
    (∑ x ∈ indices, (left • (first x * last) + right • (second x * last))) =
      left • ((∑ x ∈ indices, first x) * last) +
        right • ((∑ x ∈ indices, second x) * last) := by
  rw [Finset.sum_add_distrib]
  simp only [← Finset.smul_sum, ← Matrix.sum_mul]

private lemma sum_generated_half (r remaining : Nat)
    (action : Nat → Bool → Matrix B B ℂ) (input final emitted : Bool) :
    (∑ x ∈ Finset.range (2 ^ remaining),
      OrderedBankWord.generatedWord r action (remaining + 1) input
        (if emitted then 2 ^ remaining + x else x) final) =
      (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted false : ℂ) •
        ((∑ x ∈ Finset.range (2 ^ remaining),
          OrderedBankWord.generatedWord r action remaining false x final) *
            action remaining emitted) +
      (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted true : ℂ) •
        ((∑ x ∈ Finset.range (2 ^ remaining),
          OrderedBankWord.generatedWord r action remaining true x final) *
            action remaining emitted) := by
  exact (Finset.sum_congr rfl fun x member =>
    sum_generated_entry r remaining action input final emitted x
      (Finset.mem_range.mp member)).trans
    (sum_add_smul_mul (Finset.range (2 ^ remaining))
      (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted false : ℂ)
      (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted true : ℂ)
      (fun x => OrderedBankWord.generatedWord r action remaining false x final)
      (fun x => OrderedBankWord.generatedWord r action remaining true x final)
      (action remaining emitted))

private lemma sum_generated_step (r remaining : Nat)
    (action : Nat → Bool → Matrix B B ℂ) (input final : Bool) :
    (∑ x ∈ Finset.range (2 ^ (remaining + 1)),
      OrderedBankWord.generatedWord r action (remaining + 1) input x final) =
      ∑ memory : Bool,
        (∑ x ∈ Finset.range (2 ^ remaining),
          OrderedBankWord.generatedWord r action remaining memory x final) *
        (∑ emitted : Bool,
          (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted memory : ℂ) •
            action remaining emitted) := by
  have doubled : 2 ^ (remaining + 1) = 2 ^ remaining + 2 ^ remaining := by
    rw [pow_succ]
    omega
  rw [doubled, Finset.sum_range_add]
  have low := sum_generated_half r remaining action input final false
  have high := sum_generated_half r remaining action input final true
  simp only [Bool.false_eq_true, ↓reduceIte] at low high
  rw [low, high]
  simp only [Fintype.sum_bool, Matrix.mul_add, Matrix.mul_smul]
  abel

private lemma transferProduct_word_sum_zero (r : Nat)
    (action : Nat → Bool → Matrix B B ℂ) (input final : Bool) :
    memoryBlock (transferProduct r action 0) final input =
      ∑ x ∈ Finset.range (2 ^ 0),
        OrderedBankWord.generatedWord r action 0 input x final := by
    ext row column
    by_cases sameMemory : final = input <;>
      simp [transferProduct, memoryBlock, Matrix.one_apply, Prod.mk.injEq,
        OrderedBankWord.generatedWord, generated, sameMemory]

private lemma transferProduct_word_sum (r remaining : Nat)
    (action : Nat → Bool → Matrix B B ℂ) (input final : Bool) :
    memoryBlock (transferProduct r action remaining) final input =
      ∑ x ∈ Finset.range (2 ^ remaining),
        OrderedBankWord.generatedWord r action remaining input x final := by
  induction remaining generalizing input final with
  | zero => exact transferProduct_word_sum_zero r action input final
  | succ remaining ih =>
      refine (memoryBlock_mul (transferProduct r action remaining)
        (transfer r remaining action) final input).trans ?_
      exact (Finset.sum_congr rfl fun memory _ =>
        congrArg₂ (fun first last : Matrix B B ℂ => first * last)
          (ih memory final) (memoryBlock_transfer r remaining action memory input)).trans
        (sum_generated_step r remaining action input final).symm

end

end PointCoordinates.StageWord.PathWord
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open StoredRecursion
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

def blockIndices {m : Nat} (second : Bool) : (remaining : Nat) → remaining ≤ m →
    List (Fin (2 * m))
  | 0, _ => []
  | remaining + 1, bounded =>
      blockIndex second
        ⟨remaining, Nat.lt_of_lt_of_le (Nat.lt_succ_self remaining) bounded⟩ ::
          blockIndices second remaining (Nat.le_trans (Nat.le_succ remaining) bounded)

private lemma blockIndices_length {m : Nat} (second : Bool) (remaining : Nat)
    (bounded : remaining ≤ m) : (blockIndices second remaining bounded).length = remaining := by
  induction remaining with
  | zero => rfl
  | succ remaining ih =>
      simp only [blockIndices, List.length_cons, ih]

private lemma blockIndices_get {m : Nat} (second : Bool) (remaining : Nat)
    (bounded : remaining ≤ m) (position : Nat) (member : position < remaining) :
    (blockIndices second remaining bounded)[position]'(by
      simpa only [blockIndices_length] using member) =
      blockIndex second ⟨remaining - position - 1, by omega⟩ := by
  induction remaining generalizing position with
  | zero => omega
  | succ remaining ih =>
      cases position with
      | zero =>
          simp only [blockIndices, List.getElem_cons_zero]
          apply congrArg (blockIndex second)
          apply Fin.ext
          change remaining = remaining + 1 - 0 - 1
          omega
      | succ position =>
          simpa only [blockIndices, List.getElem_cons_succ, Nat.succ_sub_succ_eq_sub] using
            ih (Nat.le_trans (Nat.le_succ remaining) bounded) position (by omega)

lemma blockIndices_original_order {m : Nat} (second : Bool) :
    blockIndices second m le_rfl =
      (List.finRange m).map (fun position => Fin.cast (Nat.two_mul m).symm
        (if second then Fin.natAdd m position else Fin.castAdd m position)) := by
  calc
    _ = (List.finRange m).map (fun position => blockIndex second (Fin.rev position)) := by
      apply List.ext_getElem
      · simp only [blockIndices_length, List.length_map, List.length_finRange]
      · intro position leftBound rightBound
        have member : position < m := by simpa only [blockIndices_length] using leftBound
        rw [blockIndices_get second m le_rfl position member]
        simp only [List.getElem_map, List.getElem_finRange]
        apply congrArg (blockIndex second)
        apply Fin.ext
        simp only [Fin.val_rev, Fin.val_cast]
        omega
    _ = _ := by
      apply congrArg (fun operation => (List.finRange m).map operation)
      funext position
      exact blockIndex_original_order second position

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

def pathProduct
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension) :
    List (Fin (2 * m)) →
      Matrix ((Interface p.size m).register.prod Reference).Index
        ((Interface p.size m).register.prod Reference).Index ℂ
  | [] => 1
  | index :: tail => pathProduct (environment := environment) E r points Reference division
    intermediate outcomes tail *
      stageMatrix (environment := environment) E r points index Reference (intermediate index)
        (outcomes index) (division index)

private lemma freshBlock_one (width m : Nat) (Reference : Register) :
    freshBlock (width := width) (m := m) Reference 1 = 1 := by
  have injective : Function.Injective
      (fun value : Bool × Bank width m Reference =>
        (coordinates width m Reference).symm (0, (bitBasis value.1, value.2))) := by
    intro left right same
    have labels := (coordinates width m Reference).symm.injective same
    have spectators := (Prod.mk.inj labels).2
    exact Prod.ext (bitBasis.injective (Prod.mk.inj spectators).1) (Prod.mk.inj spectators).2
  ext row column
  simp only [freshBlock, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases same : row = column
  · subst column
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (fun value => same (injective value)), if_neg same]

private lemma fresh_path_transfer {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (second : Bool)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (remaining : Nat) (bounded : remaining ≤ m) :
    freshBlock Reference (pathProduct (environment := environment) E r points Reference division
      intermediate outcomes
        (blockIndices second remaining bounded)) =
      transferProduct r (blockAction (environment := environment)
        E points Reference second division intermediate outcomes)
        remaining := by
  induction remaining with
  | zero => exact freshBlock_one p.size m Reference
  | succ remaining ih =>
      simp only [blockIndices, pathProduct, transferProduct]
      rw [freshBlock_tail_stage, ih]
      congr 1
      rw [freshBlock_stage]
      ext row column
      simp only [transfer, blockIndex_remaining]
      apply Finset.sum_congr rfl
      intro emitted _
      have actual := blockAction_in_range (environment := environment)
        E points Reference second division intermediate
        outcomes ⟨remaining, Nat.lt_of_lt_of_le (Nat.lt_succ_self remaining) bounded⟩ emitted
      exact congrArg
        (fun matrix : Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ =>
          (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) column.1 emitted row.1 : ℂ) *
            matrix row.2 column.2) actual.symm

lemma actual_path_word_sum {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (second : Bool)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension) (input final : Bool) :
    (freshBlock Reference (pathProduct (environment := environment) E r points Reference division
      intermediate outcomes
        (blockIndices second m le_rfl))).submatrix (Prod.mk final) (Prod.mk input) =
      ∑ x ∈ Finset.range (2 ^ m),
        OrderedBankWord.generatedWord r
          (blockAction (environment := environment)
            E points Reference second division intermediate outcomes) m input x final :=
  (congrArg (fun matrix : Matrix (Bool × Bank p.size m Reference)
        (Bool × Bank p.size m Reference) ℂ =>
      matrix.submatrix (Prod.mk final) (Prod.mk input))
    (fresh_path_transfer E r points Reference second division intermediate outcomes m
      le_rfl)).trans
      (transferProduct_word_sum r m _ input final)

lemma actual_path_initialized_sum {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (second : Bool)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) (final : Bool) :
    (freshBlock Reference (pathProduct (environment := environment) E r points Reference division
      intermediate outcomes
        (blockIndices second m le_rfl))).submatrix (Prod.mk final) (Prod.mk false) =
      ∑ x ∈ Finset.range (2 ^ m),
        ((if x < r ∧ final = false then invSqrt r else 0 : ℝ) : ℂ) •
          OrderedBankWord.word
            (blockAction (environment := environment)
              E points Reference second division intermediate outcomes) m x := by
  rw [actual_path_word_sum]
  apply Finset.sum_congr rfl
  intro x member
  exact fixed_path_initialized_word E r points Reference second division intermediate outcomes
    x positive fits (Finset.mem_range.mp member) final

end

end PointCoordinates.StageWord.PathWord
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
