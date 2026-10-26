/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Core.Execution.Store.MarginalSum
import all QuantumAlg.Util.Matrix.SupportedBlock

/-!
# Ordered original bank words and actual complete-Store recursion

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace OrderedBankWord

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {Bank : Type} [Fintype Bank] [DecidableEq Bank]

def word (action : Nat → Bool → Matrix Bank Bank ℂ) : Nat → Nat → Matrix Bank Bank ℂ
  | 0, _ => 1
  | remaining + 1, x =>
      word action remaining (x % 2 ^ remaining) *
        action remaining (decide (2 ^ remaining ≤ x))

def generatedWord (r : Nat) (action : Nat → Bool → Matrix Bank Bank ℂ) :
    Nat → Bool → Nat → Bool → Matrix Bank Bank ℂ
  | 0, input, x, final => (generated r 0 input x final : ℂ) • (1 : Matrix Bank Bank ℂ)
  | remaining + 1, input, x, final =>
      let half := 2 ^ remaining
      let cut := r % (2 * half)
      let emitted := decide (half ≤ x)
      (table half cut input emitted false : ℂ) •
          (generatedWord r action remaining false (x % half) final * action remaining emitted) +
        (table half cut input emitted true : ℂ) •
          (generatedWord r action remaining true (x % half) final * action remaining emitted)

lemma generatedWord_eq_generated (r remaining : Nat)
    (action : Nat → Bool → Matrix Bank Bank ℂ) (input : Bool) (x : Nat) (final : Bool) :
    generatedWord r action remaining input x final =
      (generated r remaining input x final : ℂ) • word action remaining x := by
  induction remaining generalizing input x final with
  | zero => rfl
  | succ remaining ih =>
      simp only [generatedWord, generated, word, ih, Matrix.smul_mul, smul_smul,
        ← add_smul, Complex.ofReal_add, Complex.ofReal_mul]

lemma generatedWord_eq_model (r remaining : Nat)
    (action : Nat → Bool → Matrix Bank Bank ℂ) (input : Bool) (x : Nat) (final : Bool)
    (bound : x < 2 ^ remaining) :
    generatedWord r action remaining input x final =
      (model (2 ^ remaining) (r % 2 ^ remaining) input x final : ℂ) •
        word action remaining x := by
  rw [generatedWord_eq_generated,
    generated_eq_model r remaining input x final bound]

lemma initialized_word (r remaining x : Nat) (positive : 0 < r)
    (fits : r ≤ 2 ^ remaining) (bound : x < 2 ^ remaining)
    (action : Nat → Bool → Matrix Bank Bank ℂ) (final : Bool) :
    generatedWord r action remaining false x final =
      ((if x < r ∧ final = false then invSqrt r else 0 : ℝ) : ℂ) •
        word action remaining x := by
  rw [generatedWord_eq_generated,
    initialized_amplitude r remaining x positive fits bound final]

lemma initialized_memory_zero_word (r remaining x : Nat) (positive : 0 < r)
    (fits : r ≤ 2 ^ remaining) (bound : x < 2 ^ remaining)
    (action : Nat → Bool → Matrix Bank Bank ℂ) :
    generatedWord r action remaining false x true = 0 := by
  rw [generatedWord_eq_generated,
    initialized_memory_zero r remaining x positive fits bound,
    Complex.ofReal_zero, zero_smul]

def exponentPair (first second : Nat → Bool → Matrix Bank Bank ℂ)
    (remaining firstWord secondWord : Nat) : Matrix Bank Bank ℂ :=
  word second remaining secondWord * word first remaining firstWord

end

end OrderedBankWord
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

private def bitBasis : Bool ≃ Fin 2 where
  toFun := PreparationRows.bit
  invFun value := decide (value = 1)
  left_inv := by intro value; cases value <;> simp [PreparationRows.bit]
  right_inv := by intro value; fin_cases value <;> simp [PreparationRows.bit]

private lemma sum_control_memory {B : Type} [Fintype B]
    (control memory : Fin 2) (f : Fin 2 → Fin 2 → B → ℂ) :
    (∑ index : Fin 2 × (Fin 2 × B),
      if control = index.1 ∧ memory = index.2.1 then f index.1 index.2.1 index.2.2 else 0) =
      ∑ bank : B, f control memory bank := by
  simp only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Fintype.sum_ite_eq]

private lemma sum_memory_bank {B : Type} [Fintype B] [DecidableEq B]
    (memory : Fin 2) (bank : B) (f : Fin 2 → Fin 2 → B → ℂ) :
    (∑ index : Fin 2 × (Fin 2 × B),
      if memory = index.2.1 ∧ bank = index.2.2 then f index.1 index.2.1 index.2.2 else 0) =
      ∑ control : Fin 2, f control memory bank := by
  simp only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Fintype.sum_ite_eq]

private lemma point_preparation_mul_columns {Source B : Type}
    [Fintype Source] [Finite B] [DecidableEq B]
    (basis : Source ≃ Fin 2 × (Fin 2 × B)) (point prepared : Matrix Source Source ℂ)
    (control memory input : Fin 2) (rowBank columnBank : B) (coefficient : ℂ) (bankEntry : B → ℂ)
    (pointRows : ∀ middle,
      point (basis.symm (control, (memory, rowBank))) (basis.symm middle) =
        if control = middle.1 ∧ memory = middle.2.1 then bankEntry middle.2.2 else 0)
    (preparedRows : ∀ bank,
      prepared (basis.symm (control, (memory, bank)))
          (basis.symm (0, (input, columnBank))) =
        coefficient * (if bank = columnBank then 1 else 0)) :
    (point * prepared) (basis.symm (control, (memory, rowBank)))
        (basis.symm (0, (input, columnBank))) = coefficient * bankEntry columnBank := by
  let : Fintype B := Fintype.ofFinite B
  rw [Matrix.mul_apply, ← basis.symm.sum_comp]
  simp only [pointRows, ite_mul, zero_mul]
  rw [sum_control_memory (B := B) control memory
    (fun current next bank => bankEntry bank *
      prepared (basis.symm (current, (next, bank))) (basis.symm (0, (input, columnBank))))]
  simp only [preparedRows, mul_ite, mul_zero, mul_one]
  rw [Fintype.sum_ite_eq']
  exact mul_comm _ _

private lemma point_preparation_columns {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (index : Fin (2 * m)) (Reference : Register) (input emitted next : Bool)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Interface p.size m)) (rowBank columnBank : Bank p.size m Reference) :
    (pointMatrix (environment := environment) E (points index) m Reference divisionStore stored *
      preparationMatrix (environment := environment) p.size m r index Reference)
        ((coordinates p.size m Reference).symm (bitBasis emitted, (bitBasis next, rowBank)))
        ((coordinates p.size m Reference).symm (0, (bitBasis input, columnBank))) =
      (table (2 ^ Recovery.Layout.remaining m index)
        (r % (2 * 2 ^ Recovery.Layout.remaining m index)) input emitted next : ℂ) *
          bankBlock (environment := environment) E (points index) m Reference divisionStore stored
            (bitBasis emitted)
            rowBank columnBank := by
  exact point_preparation_mul_columns (coordinates p.size m Reference)
    (pointMatrix (environment := environment) E (points index) m Reference divisionStore stored)
    (preparationMatrix (environment := environment) p.size m r index Reference)
    (bitBasis emitted) (bitBasis next) (bitBasis input) rowBank columnBank
    (table (2 ^ Recovery.Layout.remaining m index)
      (r % (2 * 2 ^ Recovery.Layout.remaining m index)) input emitted next)
    (fun bank => bankBlock (environment := environment) E (points index) m Reference divisionStore
      stored
      (bitBasis emitted) rowBank bank)
    (fun middle => pointMatrix_entry E (points index) m Reference divisionStore stored
      (bitBasis emitted) middle.1 (bitBasis next) middle.2.1 rowBank middle.2.2)
    (fun bank => PreparationRows.preparationMatrix_columns (environment := environment) p.size m r
      index Reference
      input emitted next bank columnBank)


private lemma readout_feedback_entry (width m : Nat) (Reference : Register)
    (current : Fin (2 * m)) (stored : Store (Interface width m))
    (outcome : Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension)
    (columnControl rowMemory columnMemory : Fin 2)
    (rowBank columnBank : Bank width m Reference) :
    (readoutMatrix (environment := environment) width m Reference outcome *
      feedbackMatrix (environment := environment) width m Reference current stored
        (Recovery.Layout.order m))
        ((coordinates width m Reference).symm (0, (rowMemory, rowBank)))
        ((coordinates width m Reference).symm (columnControl, (columnMemory, columnBank))) =
      if rowMemory = columnMemory ∧ rowBank = columnBank then
        Gate.HOp (ReadoutRows.outcomeBit width m outcome) columnControl *
          FeedbackRows.feedbackPhase width m current stored columnControl (Recovery.Layout.order m)
      else 0 := by
  rw [FeedbackRows.readout_feedback_entry, ReadoutRows.readoutMatrix_entry]
  have actualControl : FeedbackRows.controlBit width m
      (((coordinates width m Reference).symm
        (columnControl, (columnMemory, columnBank))).1) = columnControl := by
    apply Fin.ext
    exact coordinates_control_value width m Reference columnControl columnMemory columnBank
  rw [actualControl]
  by_cases spectators : rowMemory = columnMemory ∧ rowBank = columnBank
  · rw [if_pos ⟨rfl, spectators⟩, if_pos spectators]
  · rw [if_neg (fun same => spectators same.2), zero_mul, if_neg spectators]

def action {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m)) (Reference : Register)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Interface p.size m))
    (outcome : Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension) (emitted : Bool) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  (Gate.HOp (ReadoutRows.outcomeBit p.size m outcome) (bitBasis emitted) *
    FeedbackRows.feedbackPhase p.size m index stored (bitBasis emitted) (Recovery.Layout.order m)) •
      bankBlock (environment := environment) E (points index) m Reference divisionStore stored
        (bitBasis emitted)

private lemma observed_prepared_mul_columns {Source B : Type}
    [Fintype Source] [Finite B] [DecidableEq B]
    (basis : Source ≃ Fin 2 × (Fin 2 × B)) (observed prepared : Matrix Source Source ℂ)
    (input next : Fin 2) (rowBank columnBank : B)
    (observedFactor : Fin 2 → ℂ) (coefficient bankEntry : Bool → ℂ)
    (observedRows : ∀ middle,
      observed (basis.symm (0, (next, rowBank))) (basis.symm middle) =
        if next = middle.2.1 ∧ rowBank = middle.2.2 then observedFactor middle.1 else 0)
    (preparedRows : ∀ emitted,
      prepared (basis.symm (bitBasis emitted, (next, rowBank)))
          (basis.symm (0, (input, columnBank))) = coefficient emitted * bankEntry emitted) :
    (observed * prepared) (basis.symm (0, (next, rowBank)))
        (basis.symm (0, (input, columnBank))) =
      ∑ emitted : Bool, coefficient emitted *
        (observedFactor (bitBasis emitted) * bankEntry emitted) := by
  let : Fintype B := Fintype.ofFinite B
  rw [Matrix.mul_apply, ← basis.symm.sum_comp]
  simp only [observedRows, ite_mul, zero_mul]
  rw [sum_memory_bank (B := B) next rowBank
    (fun control memory bank => observedFactor control *
      prepared (basis.symm (control, (memory, bank))) (basis.symm (0, (input, columnBank)))),
    ← bitBasis.sum_comp]
  apply Finset.sum_congr rfl
  intro emitted _
  rw [preparedRows]
  exact mul_left_comm _ _ _

lemma stageMatrix_fresh_columns {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (Reference : Register) (input next : Bool)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Interface p.size m))
    (outcome : Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (rowBank columnBank : Bank p.size m Reference) :
    stageMatrix (environment := environment) E r points index Reference stored outcome divisionStore
        ((coordinates p.size m Reference).symm (0, (bitBasis next, rowBank)))
        ((coordinates p.size m Reference).symm (0, (bitBasis input, columnBank))) =
      ∑ emitted : Bool,
        (table (2 ^ Recovery.Layout.remaining m index)
          (r % (2 * 2 ^ Recovery.Layout.remaining m index)) input emitted next : ℂ) *
            action (environment := environment) E points index Reference divisionStore stored
              outcome emitted
              rowBank columnBank := by
  have grouped := Matrix.mul_assoc
    (readoutMatrix (environment := environment) p.size m Reference outcome *
      feedbackMatrix (environment := environment) p.size m Reference index stored
        (Recovery.Layout.order m))
    (pointMatrix (environment := environment) E (points index) m Reference divisionStore stored)
    (preparationMatrix (environment := environment) p.size m r index Reference)
  refine (congrFun (congrFun grouped _) _).trans ?_
  exact observed_prepared_mul_columns (coordinates p.size m Reference)
    (readoutMatrix (environment := environment) p.size m Reference outcome *
      feedbackMatrix (environment := environment) p.size m Reference index stored
        (Recovery.Layout.order m))
    (pointMatrix (environment := environment) E (points index) m Reference divisionStore stored *
      preparationMatrix (environment := environment) p.size m r index Reference)
    (bitBasis input) (bitBasis next) rowBank columnBank
    (fun control => Gate.HOp (ReadoutRows.outcomeBit p.size m outcome) control *
      FeedbackRows.feedbackPhase p.size m index stored control (Recovery.Layout.order m))
    (fun emitted => (table (2 ^ Recovery.Layout.remaining m index)
      (r % (2 * 2 ^ Recovery.Layout.remaining m index)) input emitted next : ℂ))
    (fun emitted => bankBlock (environment := environment) E (points index) m Reference
      divisionStore stored
      (bitBasis emitted) rowBank columnBank)
    (fun middle => readout_feedback_entry p.size m Reference index stored outcome middle.1
      (bitBasis next) middle.2.1 rowBank middle.2.2)
    (fun emitted => point_preparation_columns E r points index Reference input emitted next
      divisionStore stored rowBank columnBank)


def blockIndex {m : Nat} (second : Bool) (remaining : Fin m) : Fin (2 * m) :=
  Fin.cast (Nat.two_mul m).symm
    (if second then Fin.natAdd m (Fin.rev remaining) else Fin.castAdd m (Fin.rev remaining))

lemma blockIndex_original_order {m : Nat} (second : Bool) (position : Fin m) :
    blockIndex second (Fin.rev position) = Fin.cast (Nat.two_mul m).symm
      (if second then Fin.natAdd m position else Fin.castAdd m position) := by
  simp only [blockIndex, Fin.rev_rev]

lemma blockIndex_remaining {m : Nat} (second : Bool) (remaining : Fin m) :
    Recovery.Layout.remaining m (blockIndex second remaining) = remaining.val := by
  cases second with
  | false =>
      simp only [Recovery.Layout.remaining, blockIndex, Bool.false_eq_true, ↓reduceIte,
        Fin.val_cast, Fin.val_castAdd]
      rw [Nat.mod_eq_of_lt (Fin.rev remaining).isLt, Fin.val_rev]
      omega
  | true =>
      simp only [Recovery.Layout.remaining, blockIndex, ↓reduceIte, Fin.val_cast, Fin.val_natAdd]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (Fin.rev remaining).isLt, Fin.val_rev]
      omega

def blockAction {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (points : Fin (2 * m) → AffinePoint E) (Reference : Register) (second : Bool)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension) :
    Nat → Bool → Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  fun remaining emitted => if bounded : remaining < m then
    let index := blockIndex second ⟨remaining, bounded⟩
    action (environment := environment) E points index Reference (division index) (intermediate
      index) (outcomes index) emitted
  else 1

lemma blockAction_in_range {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register) (second : Bool)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension) (remaining : Fin m) (emitted : Bool) :
    blockAction (environment := environment)
      E points Reference second division intermediate outcomes remaining.val emitted =
      action (environment := environment) E points (blockIndex second remaining) Reference
        (division (blockIndex second remaining)) (intermediate (blockIndex second remaining))
        (outcomes (blockIndex second remaining)) emitted :=
  by simp only [blockAction, dif_pos remaining.isLt]

lemma fixed_path_initialized_word {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (second : Bool)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (x : Nat) (positive : 0 < r) (fits : r ≤ 2 ^ m) (bound : x < 2 ^ m) (final : Bool) :
    OrderedBankWord.generatedWord r
        (blockAction (environment := environment)
          E points Reference second division intermediate outcomes) m false x final =
      ((if x < r ∧ final = false then invSqrt r else 0 : ℝ) : ℂ) •
        OrderedBankWord.word
          (blockAction (environment := environment)
            E points Reference second division intermediate outcomes) m x :=
  OrderedBankWord.initialized_word r m x positive fits bound _ final

end

end PointCoordinates.StageWord
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.StoredRecursion

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

private lemma filter_store_matrix {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (predicate : Store ctx → Prop) :
    (state.filterClassical (fun record => predicate record.1)).quantumMarginal.matrix =
      ∑ stored : Store ctx, if predicate stored then
        (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix
      else 0 := by
  rw [← sum_store_matrices (state.filterClassical (fun record => predicate record.1))]
  apply Finset.sum_congr rfl
  intro stored _
  by_cases selected : predicate stored
  · rw [if_pos selected]
    change (∑ record : Store ctx × History,
      (if record.1 = stored then
        (state.filterClassical (fun value => predicate value.1)).block record
      else DensityOperator.zero _).matrix) =
      ∑ record : Store ctx × History,
        (if record.1 = stored then state.block record else DensityOperator.zero _).matrix
    apply Finset.sum_congr rfl
    intro record _
    by_cases same : record.1 = stored
    · have keep : predicate record.1 := same.symm ▸ selected
      simp only [if_pos same, ExecutionState.filterClassical_block, if_pos keep]
    · simp only [if_neg same]
  · rw [if_neg selected]
    change (∑ record : Store ctx × History,
      (if record.1 = stored then
        (state.filterClassical (fun value => predicate value.1)).block record
      else DensityOperator.zero _).matrix) = 0
    apply Finset.sum_eq_zero
    intro record _
    by_cases same : record.1 = stored
    · have drop : ¬ predicate record.1 := fun keep => selected (same ▸ keep)
      simp only [if_pos same, ExecutionState.filterClassical_block, if_neg drop,
        DensityOperator.zero_matrix]
    · simp only [if_neg same, DensityOperator.zero_matrix]

def storeDensity {width m : Nat} {Reference : Register} {History : Type} [Fintype History]
    (state : State (Interface width m) Reference History) (stored : Store (Interface width m)) :
    Matrix ((Interface width m).register.prod Reference).Index
      ((Interface width m).register.prod Reference).Index ℂ :=
  (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix

def stepDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (Reference : Register)
    (density : Store (Interface p.size m) →
      Matrix ((Interface p.size m).register.prod Reference).Index
        ((Interface p.size m).register.prod Reference).Index ℂ)
    (stored : Store (Interface p.size m)) :
    Matrix ((Interface p.size m).register.prod Reference).Index
      ((Interface p.size m).register.prod Reference).Index ℂ :=
  ∑ intermediate : Store (Interface p.size m),
    ∑ outcome : Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension,
      ∑ division : Store (MeasuredPointAddition.context p.size),
        if intermediate.write (output p.size m index) (.finite outcome) = stored then
          stageMatrix (environment := environment) E r points index Reference intermediate outcome
            division *
            (∑ original : Store (Interface p.size m),
              if retains p.size m intermediate original then density original else 0) *
              (stageMatrix (environment := environment) E r points index Reference intermediate
                outcome division).conjTranspose
        else 0

lemma stage_store_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Interface p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (Interface p.size m)) :
    storeDensity ((stage E r points index).execute environment Reference state) stored =
      stepDensity (environment := environment) E r points index Reference (storeDensity state)
        stored := by
  unfold storeDensity
  rw [stage_store_matrix]
  unfold stepDensity
  apply Finset.sum_congr rfl
  intro intermediate _
  apply Finset.sum_congr rfl
  intro outcome _
  apply Finset.sum_congr rfl
  intro division _
  by_cases written : intermediate.write (output p.size m index) (.finite outcome) = stored
  · rw [if_pos written, if_pos written, filter_store_matrix]
  · rw [if_neg written, if_neg written]

def storedRecursion
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register) :
    List (Fin (2 * m)) →
      (Store (Interface p.size m) →
        Matrix ((Interface p.size m).register.prod Reference).Index
          ((Interface p.size m).register.prod Reference).Index ℂ) →
      Store (Interface p.size m) →
        Matrix ((Interface p.size m).register.prod Reference).Index
          ((Interface p.size m).register.prod Reference).Index ℂ
  | [], density => density
  | index :: tail, density =>
      storedRecursion (environment := environment) E r points Reference tail
        (stepDensity (environment := environment) E r points index Reference density)

lemma stages_store_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (indices : List (Fin (2 * m))) {Reference : Register} {History : Type} [Fintype History]
    (state : State (Interface p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (Interface p.size m)) :
    storeDensity ((stages E r points indices).execute environment Reference state) stored =
      storedRecursion (environment := environment) E r points Reference indices (storeDensity
        state) stored := by
  induction indices generalizing History with
  | nil =>
      exact id_store_matrix state stored
  | cons index tail ih =>
      let firstOutput : State (Interface p.size m) Reference
          (ClassicalOracleModel.empty.HiddenState × (History × (stage E r points index).Path)) :=
        (stage E r points index).execute environment Reference state
      have sequential :
          storeDensity
            (((stage E r points index).seq (stages E r points tail)).execute environment Reference
              state)
              stored =
            storeDensity ((stages E r points tail).execute environment Reference firstOutput)
              stored :=
        congrArg DensityOperator.matrix
        (Circuit.seq_store_marginal (environment := environment)
          (stage E r points index) (stages E r points tail)
          state stored)
      have tailLaw : storeDensity ((stages E r points tail).execute environment Reference
        firstOutput) stored =
          storedRecursion (environment := environment) E r points Reference tail (storeDensity
            firstOutput) stored :=
        ih firstOutput
      change storeDensity
          (((stage E r points index).seq (stages E r points tail)).execute environment Reference
            state)
            stored = _
      refine sequential.trans (tailLaw.trans ?_)
      have first : storeDensity firstOutput =
          stepDensity (environment := environment) E r points index Reference (storeDensity state)
            := by
        funext original
        exact stage_store_density E r points index state original
      exact congrArg (fun density : Store (Interface p.size m) →
          HilbertOperator ((Interface p.size m).register.prod Reference) =>
        storedRecursion (environment := environment) E r points Reference tail density stored) first

lemma stageMatrix_zero_control {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (Reference : Register) (stored : Store (Interface p.size m))
    (outcome : Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (division : Store (MeasuredPointAddition.context p.size))
    (rowControl rowMemory : Fin 2) (rowBank : Bank p.size m Reference)
    (column : ((Interface p.size m).register.prod Reference).Index)
    (nonzero : rowControl ≠ 0) :
    stageMatrix (environment := environment) E r points index Reference stored outcome division
      ((coordinates p.size m Reference).symm (rowControl, (rowMemory, rowBank))) column = 0 := by
  let readout : HilbertOperator ((Interface p.size m).register.prod Reference) :=
    readoutMatrix (environment := environment) p.size m Reference outcome
  let feedback : HilbertOperator ((Interface p.size m).register.prod Reference) :=
    feedbackMatrix (environment := environment) p.size m Reference index stored
      (Recovery.Layout.order m)
  let point : HilbertOperator ((Interface p.size m).register.prod Reference) :=
    pointMatrix (environment := environment) E (points index) m Reference division stored
  let prepared : HilbertOperator ((Interface p.size m).register.prod Reference) :=
    preparationMatrix (environment := environment) p.size m r index Reference
  let basis : ((Interface p.size m).register.prod Reference).Index ≃
      Fin 2 × (Fin 2 × Bank p.size m Reference) := coordinates p.size m Reference
  let row : ((Interface p.size m).register.prod Reference).Index :=
    basis.symm (rowControl, (rowMemory, rowBank))
  have grouped : stageMatrix (environment := environment) E r points index Reference stored
    outcome division =
      readout * (feedback * (point * prepared)) := by
    change ((readout * feedback) * point) * prepared = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  have groupedEntry := congrArg (fun operator :
      HilbertOperator ((Interface p.size m).register.prod Reference) => operator row column) grouped
  refine groupedEntry.trans ?_
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro middle _
  have resetZero : readout row middle = 0 := by
    have actual : readout row (basis.symm (basis middle)) =
        if rowControl = 0 ∧ rowMemory = (basis middle).2.1 ∧ rowBank = (basis middle).2.2 then
          Gate.HOp (ReadoutRows.outcomeBit p.size m outcome) (basis middle).1 else 0 :=
      ReadoutRows.readoutMatrix_entry p.size m Reference outcome
        rowControl (basis middle).1 rowMemory (basis middle).2.1 rowBank (basis middle).2.2
    have impossible : ¬ (rowControl = 0 ∧
        rowMemory = (basis middle).2.1 ∧ rowBank = (basis middle).2.2) :=
      fun same => nonzero same.1
    have coordinatesSame : readout row (basis.symm (basis middle)) = readout row middle :=
      congrArg (fun value : ((Interface p.size m).register.prod Reference).Index =>
        readout row value) (basis.symm_apply_apply middle)
    exact coordinatesSame.symm.trans (actual.trans (if_neg impossible))
  rw [resetZero, zero_mul]

def freshBlock {width m : Nat} (Reference : Register)
    (operator : Matrix ((Interface width m).register.prod Reference).Index
      ((Interface width m).register.prod Reference).Index ℂ) :
    Matrix (Bool × Bank width m Reference) (Bool × Bank width m Reference) ℂ :=
  operator.submatrix
    (fun value => (coordinates width m Reference).symm (0, (bitBasis value.1, value.2)))
    (fun value => (coordinates width m Reference).symm (0, (bitBasis value.1, value.2)))

lemma freshBlock_stage {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (Reference : Register) (stored : Store (Interface p.size m))
    (outcome : Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (division : Store (MeasuredPointAddition.context p.size)) :
    freshBlock Reference (stageMatrix (environment := environment) E r points index Reference
      stored outcome division) =
      fun row column => ∑ emitted : Bool,
        (table (2 ^ Recovery.Layout.remaining m index)
          (r % (2 * 2 ^ Recovery.Layout.remaining m index)) column.1 emitted row.1 : ℂ) *
            action (environment := environment) E points index Reference division stored outcome
              emitted row.2 column.2 := by
  apply Matrix.ext
  intro row column
  change stageMatrix (environment := environment) E r points index Reference stored outcome division
      ((coordinates p.size m Reference).symm (0, (bitBasis row.1, row.2)))
      ((coordinates p.size m Reference).symm (0, (bitBasis column.1, column.2))) = _
  exact stageMatrix_fresh_columns E r points index Reference column.1 row.1
    division stored outcome row.2 column.2

lemma freshBlock_tail_stage {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (Reference : Register) (stored : Store (Interface p.size m))
    (outcome : Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (division : Store (MeasuredPointAddition.context p.size))
    (continuation : Matrix ((Interface p.size m).register.prod Reference).Index
      ((Interface p.size m).register.prod Reference).Index ℂ) :
    freshBlock Reference
        (continuation * stageMatrix (environment := environment) E r points index Reference stored
          outcome division) =
      freshBlock Reference continuation *
        freshBlock Reference (stageMatrix (environment := environment) E r points index Reference
          stored outcome division) := by
  let joint : ((Interface p.size m).register.prod Reference).Index ≃
      Fin 2 × (Bool × Bank p.size m Reference) :=
    (coordinates p.size m Reference).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr bitBasis.symm (Equiv.refl _)))
  let operator : ((Interface p.size m).register.prod Reference).Index →
      ((Interface p.size m).register.prod Reference).Index → ℂ :=
    stageMatrix (environment := environment) E r points index Reference stored outcome division
  have jointRows (control : Fin 2) (row : Bool × Bank p.size m Reference) :
      joint.symm (control, row) =
        (coordinates p.size m Reference).symm (control, (bitBasis row.1, row.2)) := by
    rfl
  have zeroRows (control : Fin 2) (row column : Bool × Bank p.size m Reference)
      (nonzero : control ≠ 0) :
      operator (joint.symm (control, row)) (joint.symm (0, column)) = 0 := by
    rw [jointRows control row]
    exact stageMatrix_zero_control E r points index Reference stored outcome division
      control (bitBasis row.1) row.2 (joint.symm (0, column)) nonzero
  have product := MatrixSupport.zeroControl_submatrix_mul
    (Source := ((Interface p.size m).register.prod Reference).Index)
    (Block := Bool × Bank p.size m Reference) joint continuation operator zeroRows
  simpa (config := { zetaDelta := false }) only [freshBlock, jointRows, operator] using product

end

end PointCoordinates.StageWord.StoredRecursion
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
