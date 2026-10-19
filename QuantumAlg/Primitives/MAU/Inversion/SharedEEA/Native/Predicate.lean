/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PredicateLayout
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.ZeroTest

/-!
# Executed native shared-EEA zero predicates with restored Work2

These programs test the actual retained length fields used by the source
control logic [LYL+26, sec_EEA/sub_regshare.tex:303-315]. They compile the
elementary zero-predicate construction associated with
[dW19, qcnotes.tex:1335-1337], using its separately proved arbitrary-work
refinement. The source exercise permits clean auxiliary bits; restoration
of arbitrary incoming Work2 values is an additional proved property of
the literal gate list used here, not a cleanliness assumption.

Every theorem below identifies the complete register result: only Ctrl
is xored with the actual predicate. Both shared words, all lengths, and
all four other controls are restored exactly, including nonzero incoming
work and the high counter bits inside Work1. The same gates determine
the native programs and the explicit elementary event counts. No new
workspace, inferred classical branch, or opaque predicate gate is used.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativePredicate

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit PredicateLayout

private lemma word_zero_iff {width : Nat} (word : BitVec width) :
    (∀ index : Fin width, word.getMsbD index.val = false) ↔ word = 0 := by
  constructor
  · intro zeros
    apply BitVec.eq_of_getMsbD_eq
    intro index within
    exact (zeros ⟨index, within⟩).trans (BitVec.getMsbD_zero (w := width) (i := index)).symm
  · intro zero index
    rw [zero]
    exact BitVec.getMsbD_zero

lemma single_source_zero_iff (width : Nat) (field : LengthField) (enough : 2 ≤ width.size)
    (state : Registers width) :
    (∀ index, ((single width field enough).source.bit index).get state = false) ↔
      lengthValue field state = 0 := by
  rw [← word_zero_iff]
  constructor
  · intro zeros index
    have selected := zeros ⟨index.val, by have within := index.isLt; omega⟩
    rw [single_source_get] at selected
    exact selected
  · intro zeros index
    rw [single_source_get]
    exact zeros ⟨index.val, by have within := index.isLt; omega⟩

lemma pair_source_zero_iff (width : Nat) (first second : LengthField)
    (different : first ≠ second) (enough : 2 ≤ width.size) (state : Registers width) :
    (∀ index, ((pair width first second different enough).source.bit index).get state = false) ↔
      lengthValue first state = 0 ∧ lengthValue second state = 0 := by
  rw [← word_zero_iff, ← word_zero_iff]
  constructor
  · intro zeros
    constructor
    · intro index
      have selected := zeros ⟨index.val, by have within := index.isLt; omega⟩
      rw [pair_source_get, if_pos index.isLt] at selected
      exact selected
    · intro index
      have selected := zeros ⟨width.size + index.val, by have within := index.isLt; omega⟩
      have notInitial : ¬width.size + index.val < width.size := by omega
      rw [pair_source_get, if_neg notInitial] at selected
      simpa only [Nat.add_sub_cancel_left] using selected
  · rintro ⟨firstZero, secondZero⟩ index
    rw [pair_source_get]
    by_cases initial : index.val < width.size
    · rw [if_pos initial]
      exact firstZero ⟨index.val, initial⟩
    · rw [if_neg initial]
      exact secondZero ⟨index.val - width.size, by have within := index.isLt; omega⟩

lemma clock_source_zero_iff (width : Nat) (state : Registers width) :
    (∀ index, ((extendedClock width).source.bit index).get state = false) ↔
      NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0 := by
  rw [← word_zero_iff, ← word_zero_iff]
  constructor
  · intro zeros
    constructor
    · intro index
      have selected := zeros ⟨index.val, by have within := index.isLt; omega⟩
      rw [extendedClock_source_get, if_pos index.isLt] at selected
      exact selected
    · intro index
      have selected := zeros ⟨2 + index.val, by have within := index.isLt; omega⟩
      have notHigh : ¬2 + index.val < 2 := by omega
      rw [extendedClock_source_get, if_neg notHigh] at selected
      simpa only [Nat.add_sub_cancel_left] using selected
  · rintro ⟨highZero, lowZero⟩ index
    rw [extendedClock_source_get]
    by_cases high : index.val < 2
    · rw [if_pos high]
      exact highZero ⟨index.val, high⟩
    · rw [if_neg high]
      exact lowZero ⟨index.val - 2, by have within := index.isLt; omega⟩

/-- Full-register mathematical specification of writing a predicate into the existing Ctrl. -/
def xorControl {width : Nat} (value : Bool) (state : Registers width) : Registers width :=
  { state with control := state.control ^^ value }

private lemma xorControl_false {width : Nat} (state : Registers width) :
    xorControl false state = state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, flags, control⟩
  cases control <;> rfl

private lemma xorControl_true {width : Nat} (state : Registers width) :
    xorControl true state = (controlBit width).flip state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, flags, control⟩
  cases control <;> rfl

private lemma conditional_flip_xor {width : Nat} (predicate : Prop) [Decidable predicate]
    (state : Registers width) :
    (if predicate then (controlBit width).flip state else state) =
      xorControl (decide predicate) state := by
  by_cases selected : predicate
  · rw [if_pos selected, decide_eq_true selected, xorControl_true]
  · rw [if_neg selected, decide_eq_false selected, xorControl_false]

/-- Every field except Ctrl is unchanged; in particular the entire borrowed Work2 is restored. -/
lemma xorControl_retained {width : Nat} (value : Bool) (state : Registers width) :
    (xorControl value state).firstWord = state.firstWord ∧
      (xorControl value state).secondWord = state.secondWord ∧
      (xorControl value state).coefficientLength = state.coefficientLength ∧
      (xorControl value state).quotientLength = state.quotientLength ∧
      (xorControl value state).divisorLength = state.divisorLength ∧
      (xorControl value state).shift = state.shift ∧
      (xorControl value state).flags = state.flags := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every input bit of Ctrl is retained reversibly by xor, rather than overwritten. -/
lemma xorControl_twice {width : Nat} (value : Bool) (state : Registers width) :
    xorControl value (xorControl value state) = state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, flags, control⟩
  cases value <;> cases control <;> rfl

/-- Actual X/Toffoli gate list for one retained length. -/
def singleGates (width : Nat) (field : LengthField) (enough : 2 ≤ width.size) :
    List (GateSpec (encoding width)) :=
  Word.ZeroTestLayout.borrowedZeroGates (single width field enough)

lemma singleGates_step (width : Nat) (field : LengthField) (enough : 2 ≤ width.size)
    (state : Registers width) :
    GateSpec.stepList (singleGates width field enough) state =
      xorControl (decide (lengthValue field state = 0)) state := by
  rw [singleGates, Word.ZeroTestLayout.borrowedZeroGates_step]
  simp only [single_source_zero_iff]
  change (if lengthValue field state = 0 then (controlBit width).flip state else state) = _
  exact conditional_flip_xor _ state

/-- Actual gate list for the simultaneous zero predicate of two distinct lengths. -/
def pairGates (width : Nat) (first second : LengthField) (different : first ≠ second)
    (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  Word.ZeroTestLayout.borrowedZeroGates (pair width first second different enough)

lemma pairGates_step (width : Nat) (first second : LengthField) (different : first ≠ second)
    (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (pairGates width first second different enough) state =
      xorControl (decide (lengthValue first state = 0 ∧ lengthValue second state = 0)) state := by
  rw [pairGates, Word.ZeroTestLayout.borrowedZeroGates_step]
  simp only [pair_source_zero_iff]
  change (if lengthValue first state = 0 ∧ lengthValue second state = 0
    then (controlBit width).flip state else state) = _
  exact conditional_flip_xor _ state

/-- Actual zero test of all repaired counter bits, including the two original Work1 positions. -/
def clockGates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.ZeroTestLayout.borrowedZeroGates (extendedClock width)

lemma clockGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (clockGates width) state =
      xorControl (decide (NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧
        state.shift = 0)) state := by
  rw [clockGates, Word.ZeroTestLayout.borrowedZeroGates_step]
  simp only [clock_source_zero_iff]
  change (if NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0
    then (controlBit width).flip state else state) = _
  exact conditional_flip_xor _ state

def singleProgram (width : Nat) (field : LengthField) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (singleGates width field enough)

lemma singleProgram_realizes (width : Nat) (field : LengthField) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (layout := QubitLayout.canonical _)
      (encoding width) (singleProgram width field enough) environment
      (fun state => xorControl (decide (lengthValue field state = 0)) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (singleGates_step width field enough) environment

def pairProgram (width : Nat) (first second : LengthField) (different : first ≠ second)
    (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty
    (pairGates width first second different enough)

lemma pairProgram_realizes (width : Nat) (first second : LengthField)
    (different : first ≠ second) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (layout := QubitLayout.canonical _)
      (encoding width) (pairProgram width first second different enough) environment
      (fun state => xorControl (decide
        (lengthValue first state = 0 ∧ lengthValue second state = 0)) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (pairGates_step width first second different enough) environment

def clockProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (clockGates width)

lemma clockProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (layout := QubitLayout.canonical _)
      (encoding width) (clockProgram width) environment
      (fun state => xorControl (decide
        (NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0 ∧ state.shift = 0)) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (clockGates_step width) environment

/-- Closed elementary gate count for a tested word with `tail + 2` source bits. -/
def gateCount (tail : Nat) : Nat := 2 * (tail + 2) + if tail = 0 then 1 else 4 * tail

lemma singleGates_length (width : Nat) (field : LengthField) (enough : 2 ≤ width.size) :
    (singleGates width field enough).length = gateCount (width.size - 2) :=
  Word.ZeroTestLayout.borrowedZeroGates_length (single width field enough)

lemma pairGates_length (width : Nat) (first second : LengthField)
    (different : first ≠ second) (enough : 2 ≤ width.size) :
    (pairGates width first second different enough).length = gateCount (2 * width.size - 2) :=
  Word.ZeroTestLayout.borrowedZeroGates_length (pair width first second different enough)

lemma clockGates_length (width : Nat) : (clockGates width).length = gateCount width.size :=
  Word.ZeroTestLayout.borrowedZeroGates_length (extendedClock width)

lemma singleProgram_eventCost_card (width : Nat) (field : LengthField)
    (enough : 2 ≤ width.size) :
    (singleProgram width field enough).eventCost.card = gateCount (width.size - 2) := by
  rw [singleProgram, GateSpec.programList_eventCost_card, singleGates_length]

lemma pairProgram_eventCost_card (width : Nat) (first second : LengthField)
    (different : first ≠ second) (enough : 2 ≤ width.size) :
    (pairProgram width first second different enough).eventCost.card =
      gateCount (2 * width.size - 2) := by
  rw [pairProgram, GateSpec.programList_eventCost_card, pairGates_length]

lemma clockProgram_eventCost_card (width : Nat) :
    (clockProgram width).eventCost.card = gateCount width.size := by
  rw [clockProgram, GateSpec.programList_eventCost_card, clockGates_length]

lemma clockProgram_unitDepth (width : Nat) :
    (clockProgram width).evaluatedEventDepth (fun _ => 1) = gateCount width.size := by
  rw [clockProgram, GateSpec.programList_evaluatedEventDepth_unit, clockGates_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativePredicate
