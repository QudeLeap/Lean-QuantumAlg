/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Predicate
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Actual finite length XOR at one static boundary key

The gate list enumerates every possible leading position in the actual
selected work-word region. Each position emits the native predicate once
for each set bit of its fixed finite length label. Consequently the actual
current word's length is XORed into the existing length field precisely
when the retained boundary matches this key
[LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341].

The circuit parameters contain no input-dependent length. Arbitrary finite
labels use the original finite-width XOR, including empty target fields
and values whose size wraps in that field. Existing reachable-state
capacity theorems discharge truncation separately for the original input
domain. Neither Ctrl nor an additional workspace bit is required.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthWrite

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit LengthCoordinates LengthRead

/-- The existing length field in the native constant-XOR API's least-significant-first order. -/
def target (width : Nat) (field : Field) : Word (encoding width) width.size :=
  ⟨outputBit width field⟩

/-- Finite labels retain the actual hardware width on every input, without a capacity premise. -/
def constant (width value : Nat) : Fin (2 ^ width.size) :=
  ⟨value % 2 ^ width.size, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The static finite label for a possible first-one position. -/
def positionConstant (width : Nat) (field : Field) (key : BitVec width.size)
    (position : Fin (region width field key)) : Fin (2 ^ width.size) :=
  constant width (region width field key - position.val)

private lemma constant_preserves_reads (width : Nat) (field : Field) (firstWord : Bool)
    (value : Fin (2 ^ width.size)) (state : Registers width) :
    (boundaryValue field (Word.xorConstantStep (target width field) value state),
      sourceWord firstWord (Word.xorConstantStep (target width field) value state)) =
        (boundaryValue field state, sourceWord firstWord state) := by
  simp only [Word.xorConstantStep_eq_indicesStep]
  generalize Word.constantOneIndices value = indices
  induction indices generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      change (boundaryValue field (Word.xorConstantIndicesStep (target width field) rest
          ((outputBit width field bit).flip state)),
        sourceWord firstWord (Word.xorConstantIndicesStep (target width field) rest
          ((outputBit width field bit).flip state))) = _
      rw [ih, boundaryValue_output_flip, sourceWord_output_flip]

/-- The constant write preserves the entire retained boundary word used by later candidates. -/
lemma constant_preserves_boundary (width : Nat) (field : Field)
    (value : Fin (2 ^ width.size)) (state : Registers width) :
    boundaryValue field (Word.xorConstantStep (target width field) value state) =
      boundaryValue field state :=
  congrArg (fun reads : BitVec width.size × BitVec (width + 3) => reads.1)
    (constant_preserves_reads width field false value state)

/-- The constant write preserves the complete actual work word, including every outside bit. -/
lemma constant_preserves_sourceWord (width : Nat) (field : Field) (firstWord : Bool)
    (value : Fin (2 ^ width.size)) (state : Registers width) :
    sourceWord firstWord (Word.xorConstantStep (target width field) value state) =
      sourceWord firstWord state :=
  congrArg (fun reads : BitVec width.size × BitVec (width + 3) => reads.2)
    (constant_preserves_reads width field firstWord value state)

/-- The exact arithmetic read used by every later candidate is retained. -/
lemma constant_preserves_payload (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (value : Fin (2 ^ width.size)) (state : Registers width) :
    payloadValue field key firstWord (Word.xorConstantStep (target width field) value state) =
      payloadValue field key firstWord state := by
  unfold payloadValue
  rw [constant_preserves_sourceWord]

/-- Emit the real boundary/leading-one native predicate for each set bit of this static label. -/
def positionGates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) : List (GateSpec (encoding width)) :=
  (Word.constantOneIndices (positionConstant width field key position)).flatMap fun bit =>
    LengthPredicate.gates width field key firstWord position bit

private lemma position_indices_step (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key))
    (bits : List (Fin width.size)) (state : Registers width) :
    GateSpec.stepList (bits.flatMap fun bit =>
      LengthPredicate.gates width field key firstWord position bit) state =
        if LengthPredicate.Selected field key firstWord position state
        then Word.xorConstantIndicesStep (target width field) bits state else state := by
  induction bits generalizing state with
  | nil => simp [Word.xorConstantIndicesStep, GateSpec.stepList]
  | cons bit rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, LengthPredicate.gates_step]
      by_cases selected : LengthPredicate.Selected field key firstWord position state
      · rw [if_pos selected, ih]
        simp only [LengthPredicate.selected_output_flip, if_pos selected,
          Word.xorConstantIndicesStep, List.foldl_cons, target]
      · rw [if_neg selected, ih, if_neg selected]
        rw [if_neg selected]

/-- One candidate has a complete-register conditional finite constant-XOR action. -/
lemma positionGates_step (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (state : Registers width) :
    GateSpec.stepList (positionGates width field key firstWord position) state =
      if LengthPredicate.Selected field key firstWord position state
      then Word.xorConstantStep (target width field)
        (positionConstant width field key position) state else state := by
  rw [positionGates, position_indices_step, Word.xorConstantStep_eq_indicesStep]

/-- Enumerate every possible leading position at this static boundary exactly once. -/
def gates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool) :
    List (GateSpec (encoding width)) :=
  (List.ofFn fun position : Fin (region width field key) => position).flatMap
    (positionGates width field key firstWord)

private lemma unmatched_indices_step (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (indices : List (Fin (region width field key))) (state : Registers width)
    (unmatched : boundaryValue field state ≠ key) :
    GateSpec.stepList (indices.flatMap (positionGates width field key firstWord)) state =
      state := by
  induction indices with
  | nil => rfl
  | cons head rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, positionGates_step]
      have absent : ¬LengthPredicate.Selected field key firstWord head state :=
        fun selected => unmatched selected.1
      rw [if_neg absent]
      exact ih

private lemma indices_step (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (value : Nat) (indices : List (Fin (region width field key)))
    (distinct : indices.Nodup) (state : Registers width) (matched : boundaryValue field state = key)
    (input : (payloadValue field key firstWord state).size = value) :
    GateSpec.stepList (indices.flatMap (positionGates width field key firstWord)) state =
      if ∃ index ∈ indices, region width field key - index.val = value
      then Word.xorConstantStep (target width field) (constant width value) state else state := by
  induction indices generalizing state with
  | nil => simp [GateSpec.stepList]
  | cons head rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, positionGates_step]
      by_cases selected : region width field key - head.val = value
      · have chosen : LengthPredicate.Selected field key firstWord head state :=
          ⟨matched, input.trans selected.symm⟩
        rw [if_pos chosen]
        have labels : positionConstant width field key head = constant width value :=
          congrArg (constant width) selected
        rw [labels]
        have retainedBoundary : boundaryValue field
            (Word.xorConstantStep (target width field) (constant width value) state) = key :=
          (constant_preserves_boundary width field _ state).trans matched
        have retainedValue : (payloadValue field key firstWord
            (Word.xorConstantStep (target width field) (constant width value) state)).size =
              value := by
          rw [constant_preserves_payload, input]
        rw [ih distinct.tail _ retainedBoundary retainedValue]
        have noMore : ¬∃ index ∈ rest, region width field key - index.val = value := by
          rintro ⟨index, present, selectedAgain⟩
          have same : index = head := by
            apply Fin.ext
            have indexBound := index.isLt
            have headBound := head.isLt
            omega
          exact distinct.notMem (same ▸ present)
        have present : ∃ index ∈ head :: rest, region width field key - index.val = value :=
          ⟨head, List.mem_cons_self, selected⟩
        rw [if_neg noMore, if_pos present]
      · have absent : ¬LengthPredicate.Selected field key firstWord head state := by
          intro chosen
          exact selected (chosen.2.symm.trans input)
        rw [if_neg absent, ih distinct.tail state matched input]
        have selection :
            (∃ index ∈ head :: rest, region width field key - index.val = value) ↔
              ∃ index ∈ rest, region width field key - index.val = value := by
          constructor
          · rintro ⟨index, present, chosen⟩
            rcases List.mem_cons.mp present with same | later
            · subst index
              exact False.elim (selected chosen)
            · exact ⟨index, later, chosen⟩
          · rintro ⟨index, present, chosen⟩
            exact ⟨index, List.mem_cons_of_mem head present, chosen⟩
        simp only [selection]

private lemma xor_zero (width : Nat) (field : Field) (state : Registers width) :
    Word.xorConstantStep (target width field) (constant width 0) state = state := by
  simp [Word.xorConstantStep, Word.xorConstantGates, Word.constantOneIndices,
    constant, GateSpec.stepList]

/-- The complete emitted circuit reads and writes the actual finite length at a matching key. -/
lemma gates_step (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (state : Registers width) :
    GateSpec.stepList (gates width field key firstWord) state =
      if boundaryValue field state = key
      then Word.xorConstantStep (target width field)
        (constant width (payloadValue field key firstWord state).size) state else state := by
  by_cases matched : boundaryValue field state = key
  · rw [if_pos matched]
    let length := (payloadValue field key firstWord state).size
    have bounded : length ≤ region width field key :=
      Nat.size_le.mpr (payloadValue_fits field key firstWord state)
    rw [gates, indices_step width field key firstWord length _
      (List.nodup_ofFn_ofInjective (fun _ _ same => same)) state matched rfl]
    by_cases positive : 0 < length
    · have present : ∃ index ∈ List.ofFn (fun index : Fin (region width field key) => index),
          region width field key - index.val = length := by
        let chosen : Fin (region width field key) :=
          ⟨region width field key - length, by omega⟩
        refine ⟨chosen, List.mem_ofFn.mpr ⟨chosen, rfl⟩, ?_⟩
        change region width field key - (region width field key - length) = length
        omega
      exact if_pos present
    · have zero : length = 0 := by omega
      have absent : ¬∃ index ∈ List.ofFn (fun index : Fin (region width field key) => index),
          region width field key - index.val = length := by
        rintro ⟨index, _, chosen⟩
        have indexBound := index.isLt
        omega
      rw [if_neg absent]
      have labels : constant width (payloadValue field key firstWord state).size =
          constant width 0 := congrArg (constant width) zero
      rw [labels, xor_zero]
  · rw [if_neg matched]
    exact unmatched_indices_step width field key firstWord _ state matched

/-- Exact complete-state realization of the same emitted elementary gate list. -/
lemma gates_realizes (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty (gates width field key firstWord))
        environment
      (fun state => if boundaryValue field state = key
        then Word.xorConstantStep (target width field)
          (constant width (payloadValue field key firstWord state).size) state else state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width field key firstWord) (gates_step width field key firstWord) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthWrite
