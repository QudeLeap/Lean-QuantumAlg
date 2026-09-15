/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Length.Read
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Predicate

/-!
# Actual guarded leading-one native blocks for shared-EEA length refresh

The native pattern directly reads the two original zero-tested fields,
the actual retained boundary key, and the selected physical payload prefix.
It flips the real target length bit precisely under the source boundary
and the already proved exact arithmetic length test
[LYL+26, sec_EEA/sub_regshare.tex:309-313;
sec_circuit/sub_block_new.tex:211-219,338-341].

The new predicate has the exact conditional action of the existing native
length predicate. Both use arbitrary original Iter as their only work bit
and preserve its value. The actual added guard wires are included in the
emitted conjunction and in its actual elementary count.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthPredicate

noncomputable section

open EncodedBit LengthCoordinates LengthRead GuardedLengthRead

private theorem source_prefix_get (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (output : Fin width.size)
    (index : Fin (GuardedLengthCoordinates.prefixWidth width)) (state : Registers width) :
    ((GuardedLengthCoordinates.layout width field key firstWord output).source.bit
      (Word.OneDirtyLayout.keyIndex index)).get state =
        (prefixBit width field key firstWord index).get state := rfl

private theorem source_payload_get (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (output : Fin width.size) (index : Fin (region width field key))
    (state : Registers width) :
    ((GuardedLengthCoordinates.layout width field key firstWord output).source.bit
      (Word.OneDirtyLayout.wordIndex index)).get state =
        (payloadValue field key firstWord state).testBit
          (region width field key - 1 - index.val) := by
  have afterGuard : ¬GuardedLengthCoordinates.prefixWidth width + index.val < 2 * width.size := by
    unfold GuardedLengthCoordinates.prefixWidth
    omega
  change (GuardedLengthCoordinates.sourceBit width field key firstWord
    ⟨GuardedLengthCoordinates.prefixWidth width + index.val, _⟩).get state = _
  rw [GuardedLengthCoordinates.sourceBit, dif_neg afterGuard]
  have same :
      (⟨GuardedLengthCoordinates.prefixWidth width + index.val - 2 * width.size, by
        have within := index.isLt
        unfold GuardedLengthCoordinates.prefixWidth
        omega⟩ : Fin (width.size + region width field key)) =
          ⟨width.size + index.val, by have within := index.isLt; omega⟩ := by
    apply Fin.ext
    change GuardedLengthCoordinates.prefixWidth width + index.val - 2 * width.size =
      width.size + index.val
    unfold GuardedLengthCoordinates.prefixWidth
    omega
  rw [same]
  exact LengthPredicate.source_payload_get width field key firstWord output index state

/-- The real enlarged source pattern reads exactly the guard and the original actual length test. -/
theorem leading_iff (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    (GuardedLengthCoordinates.layout width field key firstWord output).PrefixLeading position
        (expected width key) state ↔
      Guard state ∧ LengthPredicate.Selected field key firstWord position state := by
  unfold LengthPredicate.Selected
  rw [← QuantumAlg.NumberTheory.SharedEEA.LeadingBit.selected_iff_size
    (region width field key) (payloadValue field key firstWord state)
    (payloadValue_fits field key firstWord state) position]
  simp only [Word.OneDirtyLayout.PrefixLeading, source_prefix_get, source_payload_get,
    prefix_matches_iff, QuantumAlg.NumberTheory.SharedEEA.LeadingBit.selected, and_assoc]

/-- Actual native predicate on the enlarged original source prefix and the real length output. -/
def gates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    List (GateSpec (encoding width)) :=
  (GuardedLengthCoordinates.layout width field key firstWord output).leadingOneGates position
    (expected width key)

/-- The exact complete-state action includes the actual two-field boundary predicate. -/
theorem gates_step (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (gates width field key firstWord position output) state =
      if Guard state ∧ LengthPredicate.Selected field key firstWord position state
      then (outputBit width field output).flip state else state := by
  rw [gates, Word.OneDirtyLayout.leadingOneGates_step]
  change (if (GuardedLengthCoordinates.layout width field key firstWord output).PrefixLeading
      position (expected width key) state
    then (outputBit width field output).flip state else state) = _
  simp only [leading_iff]

/-- The new actual native block is exactly the existing block under the retained real guard. -/
theorem gates_step_if (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (gates width field key firstWord position output) state =
      if Guard state
      then GateSpec.stepList (LengthPredicate.gates width field key firstWord position output) state
      else state := by
  rw [gates_step, LengthPredicate.gates_step]
  by_cases guarded : Guard state
  · simp only [guarded, true_and, if_true]
  · simp only [guarded, false_and, if_false]

/-- Every original block retains the actual guard, permitting exact full-list refinement. -/
theorem original_guard (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    Guard (GateSpec.stepList (LengthPredicate.gates width field key firstWord position output)
      state) ↔ Guard state := by
  rw [LengthPredicate.gates_step]
  split
  · exact guard_output_flip width field output state
  · rfl

/-- Complete native basis action retains all original data, including arbitrary dirty Iter. -/
theorem gates_realizes (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (gates width field key firstWord position output))
      (fun state => if Guard state ∧ LengthPredicate.Selected field key firstWord position state
        then (outputBit width field output).flip state else state) :=
  GateSpec.realizesList_congrStep _ (gates_step width field key firstWord position output)

/-- All actual added guard controls and their arbitrary-work cleanup are counted. -/
theorem gates_length_le (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    (gates width field key firstWord position output).length ≤
      10 * (3 * width.size + (position.val + 1)) + 1 :=
  (GuardedLengthCoordinates.layout width field key firstWord output).leadingOneGates_length_le
    position _

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthPredicate
