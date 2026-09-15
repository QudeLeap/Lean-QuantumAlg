/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Read
import all QuantumAlg.Components.Encoded.BitGates.Word.LeadingOne
import all QuantumAlg.Util.NumberTheory.SharedEEA.LeadingBit

/-!
# Actual retained-boundary and length predicates on the original shared EEA frame

Each fixed boundary key and leading position compiles to the actual masked
conjunction gates on the original length-field and work-word coordinates.
The only temporary work bit is the original arbitrary Iter bit, which is
restored on every call [G17, paper.tex:278-293]. The designated output is a
real bit of the length register being refreshed.

The complete native action tests the current boundary word and the exact
ordinary binary size of its physical region, as required by the source's
old-length and new-length XOR operations
[LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341]. No input-dependent
value is passed to the circuit as a preparation parameter.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthPredicate

noncomputable section

open EncodedBit LengthCoordinates LengthRead

/-- A static candidate matches the actual retained boundary and actual read value's size. -/
def Selected {width : Nat} (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (state : Registers width) : Prop :=
  boundaryValue field state = key ∧
    (payloadValue field key firstWord state).size = region width field key - position.val

private instance selectedDecidable {width : Nat} (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (state : Registers width) :
    Decidable (Selected field key firstWord position state) := by
  unfold Selected
  infer_instance

private theorem source_key_get (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (output index : Fin width.size) (state : Registers width) :
    ((layout width field key firstWord output).source.bit
      (Word.OneDirtyLayout.keyIndex index)).get state =
        (boundaryValue field state).getMsbD index.val := by
  change (sourceBit width field key firstWord ⟨index.val, _⟩).get state = _
  rw [sourceBit, dif_pos index.isLt]
  exact boundaryBit_get width field index state

private theorem source_payload_get (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (output : Fin width.size) (index : Fin (region width field key))
    (state : Registers width) :
    ((layout width field key firstWord output).source.bit
      (Word.OneDirtyLayout.wordIndex index)).get state =
        (payloadValue field key firstWord state).testBit
          (region width field key - 1 - index.val) := by
  have afterKey : ¬width.size + index.val < width.size := by omega
  change (sourceBit width field key firstWord ⟨width.size + index.val, _⟩).get state = _
  calc
    _ = (payloadBit width field key firstWord index).get state := by
      rw [sourceBit, dif_neg afterKey]
      exact congrArg (fun selected : Fin (region width field key) =>
        (payloadBit width field key firstWord selected).get state)
          (Fin.ext (Nat.add_sub_cancel_left width.size index.val))
    _ = _ := payloadBit_testBit width field key firstWord index state

/-- The actual full source predicate is exactly the actual boundary and arithmetic size test. -/
theorem leading_iff (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    (layout width field key firstWord output).PrefixLeading position
        (fun index => key.getMsbD index.val) state ↔
      Selected field key firstWord position state := by
  have keyMatches :
      (∀ index : Fin width.size,
        (boundaryValue field state).getMsbD index.val = key.getMsbD index.val) ↔
          boundaryValue field state = key := by
    simpa only [boundaryBit_get] using boundary_matches_iff width field key state
  unfold Selected
  rw [← QuantumAlg.NumberTheory.SharedEEA.LeadingBit.selected_iff_size
    (region width field key) (payloadValue field key firstWord state)
    (payloadValue_fits field key firstWord state) position]
  simp only [Word.OneDirtyLayout.PrefixLeading, source_key_get, source_payload_get,
    QuantumAlg.NumberTheory.SharedEEA.LeadingBit.selected]
  exact and_congr keyMatches Iff.rfl

/-- Actual elementary gates for one static boundary, leading position, and output bit. -/
def gates (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    List (GateSpec (encoding width)) :=
  (layout width field key firstWord output).leadingOneGates position
    (fun index => key.getMsbD index.val)

/-- The emitted native list has this exact complete-register action for arbitrary incoming data. -/
theorem gates_step (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (gates width field key firstWord position output) state =
      if Selected field key firstWord position state
      then (outputBit width field output).flip state else state := by
  rw [gates, Word.OneDirtyLayout.leadingOneGates_step]
  change (if (layout width field key firstWord output).PrefixLeading position
      (fun index => key.getMsbD index.val) state
    then (outputBit width field output).flip state else state) = _
  simp only [leading_iff]

/-- Native target writes preserve the exact condition read by all subsequent copies. -/
theorem selected_output_flip (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    Selected field key firstWord position ((outputBit width field output).flip state) ↔
      Selected field key firstWord position state := by
  simp only [Selected, boundaryValue_output_flip, payloadValue_output_flip]

/-- The actual program realizes the complete state update, retaining relative amplitudes. -/
theorem gates_realizes (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (gates width field key firstWord position output))
      (fun state => if Selected field key firstWord position state
        then (outputBit width field output).flip state else state) :=
  GateSpec.realizesList_congrStep _ (gates_step width field key firstWord position output)

/-- The original arbitrary Iter work value is restored, whether or not this candidate matches. -/
theorem gates_iteration (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size)
    (state : Registers width) :
    (iterationBit width).get
        (GateSpec.stepList (gates width field key firstWord position output) state) =
      (iterationBit width).get state :=
  (layout width field key firstWord output).leadingOneGates_work position _ state

/-- Actual count includes all key masks, prefix masks, and arbitrary-work cleanup gates. -/
theorem gates_length_le (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (position : Fin (region width field key)) (output : Fin width.size) :
    (gates width field key firstWord position output).length ≤
      10 * (width.size + (position.val + 1)) + 1 :=
  (layout width field key firstWord output).leadingOneGates_length_le position _

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthPredicate
