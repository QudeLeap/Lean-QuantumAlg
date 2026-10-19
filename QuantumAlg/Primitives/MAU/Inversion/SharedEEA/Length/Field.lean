/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Write

/-!
# Complete original-frame action of actual length XOR writes

The source updates a retained length by XORing the old and new sizes
[LYL+26, sec_circuit/sub_block_new.tex:211-219]. This owner identifies the
already emitted native gate list with its complete original-register
record update. Both work words, the other three length fields, all phase
flags, arbitrary Iter, and arbitrary Ctrl return exactly unchanged.

The finite XOR includes every incoming target value. Its characterization
therefore keeps all information required by the later reverse gate list;
there is no erasure or implicit allocation in the mathematical update.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthField

noncomputable section

open EncodedBit LengthCoordinates

/-- The actual original length field designated by the current source instruction. -/
def value {width : Nat} : Field → Registers width → BitVec width.size
  | .coefficient, state => state.coefficientLength
  | .divisor, state => state.divisorLength

/-- The complete finite record action characterized below for the actual native constant write. -/
def xorLength {width : Nat} (field : Field) (mask : BitVec width.size)
    (state : Registers width) : Registers width :=
  match field with
  | .coefficient => { state with coefficientLength := state.coefficientLength ^^^ mask }
  | .divisor => { state with divisorLength := state.divisorLength ^^^ mask }

private lemma target_get (width : Nat) (field : Field) (index : Fin width.size)
    (state : Registers width) :
    ((LengthWrite.target width field).bit index).get state =
      (value field state).getLsbD index.val := by
  have reverse : width.size - 1 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have within := index.isLt
    omega
  cases field with
  | coefficient =>
      change (coefficientLengthBit width index.rev).get state = _
      rw [coefficientLengthBit_get]
      simp only [BitVec.getMsbD_eq_getLsbD, index.rev.isLt, decide_true, Bool.true_and,
        reverse, value]
  | divisor =>
      change (divisorLengthBit width index.rev).get state = _
      rw [divisorLengthBit_get]
      simp only [BitVec.getMsbD_eq_getLsbD, index.rev.isLt, decide_true, Bool.true_and,
        reverse, value]

private lemma target_distinct (width : Nat) (field : Field) (left right : Fin width.size)
    (different : left ≠ right) :
    ((LengthWrite.target width field).bit left).wire ≠
      ((LengthWrite.target width field).bit right).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  apply different
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  cases field <;> simp only [LengthWrite.target, outputBit, coefficientLengthBit_wire,
    divisorLengthBit_wire, Fin.val_rev] at values <;> omega

/-- The actual native constant write gives exact finite-word XOR in its target field. -/
lemma constant_value (width : Nat) (field : Field) (constant : Fin (2 ^ width.size))
    (state : Registers width) :
    value field (Word.xorConstantStep (LengthWrite.target width field) constant state) =
      value field state ^^^ BitVec.ofFin constant := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have actual := Word.xorConstantStep_get_target (LengthWrite.target width field) constant
    ⟨index, within⟩ (fun other different => target_distinct width field other _ different) state
  rw [target_get, target_get] at actual
  simpa only [BitVec.getLsbD_xor, BitVec.getLsbD_ofFin] using actual

private def withoutLength {width : Nat} (field : Field) (state : Registers width) :
    Registers width :=
  match field with
  | .coefficient => { state with coefficientLength := 0#width.size }
  | .divisor => { state with divisorLength := 0#width.size }

private lemma withoutLength_flip (width : Nat) (field : Field) (bit : Fin width.size)
    (state : Registers width) :
    withoutLength field ((outputBit width field bit).flip state) = withoutLength field state := by
  cases field <;> rfl

private lemma constant_withoutLength (width : Nat) (field : Field)
    (constant : Fin (2 ^ width.size)) (state : Registers width) :
    withoutLength field (Word.xorConstantStep (LengthWrite.target width field) constant state) =
      withoutLength field state := by
  rw [Word.xorConstantStep_eq_indicesStep]
  generalize Word.constantOneIndices constant = indices
  induction indices generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      change withoutLength field (Word.xorConstantIndicesStep (LengthWrite.target width field)
        rest ((outputBit width field bit).flip state)) = _
      rw [ih, withoutLength_flip]

/-- The complete constant write restores every original coordinate outside its real target field. -/
lemma constant_step_eq (width : Nat) (field : Field) (constant : Fin (2 ^ width.size))
    (state : Registers width) :
    Word.xorConstantStep (LengthWrite.target width field) constant state =
      xorLength field (BitVec.ofFin constant) state := by
  let result := Word.xorConstantStep (LengthWrite.target width field) constant state
  have retained : withoutLength field result = withoutLength field state :=
    constant_withoutLength width field constant state
  have written := constant_value width field constant state
  change value field result = _ at written
  cases field with
  | coefficient =>
      change result.coefficientLength = state.coefficientLength ^^^ BitVec.ofFin constant at written
      calc
        result = { withoutLength .coefficient result with
            coefficientLength := result.coefficientLength } := rfl
        _ = _ := by
          rw [retained, written]
          rfl
  | divisor =>
      change result.divisorLength = state.divisorLength ^^^ BitVec.ofFin constant at written
      calc
        result = { withoutLength .divisor result with divisorLength := result.divisorLength } := rfl
        _ = _ := by
          rw [retained, written]
          rfl

/-- Decoding the exact finite constant gives the original finite-width bit-vector constructor. -/
lemma constant_word (width number : Nat) :
    BitVec.ofFin (LengthWrite.constant width number) = BitVec.ofNat width.size number := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofFin]
  rfl

/-- The actual retained-key native writer has precisely this complete source-register update. -/
lemma gates_step_eq (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (state : Registers width) :
    GateSpec.stepList (LengthWrite.gates width field key firstWord) state =
      if boundaryValue field state = key
      then xorLength field
        (BitVec.ofNat width.size (LengthRead.payloadValue field key firstWord state).size) state
      else state := by
  rw [LengthWrite.gates_step]
  by_cases matched : boundaryValue field state = key
  · simp only [if_pos matched]
    rw [constant_step_eq, constant_word]
  · simp only [if_neg matched]

/-- The identical finite XOR restores every incoming target value without erasing information. -/
lemma xorLength_involutive {width : Nat} (field : Field) (mask : BitVec width.size) :
    Function.Involutive (xorLength field mask) := by
  intro state
  cases field <;> simp only [xorLength, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The complete record update preserves the retained boundary used by the source length refresh. -/
lemma boundary_xorLength {width : Nat} (field : Field) (mask : BitVec width.size)
    (state : Registers width) :
    boundaryValue field (xorLength field mask state) = boundaryValue field state := by
  cases field <;> rfl

/-- The complete original work word is retained even when outside-window payload is nonzero. -/
lemma sourceWord_xorLength {width : Nat} (field : Field) (mask : BitVec width.size)
    (firstWord : Bool) (state : Registers width) :
    LengthRead.sourceWord firstWord (xorLength field mask state) =
      LengthRead.sourceWord firstWord state := by
  cases field <;> cases firstWord <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthField
