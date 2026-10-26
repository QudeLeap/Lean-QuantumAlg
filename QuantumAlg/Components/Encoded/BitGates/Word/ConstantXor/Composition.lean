/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Full-state composition of the actual constant X masks

These equalities use the existing literal X/CNOT lists, including every
physical complement bit. The encoding need not cover the full basis.
-/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma constantStep_encoded_outside (target : Word encoding width)
    (constant : Fin (2 ^ width)) (wire : Fin encoding.width)
    (outside : ∀ index, (target.bit index).wire ≠ wire) (state : Data) :
    (encoding.encode (xorConstantStep target constant state)).val.testBit
        (WireAddress.bitIndex wire).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex wire).val := by
  unfold xorConstantStep xorConstantGates
  generalize constantOneIndices constant = indices
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      change (encoding.encode (GateSpec.stepList (rest.map fun bit => .x (target.bit bit))
        ((target.bit index).flip state))).val.testBit _ = _
      rw [ih, (target.bit index).encode_flip, WireAddress.bit_flipBit_of_ne (outside index)]

/-- Two literal constant masks equal their bitwise XOR on the complete encoded state. -/
lemma xorConstantStep_xor (target : Word encoding width)
    (first second : BitVec width)
    (distinct : Function.Injective (fun index => (target.bit index).wire)) (state : Data) :
    xorConstantStep target second.toFin (xorConstantStep target first.toFin state) =
      xorConstantStep target (first ^^^ second).toFin state := by
  apply encoding.encode_injective
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  let wire := WireAddress.littleEndianWire bit
  have position : (WireAddress.bitIndex wire).val = bit.val := by
    rw [WireAddress.bitIndex_littleEndianWire]
  by_cases inside : ∃ index, (target.bit index).wire = wire
  · obtain ⟨index, same⟩ := inside
    have targetPosition : (WireAddress.bitIndex (target.bit index).wire).val = bit.val := by
      rw [same, position]
    rw [← targetPosition, (target.bit index).get_eq, (target.bit index).get_eq]
    rw [xorConstantStep_get_target target second.toFin index
        (fun other different => fun equal => different (distinct equal)),
      xorConstantStep_get_target target first.toFin index
        (fun other different => fun equal => different (distinct equal)),
      xorConstantStep_get_target target (first ^^^ second).toFin index
        (fun other different => fun equal => different (distinct equal))]
    change ((_ ^^ first.getLsbD index.val) ^^ second.getLsbD index.val) =
      (_ ^^ (first ^^^ second).getLsbD index.val)
    rw [BitVec.getLsbD_xor, Bool.xor_assoc]
  · have outside : ∀ index, (target.bit index).wire ≠ wire := by
      intro index same
      exact inside ⟨index, same⟩
    rw [← position, constantStep_encoded_outside target second.toFin wire outside,
      constantStep_encoded_outside target first.toFin wire outside,
      constantStep_encoded_outside target (first ^^^ second).toFin wire outside]

/-- A literal controlled constant mask is the same complete-state X action when enabled. -/
lemma controlledXorConstantStep_eq_selected (control : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (separate : ∀ index, control.wire ≠ (target.bit index).wire) (state : Data) :
    controlledXorConstantStep control target constant separate state =
      if control.get state then xorConstantStep target constant state else state := by
  unfold controlledXorConstantStep controlledXorConstantGates xorConstantStep xorConstantGates
  generalize constantOneIndices constant = indices
  induction indices generalizing state with
  | nil => cases control.get state <;> rfl
  | cons index rest ih =>
      have retained : control.get ((target.bit index).flip state) = control.get state :=
        get_flip_of_wire_ne _ _ (Ne.symm (separate index)) state
      change GateSpec.stepList (rest.map fun bit => .cnot control (target.bit bit) (separate bit))
        (cnotStep control (target.bit index) state) = _
      cases selected : control.get state
      · simp only [cnotStep, selected, Bool.false_eq_true, if_false]
        rw [ih]
        simp only [selected, Bool.false_eq_true, if_false]
      · simp only [cnotStep, selected, if_true]
        rw [ih, retained]
        simp only [selected, if_true]
        rfl

end

end QuantumAlg.EncodedBit.Word
