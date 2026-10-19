/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Util.Nat.Binary.Arithmetic

/-!
# Local actions of the TTK carry network

The TTK adder stores each intermediate carry in an operand bit. Its forward
Toffoli acts on readouts `b xor a`, `a xor c`, and `next xor a`; its reverse
Toffoli restores `next xor a`. These statements describe actual addressed
primitive gates, without a separate carry register [TTK09,
qic-loglogaddition-quant.tex:262-283,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma carryXorIdentity (a b c z : Bool) :
    ((z ^^ a) ^^ ((b ^^ a) && (a ^^ c))) = (z ^^ Bool.carry a b c) := by
  cases a <;> cases b <;> cases c <;> cases z <;> rfl

private lemma reverseCarryXorIdentity (a b c z : Bool) :
    ((z ^^ Bool.carry a b c) ^^ ((b ^^ a) && (a ^^ c))) = (z ^^ a) := by
  cases a <;> cases b <;> cases c <;> cases z <;> rfl

/-- The single actual Toffoli used by one TTK carry-propagation step. -/
def carryGate (right left next : EncodedBit encoding)
    (hrl : right.wire ≠ left.wire) (hrn : right.wire ≠ next.wire)
    (hln : left.wire ≠ next.wire) : EncodedBit.GateSpec encoding :=
  .toffoli right left next hrl hrn hln

/-- One TTK carry Toffoli replaces the stored input xor by the next carry xor. -/
lemma ttkCarryGate_target
    (right left next : EncodedBit encoding)
    (hrl : right.wire ≠ left.wire) (hrn : right.wire ≠ next.wire)
    (hln : left.wire ≠ next.wire) (state : Data) (a b c z : Bool)
    (hr : right.get state = (b ^^ a))
    (hl : left.get state = (a ^^ c))
    (hn : next.get state = (z ^^ a)) :
    next.get ((carryGate right left next hrl hrn hln).step state) =
      (z ^^ Bool.carry a b c) := by
  change next.get (EncodedBit.toffoliStep right left next state) = _
  rw [EncodedBit.toffoliStep_get_target, hr, hl, hn]
  exact carryXorIdentity a b c z

/-- The same Toffoli reverses the operand-encoded carry, for arbitrary bits. -/
lemma ttkCarryGate_reverse_target
    (right left next : EncodedBit encoding)
    (hrl : right.wire ≠ left.wire) (hrn : right.wire ≠ next.wire)
    (hln : left.wire ≠ next.wire) (state : Data) (a b c z : Bool)
    (hr : right.get state = (b ^^ a))
    (hl : left.get state = (a ^^ c))
    (hn : next.get state = (z ^^ Bool.carry a b c)) :
    next.get ((carryGate right left next hrl hrn hln).step state) =
      (z ^^ a) := by
  change next.get (EncodedBit.toffoliStep right left next state) = _
  rw [EncodedBit.toffoliStep_get_target, hr, hl, hn]
  exact reverseCarryXorIdentity a b c z

/-- A carry Toffoli preserves its two controls exactly. -/
lemma ttkCarryGate_controls
    (right left next : EncodedBit encoding)
    (hrl : right.wire ≠ left.wire) (hrn : right.wire ≠ next.wire)
    (hln : left.wire ≠ next.wire) (state : Data) :
    right.get ((carryGate right left next hrl hrn hln).step state) =
        right.get state ∧
      left.get ((carryGate right left next hrl hrn hln).step state) =
        left.get state := by
  constructor
  · exact EncodedBit.toffoliStep_get_of_target_ne right left next right
      (Ne.symm hrn) state
  · exact EncodedBit.toffoliStep_get_of_target_ne right left next left
      (Ne.symm hln) state

/-- The reverse sweep changes the right operand's xor from its addend to its
incoming carry; it uses the carry already stored in the left operand bit. -/
lemma ttkSumExtraction_target
    (left right : EncodedBit encoding) (hlr : left.wire ≠ right.wire)
    (state : Data) (a b c : Bool)
    (hl : left.get state = (a ^^ c))
    (hr : right.get state = (b ^^ a)) :
    right.get ((EncodedBit.GateSpec.cnot left right hlr).step state) =
      (b ^^ c) := by
  change right.get (EncodedBit.cnotStep left right state) = _
  rw [EncodedBit.cnotStep_get_target, hl, hr]
  cases a <;> cases b <;> cases c <;> rfl

end

end QuantumAlg.MAU.Addition.TTK
