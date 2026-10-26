/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary

/-!
# Original address and prefix invariants of the actual table action

These laws permit an original address bit to serve as the top traversal
enable. Its temporary X operations do not inspect or alter the remaining
address, and every unused prefix remains clean.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width wordWidth : Nat}

namespace SelectorFrame

/-- Decoding depends on exactly the original address fields, in their original order. -/
lemma addressLabelAt_congr (frame : SelectorFrame encoding width) (first second : Data)
    (agree : ∀ index, (frame.address index).get first = (frame.address index).get second)
    (remaining depth : Nat) (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    frame.addressLabelAt remaining depth fits offset bounded first =
      frame.addressLabelAt remaining depth fits offset bounded second := by
  induction remaining generalizing depth offset with
  | zero => rfl
  | succ remaining ih =>
      dsimp only [addressLabelAt]
      rw [show (frame.addressAt depth (by omega)).get first =
        (frame.addressAt depth (by omega)).get second from agree _]
      split
      · exact ih _ (by omega) _ (right_bound bounded)
      · exact ih _ (by omega) _ (left_bound bounded)

/-- Flipping the existing enable leaves the complete remaining address unchanged. -/
lemma addressLabelAt_flip_enable (frame : SelectorFrame encoding width)
    (remaining depth : Nat) (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    frame.addressLabelAt remaining depth fits offset bounded
        ((frame.stack ⟨0, by omega⟩).flip state) =
      frame.addressLabelAt remaining depth fits offset bounded state := by
  apply frame.addressLabelAt_congr
  intro index
  exact EncodedBit.get_flip_of_wire_ne _ _ (Ne.symm (frame.separate index _)) state

/-- A temporary X on the existing enable preserves all initially clean prefix positions. -/
lemma cleanFrom_flip_enable (frame : SelectorFrame encoding width) (state : Data)
    (clean : frame.CleanFrom 0 state) :
    frame.CleanFrom 0 ((frame.stack ⟨0, by omega⟩).flip state) := by
  intro index later
  rw [EncodedBit.get_flip_of_wire_ne]
  · exact clean index later
  · intro equal
    have values := congrArg Fin.val (frame.stackDistinct equal)
    change 0 = index.val + 1 at values
    omega

end SelectorFrame

namespace LookupTarget

variable {frame : SelectorFrame encoding width}

/-- The table XOR retains the complete original address label. -/
lemma xor_addressLabel (target : LookupTarget frame wordWidth)
    (constant : Fin (2 ^ wordWidth)) (state : Data) :
    frame.addressLabelAt width 0 (by omega) 0 (by omega)
        (Word.xorConstantStep target.word constant state) =
      frame.addressLabelAt width 0 (by omega) 0 (by omega) state :=
  frame.addressLabelAt_congr _ _ (fun index => (target.xor_preserves constant).1 index state)
    _ _ _ _ _

/-- Constant XOR commutes with an original bit flip, as an exact full-data action. -/
lemma xor_flip (target : LookupTarget frame wordWidth) (constant : Fin (2 ^ wordWidth))
    (bit : EncodedBit encoding) (state : Data) :
    Word.xorConstantStep target.word constant (bit.flip state) =
      bit.flip (Word.xorConstantStep target.word constant state) := by
  rw [← constantMaskTarget_flip target.word constant (bit.flip state),
    ← constantMaskTarget_flip target.word constant state]
  exact flipBits_flip _ _ state

end LookupTarget

end

end QuantumAlg.EncodedBit.WindowLookup
