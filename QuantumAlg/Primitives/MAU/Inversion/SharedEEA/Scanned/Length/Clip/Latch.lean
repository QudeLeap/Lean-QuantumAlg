/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Active
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.BitVector

/-! # Exact actual validity-latch readout and retained physical complement -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The real negative-control word toggles the arbitrary incoming high address value. -/
lemma activeGates_get (width : Nat) (state : Data width) :
    (LengthCopy.active width true).get (GateSpec.stepList (activeGates width) state) =
      ((LengthCopy.active width true).get state ^^
        (state.1.control && !(highBit width).get state)) := by
  rw [activeGates_step]
  unfold predicateFlip
  cases selected : state.1.control && !(highBit width).get state <;>
    simp only [selected, Bool.false_eq_true, if_false, if_true, Bool.xor_false,
      Bool.xor_true, EncodedBit.get_flip_self]

/-- Every other actual physical position retains its full original value. -/
lemma activeGates_get_observed (width : Nat) (state : Data width)
    (observed : EncodedBit (encoding width))
    (outside : (LengthCopy.active width true).wire ≠ observed.wire) :
    observed.get (GateSpec.stepList (activeGates width) state) = observed.get state := by
  rw [activeGates_step]
  unfold predicateFlip
  split
  · exact EncodedBit.get_flip_of_wire_ne _ _ outside state
  · rfl

/-- The existing high prefix gives exactly the native whole-capacity validity predicate. -/
lemma highBit_get (width : Nat) (state : Data width) :
    (highBit width).get state = decide (2 ^ width.size ≤ state.2.2.1.toNat) := by
  change (prefixBit width ⟨0, by unfold ScanMetadata.addressWidth; omega⟩).get state = _
  rw [prefixBit_get]
  exact high_get state.2.2.1

/-- The complete prefix, including the high validity bit, survives the real latch word. -/
lemma activeGates_prefix (width : Nat) (state : Data width) :
    (GateSpec.stepList (activeGates width) state).2.2.1 = state.2.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := activeGates_get_observed width state (prefixBit width ⟨index, within⟩)
    (address_prefix_ne width _ _)
  simpa only [prefixBit_get] using actual

/-- All original EEA fields, including retained Ctrl and arbitrary Iter, remain unchanged. -/
lemma activeGates_original (width : Nat) (state : Data width)
    (observed : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width observed).get (GateSpec.stepList (activeGates width) state) =
      (sourceBit width observed).get state :=
  activeGates_get_observed width state _ (source_address_ne width observed _).symm

/-- A clean high address becomes exactly the real retained Ctrl-and-validity flag. -/
lemma activeGates_get_clean (width : Nat) (state : Data width)
    (zero : (LengthCopy.active width true).get state = false) :
    (LengthCopy.active width true).get (GateSpec.stepList (activeGates width) state) =
      (state.1.control && !(decide (2 ^ width.size ≤ state.2.2.1.toNat))) := by
  rw [activeGates_get, zero, Bool.false_xor, highBit_get]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
