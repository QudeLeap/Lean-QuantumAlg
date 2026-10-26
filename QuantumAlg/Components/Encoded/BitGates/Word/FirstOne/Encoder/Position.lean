/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder
import all QuantumAlg.Util.Nat.FixedWidth.PriorityPrefix.Characterization

/-! # The original ordered marked position equals width minus the original binary size -/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- A most-significant-first original source has exactly the independent numeric first-one value. -/
lemma firstPosition_eq_firstOne (state : Data) (word : BitVec count)
    (source : ∀ index, (frame.source.bit index).get state = word.getMsbD index.val) :
    frame.firstPosition state = NatFixedWidth.PriorityPrefix.firstOne word := by
  apply NatFixedWidth.PriorityPrefix.firstOne_unique word
  · exact ListPriority.Tree.position_le _
  · intro before earlier
    have fits : before < count := Nat.lt_of_lt_of_le earlier (ListPriority.Tree.position_le _)
    rw [← source ⟨before, fits⟩]
    exact ListPriority.Tree.before_position
      (fun label => (frame.source.bit label).get state) ⟨before, fits⟩ earlier
  · intro present
    rw [← source ⟨frame.firstPosition state, present⟩]
    exact ListPriority.Tree.at_position (fun label => (frame.source.bit label).get state) present

end

end QuantumAlg.EncodedBit.FirstOne.Frame
