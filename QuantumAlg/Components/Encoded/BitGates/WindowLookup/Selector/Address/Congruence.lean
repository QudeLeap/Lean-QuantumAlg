/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address

/-!
# Original address decoding depends only on its original address bits

The same symbolic interval decoder returns the same finite label whenever
its original address readouts agree. All widths and intervals, including
empty intervals, stay symbolic; no basis or address tree is expanded.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Other coordinates cannot change a decoder whose original address readouts are unchanged. -/
lemma addressLabelAt_congr (frame : SelectorFrame encoding width) (first second : Data)
    (reads : ∀ index, (frame.address index).get first = (frame.address index).get second)
    (remaining depth : Nat) (fits : depth + remaining = width)
    (offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    frame.addressLabelAt remaining depth fits offset bounded first =
      frame.addressLabelAt remaining depth fits offset bounded second := by
  induction remaining generalizing depth offset with
  | zero => rfl
  | succ remaining ih =>
      have read : (frame.addressAt depth (by omega)).get first =
          (frame.addressAt depth (by omega)).get second := reads _
      dsimp only [addressLabelAt]
      rw [read]
      split <;> exact ih _ _ _ _

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
