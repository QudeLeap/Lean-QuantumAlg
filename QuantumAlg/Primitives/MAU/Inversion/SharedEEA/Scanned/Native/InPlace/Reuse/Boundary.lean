/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse.Words
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers.BitExt

/-!
# Complete reused source boundary from actual saved A and reset Y

The caller supplies physical readout facts: Y was actually reset, the
saved A is arbitrary, and every other original source and pool bit was
retained. These facts determine the entire source label, including all
three original padding positions and every small history field. The
saved-word argument of the reused program is the reversed numerical A
value. No metadata equality is inferred from a payload-only invariant.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse

noncomputable section

open BinaryLabelEncoding

/-- Actual reset and complete complement preservation fix the full zero-work source frame. -/
lemma grouping_saved_reset (width : Nat) (base : Scanned.Data width)
    (state : OutputCopy.Data width)
    (baseZero : ∀ index : Fin width, base.1.firstWord.getMsbD index.val = false)
    (retained : ∀ bit : EncodedBit (SharedEEA.encoding width), width ≤ bit.wire.val →
      bit.get state.1.1 = bit.get base.1)
    (pool : state.1.2 = base.2) (reset : state.2 = 0) :
    (placement width).grouping state = (base, reverseWord (largeWord state)) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Registers.eq_of_bit_get_eq
      intro bit
      by_cases outside : width ≤ bit.wire.val
      · exact (grouping_original_read width state bit outside).trans (retained bit outside)
      · have within : bit.wire.val < width := by omega
        let index : Fin width := ⟨bit.wire.val, within⟩
        have same : bit = firstWordBit width ⟨index.val, by omega⟩ := by
          apply EncodedBit.eq_of_wire_eq
          apply Fin.ext
          rw [firstWordBit_wire]
        rw [same, firstWordBit_get, firstWordBit_get]
        change ((placement width).grouping state).1.1.firstWord.getMsbD index.val =
          base.1.firstWord.getMsbD index.val
        rw [grouping_large_bit width state index, reset, baseZero index]
        change (0 : Fin (2 ^ width)).val.testBit
          (WireAddress.bitIndex index).val = false
        rw [Fin.val_zero]
        exact Nat.zero_testBit _
    · exact (grouping_pool width state).trans pool
  · exact grouping_numerator width state

/-- The same actual readouts identify the complete inverse-grouped boundary used by the program. -/
lemma saved_reset_eq_grouping_symm (width : Nat) (base : Scanned.Data width)
    (state : OutputCopy.Data width)
    (baseZero : ∀ index : Fin width, base.1.firstWord.getMsbD index.val = false)
    (retained : ∀ bit : EncodedBit (SharedEEA.encoding width), width ≤ bit.wire.val →
      bit.get state.1.1 = bit.get base.1)
    (pool : state.1.2 = base.2) (reset : state.2 = 0) :
    state = (placement width).grouping.symm (base, reverseWord (largeWord state)) := by
  have actual := congrArg (placement width).grouping.symm
    (grouping_saved_reset width base state baseZero retained pool reset)
  simpa only [Equiv.symm_apply_apply] using actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.WorkspaceReuse
