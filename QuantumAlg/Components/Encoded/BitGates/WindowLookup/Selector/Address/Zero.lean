/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Flags

/-!
# Original zero-address predicate of the symbolic selector

The real complete decoder selects the left endpoint precisely when all
original bits of the remaining interval are zero. Width, interval and
original input stay symbolic, including the empty interval.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The original decoder selects its left endpoint exactly on the original all-zero interval. -/
lemma addressLabelAt_eq_offset_iff (frame : SelectorFrame encoding width)
    (remaining depth : Nat) (fits : depth + remaining = width)
    (offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    (frame.addressLabelAt remaining depth fits offset bounded state).val = offset ↔
      ∀ index : Fin width, depth ≤ index.val → index.val < depth + remaining →
        (frame.address index).get state = false := by
  induction remaining generalizing depth offset with
  | zero =>
      change offset = offset ↔ _
      exact ⟨fun _ _ lower upper => by omega, fun _ => rfl⟩
  | succ remaining ih =>
      dsimp only [addressLabelAt]
      split
      next selected =>
        constructor
        · intro impossible
          have interval := StreamedSelector.addressLabelAt_bounds frame remaining (depth + 1)
            (by omega) (offset + 2 ^ remaining) (right_bound bounded) state
          have positive := Nat.two_pow_pos remaining
          omega
        · intro allZero
          have current := allZero ⟨depth, by omega⟩
            (by change depth ≤ depth; omega)
            (by change depth < depth + (remaining + 1); omega)
          change (frame.addressAt depth (by omega)).get state = false at current
          rw [selected] at current
          contradiction
      next unselected =>
        rw [ih (depth + 1) (by omega) offset (left_bound bounded)]
        constructor
        · intro later index lower upper
          by_cases first : index.val = depth
          · have same : index = ⟨depth, by omega⟩ := Fin.ext first
            exact (congrArg (fun bit : Fin width => (frame.address bit).get state) same).trans
              (Bool.eq_false_iff.mpr unselected)
          · exact later index (by omega) (by omega)
        · intro allZero index lower upper
          exact allZero index (by omega) (by omega)

/-- The complete original address is zero exactly when every original address bit is zero. -/
lemma addressLabelAt_zero_iff (frame : SelectorFrame encoding width) (state : Data) :
    (frame.addressLabelAt width 0 (by omega) 0 (by omega) state).val = 0 ↔
      ∀ index : Fin width, (frame.address index).get state = false := by
  rw [addressLabelAt_eq_offset_iff]
  exact ⟨fun known index => known index (Nat.zero_le _)
      (by simpa only [Nat.zero_add] using index.isLt),
    fun known index _ _ => known index⟩

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
