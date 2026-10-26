/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant.Final

/-!
# Original dirty-carry outputs and both physically reset final helpers

After the final actual row, every dirty port contains its arbitrary original
value xored with the original arithmetic carry. Both original helper systems
are physically zero. The later native carry word restores the dirty outputs
[G25, main.tex:239-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {layout : Layout encoding width} {constant : BitVec width} {initial current : Data}

/-- Every final dirty output retains its arbitrary original bit xored with its original carry. -/
lemma prefixInvariant_final_dirty (wide : 2 ≤ width) (index : Fin (width - 1))
    (final : ¬ index.val + 1 < width - 1)
    (invariant : layout.PrefixInvariant constant initial current index.val)
    (observed : Fin (width - 2)) :
    (layout.dirty observed).get
        (wordLabel (layout.streamingStep wide constant index) current) =
      ((layout.dirty observed).get initial ^^
        layout.carryInto constant initial (observed.val + 1)) := by
  have last : index.val + 1 = width - 1 := by have inside := index.isLt; omega
  by_cases same : observed.val + 1 = index.val
  · have positive : 0 < index.val := by omega
    have outputEq : (⟨index.val - 1, by omega⟩ : Fin (width - 2)) = observed := by
      apply Fin.ext
      change index.val - 1 = observed.val
      omega
    have previous : index.val - 1 + 1 = index.val := by omega
    rw [← outputEq, streamingStep_dirty layout wide constant index positive, invariant.dirty,
      prefixInvariant_incoming_helper invariant, previous,
      if_neg (Nat.lt_irrefl index.val), Bool.xor_false]
  · have different : 0 < index.val → index.val - 1 ≠ observed.val := by
      intro positive equal
      apply same
      omega
    rw [streamingStep_dirty_other layout wide constant index observed different,
      invariant.dirty, if_pos (by
        have inside := observed.isLt
        omega : observed.val + 1 < index.val)]

/-- Both original physical clean helpers are zero after the final actual row. -/
lemma prefixInvariant_final_clean (wide : 2 ≤ width) (index : Fin (width - 1))
    (final : ¬ index.val + 1 < width - 1)
    (invariant : layout.PrefixInvariant constant initial current index.val) (helper : Fin 2) :
    (layout.clean helper).get
      (wordLabel (layout.streamingStep wide constant index) current) = false := by
  by_cases same : helper.val = index.val % 2
  · have helperEq : layout.clean helper = layout.carryHelper index.val := by
      unfold carryHelper
      congr 1
      exact Fin.ext same
    rw [helperEq, streamingStep_incoming layout wide constant index current]
    by_cases positive : 0 < index.val
    · rw [if_pos positive]
    · have first : index.val = 0 := by omega
      rw [if_neg positive, prefixInvariant_incoming_helper invariant, first]
      rfl
  · have preserved : (layout.clean helper).get
          (wordLabel (layout.streamingStep wide constant index) current) =
        (layout.clean helper).get current := by
      apply streamingStep_preserves layout wide constant index (layout.clean helper).get
      · rw [nextCarry, if_neg final]
        exact get_flip_of_wire_ne _ _ (layout.target_clean_ne _ helper)
      · exact get_flip_of_wire_ne _ _ (layout.target_clean_ne _ helper)
      · intro _
        exact get_flip_of_wire_ne _ _ (layout.dirty_clean_ne _ helper)
      · intro _
        exact get_flip_of_wire_ne _ _ (layout.clean_clean_ne (fun equal =>
          same (congrArg (fun value : Fin 2 => value.val) equal).symm))
    rw [preserved, invariant.clean, if_neg same]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
