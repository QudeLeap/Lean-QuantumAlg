/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant.Rows
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant.Final.Workspace

/-!
# Original target sum, dirty carries and physical helpers of the full streaming word

The complete label is obtained from the actual chronological source rows.
Every original target, control and dirty value remains arbitrary; only the
two original helpers are assumed clean. The dirty values are restored by
the later measured-adder phase/carry/phase tail [G25, main.tex:209-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The final actual source row follows precisely the first width-minus-two chronological rows. -/
lemma streamingWord_label_final (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data) :
    wordLabel (layout.streamingWord wide constant) initial =
      wordLabel (layout.streamingStep wide constant ⟨width - 2, by omega⟩)
        (wordLabel (layout.streamingRows wide constant (width - 2) (by omega))
          (stepList (layout.offsetGates constant) initial)) := by
  rw [streamingWord_eq_rows]
  change wordLabel (layout.streamingRows wide constant (width - 1) le_rfl)
    (stepList (layout.offsetGates constant) initial) = _
  have actual := streamingRows_label_succ layout wide constant (width - 2) (by omega)
    (stepList (layout.offsetGates constant) initial)
  have countEq : width - 2 + 1 = width - 1 := by omega
  simpa only [countEq] using actual

/-- Every original target bit is exactly its selected finite-word addition sum bit. -/
lemma streamingWord_target_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) (observed : Fin width) :
    (layout.target observed).get (wordLabel (layout.streamingWord wide constant) initial) =
      (((layout.target observed).get initial ^^
        (constant.getLsbD observed.val && layout.control.get initial)) ^^
          layout.carryInto constant initial observed.val) := by
  rw [streamingWord_label_final]
  have invariant := streamingRows_prefixInvariant layout wide constant initial clean
    (width - 2) le_rfl
  exact prefixInvariant_final_target wide ⟨width - 2, by omega⟩
    (by change ¬ width - 2 + 1 < width - 1; omega) invariant observed

/-- Every arbitrary dirty value is xored with the matching original carry by the actual word. -/
lemma streamingWord_dirty_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (observed : Fin (width - 2)) :
    (layout.dirty observed).get (wordLabel (layout.streamingWord wide constant) initial) =
      ((layout.dirty observed).get initial ^^
        layout.carryInto constant initial (observed.val + 1)) := by
  rw [streamingWord_label_final]
  have invariant := streamingRows_prefixInvariant layout wide constant initial clean
    (width - 2) le_rfl
  exact prefixInvariant_final_dirty wide ⟨width - 2, by omega⟩
    (by change ¬ width - 2 + 1 < width - 1; omega) invariant observed

/-- Both original physical carry helpers end at zero in every retained branch label. -/
lemma streamingWord_clean_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) (helper : Fin 2) :
    (layout.clean helper).get (wordLabel (layout.streamingWord wide constant) initial) = false := by
  rw [streamingWord_label_final]
  have invariant := streamingRows_prefixInvariant layout wide constant initial clean
    (width - 2) le_rfl
  exact prefixInvariant_final_clean wide ⟨width - 2, by omega⟩
    (by change ¬ width - 2 + 1 < width - 1; omega) invariant helper

/-- The complete actual streaming word retains the same original coherent control label. -/
lemma streamingWord_control_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.control.get (wordLabel (layout.streamingWord wide constant) initial) =
      layout.control.get initial := by
  rw [streamingWord_label_final, streamingStep_control_get]
  exact (streamingRows_prefixInvariant layout wide constant initial clean
    (width - 2) le_rfl).control

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
