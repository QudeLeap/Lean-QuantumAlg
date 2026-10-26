/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail.Arithmetic

/-!
# Full original-port behavior of the complete measured constant-adder word

The source-order repair restores every arbitrary dirty port, retains the
original coherent control, and returns both original helpers physically to
zero. Every original target bit is the selected finite-word sum
[G25, main.tex:209-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual measured-adder label follows the complete stream and the same native repair word. -/
lemma adderWord_label (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data) :
    wordLabel (layout.adderWord wide constant) state =
      stepList layout.complementGates
        (stepList (layout.carryLayout.gates (constant.setWidth (width - 2)))
          (layout.complementedStream wide constant state)) := by
  rw [adderWord_eq_stream_tail, wordLabel_append, tailWord_label]
  rfl

/-- Every original target bit is the selected sum after both actual native complements. -/
lemma adderWord_target_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) (index : Fin width) :
    (layout.target index).get (wordLabel (layout.adderWord wide constant) initial) =
      (layout.targetWord initial + layout.selectedOffsetWord constant initial).getLsbD index.val :=
  by
  rw [adderWord_label, complementGates_target]
  have preserved := CarryLayout.gates_preserves (layout.target index).get layout.carryLayout
    (constant.setWidth (width - 2)) (fun output =>
      get_flip_of_wire_ne (layout.dirty output) (layout.target index)
        (layout.target_dirty_ne index output).symm)
    (layout.complementedStream wide constant initial)
  rw [preserved, complementedStream, complementGates_target, Bool.not_not]
  have sumWord := streamingWord_targetWord layout wide constant initial clean
  have bit := congrArg (fun word : BitVec width => word.toNat.testBit index.val) sumWord
  rw [targetWord_bit _ _ _ index.isLt] at bit
  exact bit

/-- Every arbitrary original dirty carry output is restored exactly by the actual native tail. -/
lemma adderWord_dirty_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (index : Fin (width - 2)) :
    (layout.dirty index).get (wordLabel (layout.adderWord wide constant) initial) =
      (layout.dirty index).get initial := by
  rw [adderWord_label, complementGates_other layout (layout.dirty index)
    (fun target => layout.target_dirty_ne target index)]
  have actual := CarryLayout.gates_output_get layout.carryLayout
    (constant.setWidth (width - 2)) (layout.complementedStream wide constant initial) index
  change (layout.dirty index).get _ =
    ((layout.dirty index).get (layout.complementedStream wide constant initial) ^^
      layout.carryLayout.carryValues (constant.setWidth (width - 2))
        (layout.complementedStream wide constant initial) (index.val + 1)) at actual
  rw [actual, complementedStream_carryValues layout wide constant initial clean _ (by omega),
    complementedStream, complementGates_other layout (layout.dirty index)
      (fun target => layout.target_dirty_ne target index),
    streamingWord_dirty_get layout wide constant initial clean, Bool.xor_assoc, Bool.xor_self,
    Bool.xor_false]

/-- Both original physical clean systems finish at zero after every retained record. -/
lemma adderWord_clean_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) (helper : Fin 2) :
    (layout.clean helper).get (wordLabel (layout.adderWord wide constant) initial) = false := by
  rw [adderWord_label, complementGates_other layout (layout.clean helper)
    (fun target => layout.target_clean_ne target helper)]
  have preserved := CarryLayout.gates_preserves (layout.clean helper).get layout.carryLayout
    (constant.setWidth (width - 2)) (fun output =>
      get_flip_of_wire_ne (layout.dirty output) (layout.clean helper)
        (layout.dirty_clean_ne output helper))
    (layout.complementedStream wide constant initial)
  rw [preserved, complementedStream, complementGates_other layout (layout.clean helper)
    (fun target => layout.target_clean_ne target helper),
    streamingWord_clean_get layout wide constant initial clean]

/-- The complete actual measured word retains the arbitrary original coherent control. -/
lemma adderWord_control_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.control.get (wordLabel (layout.adderWord wide constant) initial) =
      layout.control.get initial := by
  rw [adderWord_label, complementGates_other layout layout.control
    (fun target => (layout.control_target_ne target).symm)]
  have preserved := CarryLayout.gates_control_get layout.carryLayout
    (constant.setWidth (width - 2)) (layout.complementedStream wide constant initial)
  change layout.control.get _ = layout.control.get _ at preserved
  exact preserved.trans (complementedStream_control_get layout wide constant initial clean)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
