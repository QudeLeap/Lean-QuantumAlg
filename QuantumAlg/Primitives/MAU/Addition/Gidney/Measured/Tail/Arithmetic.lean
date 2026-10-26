/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Semantics
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Offset
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Arithmetic

/-!
# Recovery of the original carries from the actual complemented streaming sum

The complete addressed target word is the finite selected sum. The actual
native X word complements that sum while retaining the coherent control.
Consequently the actual native dirty-carry word recovers precisely the
original carries, including for zero control [G25, main.tex:209-239,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The first actual native complement follows the complete physical streaming word. -/
def complementedStream (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data) : Data :=
  stepList layout.complementGates (wordLabel (layout.streamingWord wide constant) state)

/-- The actual native target complement retains every other original encoded bit. -/
lemma complementGates_other (layout : Layout encoding width) (observed : EncodedBit encoding)
    (different : ∀ index, (layout.target index).wire ≠ observed.wire) (state : Data) :
    observed.get (stepList layout.complementGates state) = observed.get state := by
  rw [complementGates_eq_word]
  exact Word.complementGates_get_other layout.targetPorts observed different state

/-- Reading the actual complete streaming output gives exactly finite-word selected addition. -/
lemma streamingWord_targetWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.targetWord (wordLabel (layout.streamingWord wide constant) initial) =
      layout.targetWord initial + layout.selectedOffsetWord constant initial := by
  apply BitVec.eq_of_getLsbD_eq
  intro index inside
  change (layout.targetWord (wordLabel (layout.streamingWord wide constant) initial)).toNat.testBit
    index = _
  rw [targetWord_bit _ _ _ inside, streamingWord_target_get layout wide constant initial clean]
  change _ = (layout.targetWord initial + layout.selectedOffsetWord constant initial).toNat.testBit
    index
  rw [BitVec.toNat_add, Nat.testBit_mod_two_pow, decide_eq_true inside, Bool.true_and,
    Nat.BinaryArithmetic.testBit_add_eq_xor3, targetWord_bit _ _ _ inside, selectedOffsetWord_bit]
  rfl

/-- The same literal native X word is the full finite-word complement at the actual ports. -/
lemma complementGates_targetWord (layout : Layout encoding width) (state : Data) :
    layout.targetWord (stepList layout.complementGates state) = ~~~layout.targetWord state := by
  apply BitVec.eq_of_getLsbD_eq
  intro index inside
  rw [BitVec.getLsbD_not, decide_eq_true inside, Bool.true_and]
  change (layout.targetWord (stepList layout.complementGates state)).toNat.testBit index =
    !(layout.targetWord state).toNat.testBit index
  rw [targetWord_bit _ _ _ inside, targetWord_bit _ _ _ inside, complementGates_target]

/-- The carry-repair input is exactly the complemented original selected sum. -/
lemma complementedStream_targetWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.targetWord (layout.complementedStream wide constant initial) =
      ~~~(layout.targetWord initial + layout.selectedOffsetWord constant initial) := by
  rw [complementedStream, complementGates_targetWord,
    streamingWord_targetWord layout wide constant initial clean]

/-- The carry-repair input retains the same original coherent control. -/
lemma complementedStream_control_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.control.get (layout.complementedStream wide constant initial) =
      layout.control.get initial := by
  rw [complementedStream, complementGates_other layout layout.control
    (fun index => (layout.control_target_ne index).symm),
    streamingWord_control_get layout wide constant initial clean]

/-- The actual native carry recurrence on the complemented stream is the original carry. -/
lemma complementedStream_carryValues (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (count : Nat) (bounded : count ≤ width - 2) :
    layout.carryLayout.carryValues (constant.setWidth (width - 2))
        (layout.complementedStream wide constant initial) count =
      layout.carryInto constant initial count := by
  rw [carryValues_eq_carryInto layout constant _ count bounded, carryInto,
    complementedStream_targetWord layout wide constant initial clean]
  have sameOffset : layout.selectedOffsetWord constant
      (layout.complementedStream wide constant initial) =
        layout.selectedOffsetWord constant initial := by
    unfold selectedOffsetWord
    rw [complementedStream_control_get layout wide constant initial clean]
  rw [sameOffset, carry_complemented_sum _ _ count (by omega)]
  rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
