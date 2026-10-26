/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Frame

/-!
# One-hot invariant of the actual doubled unary ranges

Each address-controlled stage keeps the token in the old range or moves it
to the new range. The proof reads the same actual Toffoli word and parallel
CNOT layer; all positions outside that stage retain their original values.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnaryFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma old_half (index label span : Nat) (indexBefore : index < span)
    (_labelBefore : label < span) (chosen : Bool) :
    (decide (index = label) && !chosen) =
      decide (index = if chosen then span + label else label) := by
  cases chosen
  · exact Bool.and_true _
  · change (decide (index = label) && false) = decide (index = span + label)
    rw [Bool.and_false]
    symm
    exact decide_eq_false (by omega)

private lemma fresh_half (index label span : Nat) (labelBefore : label < span)
    (chosen : Bool) :
    (chosen && decide (index = label)) =
      decide (span + index = if chosen then span + label else label) := by
  cases chosen
  · rw [Bool.false_and]
    change false = decide (span + index = label)
    symm
    exact decide_eq_false (by omega)
  · rw [Bool.true_and]
    change decide (index = label) = decide (span + index = span + label)
    exact Bool.decide_congr (by omega)

private lemma outside_halves (index label span : Nat) (after : 2 * span ≤ index)
    (labelBefore : label < span) (chosen : Bool) :
    decide (index = label) =
      decide (index = if chosen then span + label else label) := by
  have oldDifferent : index ≠ label := by omega
  rw [decide_eq_false oldDifferent]
  symm
  apply decide_eq_false
  split <;> omega

private lemma nextLabel_val (depth : Nat) (present : depth < width)
    (label : Fin (2 ^ width)) (before : label.val < 2 ^ depth) (chosen : Bool) :
    (nextLabel depth present label before chosen).val =
      if chosen then 2 ^ depth + label.val else label.val := by
  cases chosen <;> rfl

/-- The same actual unary stage preserves a unique selected token and advances its address. -/
lemma stage_oneHot (frame : UnaryFrame encoding width) (depth : Nat) (present : depth < width)
    (label : Fin (2 ^ width)) (before : label.val < 2 ^ depth) (state : Data)
    (oneHot : frame.OneHot label state) :
    frame.OneHot (nextLabel depth present label before
      ((frame.address ⟨depth, present⟩).get state)) ((frame.stage depth present).step state) := by
  intro index
  by_cases old : index.val < 2 ^ depth
  · let relative : Fin (2 ^ depth) := ⟨index.val, old⟩
    have same : oldIndex depth present relative = index := Fin.ext rfl
    have value := frame.stage_get_old depth present label before state oneHot relative
    rw [same] at value
    rw [value]
    simp only [Fin.ext_iff]
    rw [nextLabel_val]
    exact old_half _ _ _ old before _
  · by_cases fresh : index.val < 2 * 2 ^ depth
    · let relative : Fin (2 ^ depth) := ⟨index.val - 2 ^ depth, by omega⟩
      have same : freshIndex depth present relative = index := by
        apply Fin.ext
        dsimp only [freshIndex, relative, Fin.val_mk]
        omega
      have value := frame.stage_get_fresh depth present label before state oneHot relative
      rw [same] at value
      rw [value]
      simp only [Fin.ext_iff]
      rw [nextLabel_val]
      have sameValue : index.val = 2 ^ depth + relative.val :=
        (congrArg Fin.val same).symm
      rw [sameValue]
      exact fresh_half _ _ _ before _
    · rw [frame.stage_get_after depth present index (by omega) state, oneHot]
      simp only [Fin.ext_iff]
      rw [nextLabel_val]
      exact outside_halves _ _ _ (by omega) before _

end

end QuantumAlg.EncodedBit.WindowLookup.UnaryFrame
