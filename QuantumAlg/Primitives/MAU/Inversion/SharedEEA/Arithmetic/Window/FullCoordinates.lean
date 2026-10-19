/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Encoding

/-!
# Every grouped arithmetic coordinate has its original physical address

In addition to both TTK windows and Sign, the placement includes every
prefix, suffix, length and remaining flag. In particular the Ctrl and
arbitrary borrowed Iter wires are mapped to their actual original source
positions. The injection and range proof cover the complete binary
frame, including empty windows and empty prefix or suffix regions
[LYL+26, sec_EEA/sub_regshare.tex:16-26,263-278].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowFullCoordinates

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowEncoding

/-- Original address of every explicitly retained complementary coordinate. -/
def complementPhysicalIndex {width : Nat} (window : Window width) (index : Nat) : Nat :=
  if index < window.above then index
  else if index < window.above + window.below then window.length + index
  else if index < 2 * window.above + window.below then
    width + 3 + (index - (window.above + window.below))
  else if index < 2 * (window.above + window.below) then
    width + 3 + window.length + (index - (window.above + window.below))
  else if index < 2 * (window.above + window.below) + 4 * width.size + 2 then
    2 * (width + 3) + (index - 2 * (window.above + window.below))
  else 2 * (width + 3) + 1 + (index - 2 * (window.above + window.below))

/-- Map the complete native grouped frame back to the original physical source frame. -/
def physicalIndex {width : Nat} (window : Window width) (index : Nat) : Nat :=
  if index < 2 * window.length + 1 then
    ArithmeticWindowCoordinates.physicalIndex window index
  else complementPhysicalIndex window (index - (2 * window.length + 1))

private lemma grouped_width {width : Nat} (window : Window width) :
    (groupedEncoding window).width = 2 * window.length + 1 +
      (2 * (window.above + window.below) + 4 * width.size + 4) := by
  rw [groupedEncoding_width, encoding_width]
  have complete := window.complete
  omega

/-- Every already checked TTK source, target and Sign address is retained by the full map. -/
lemma physicalIndex_focus {width : Nat} (window : Window width)
    (index : Fin (2 * window.length + 1)) :
    physicalIndex window index.val = ArithmeticWindowCoordinates.physicalIndex window index.val :=
  if_pos index.isLt

private lemma complement_injective {width : Nat} (window : Window width) :
    Function.Injective
      (fun index : Fin (2 * (window.above + window.below) + 4 * width.size + 4) =>
        complementPhysicalIndex window index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  have complete := window.complete
  change complementPhysicalIndex window left.val =
    complementPhysicalIndex window right.val at same
  unfold complementPhysicalIndex at same
  split_ifs at same <;> omega

private lemma focus_ne_complement {width : Nat} (window : Window width)
    (focus : Fin (2 * window.length + 1))
    (rest : Fin (2 * (window.above + window.below) + 4 * width.size + 4)) :
    ArithmeticWindowCoordinates.physicalIndex window focus.val ≠
      complementPhysicalIndex window rest.val := by
  intro same
  have focusBound := focus.isLt
  have restBound := rest.isLt
  have complete := window.complete
  unfold ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex at same
  split_ifs at same <;> omega

/-- The complete actual grouping does not alias any two physical source wires. -/
lemma physicalIndex_injective {width : Nat} (window : Window width) :
    Function.Injective
      (fun index : Fin (groupedEncoding window).width => physicalIndex window index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  have total := grouped_width window
  change physicalIndex window left.val = physicalIndex window right.val at same
  unfold physicalIndex at same
  by_cases leftFocus : left.val < 2 * window.length + 1
  · rw [if_pos leftFocus] at same
    by_cases rightFocus : right.val < 2 * window.length + 1
    · rw [if_pos rightFocus] at same
      exact congrArg (fun index : Fin (2 * window.length + 1) => index.val)
        (ArithmeticWindowCoordinates.physicalIndex_injective window
          (a₁ := ⟨left.val, leftFocus⟩) (a₂ := ⟨right.val, rightFocus⟩) same)
    · rw [if_neg rightFocus] at same
      exact False.elim (focus_ne_complement window ⟨left.val, leftFocus⟩
        ⟨right.val - (2 * window.length + 1), by omega⟩ same)
  · rw [if_neg leftFocus] at same
    by_cases rightFocus : right.val < 2 * window.length + 1
    · rw [if_pos rightFocus] at same
      exact False.elim (focus_ne_complement window ⟨right.val, rightFocus⟩
        ⟨left.val - (2 * window.length + 1), by omega⟩ same.symm)
    · rw [if_neg rightFocus] at same
      have values := congrArg
        (fun index : Fin (2 * (window.above + window.below) + 4 * width.size + 4) =>
          index.val)
        (complement_injective window
          (a₁ := ⟨left.val - (2 * window.length + 1), by omega⟩)
          (a₂ := ⟨right.val - (2 * window.length + 1), by omega⟩) same)
      change left.val - (2 * window.length + 1) =
        right.val - (2 * window.length + 1) at values
      omega

/-- All actual body and borrowed-control gates stay inside the original full frame. -/
lemma physicalIndex_within {width : Nat} (window : Window width)
    (index : Fin (groupedEncoding window).width) :
    physicalIndex window index.val < (encoding width).width := by
  rw [encoding_width]
  have bound := index.isLt
  have total := grouped_width window
  have complete := window.complete
  unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
  split_ifs <;> omega

/-- The complete address map, with each source and target coordinate in its native frame. -/
def wireMap {width : Nat} (window : Window width) :
    Fin (groupedEncoding window).width → Fin (encoding width).width :=
  fun index => ⟨physicalIndex window index.val, physicalIndex_within window index⟩

lemma wireMap_injective {width : Nat} (window : Window width) :
    Function.Injective (wireMap window) := by
  intro left right same
  exact physicalIndex_injective window (congrArg Fin.val same)

/-- Equal complete-frame widths make the verified injective address map onto. -/
lemma wireMap_surjective {width : Nat} (window : Window width) :
    Function.Surjective (wireMap window) := by
  let sameWidth := groupedEncoding_width window
  let endomap := fun index : Fin (groupedEncoding window).width =>
    Fin.cast sameWidth.symm (wireMap window index)
  have injective : Function.Injective endomap := by
    intro left right same
    apply wireMap_injective window
    exact Fin.cast_injective sameWidth.symm same
  intro target
  obtain ⟨source, same⟩ :=
    Finite.surjective_of_injective injective (Fin.cast sameWidth.symm target)
  exact ⟨source, Fin.cast_injective sameWidth.symm same⟩

/-- Every native grouped wire has exactly one original address, and every address is used. -/
def wireEquiv {width : Nat} (window : Window width) :
    Fin (groupedEncoding window).width ≃ Fin (encoding width).width :=
  Equiv.ofBijective (wireMap window)
    ⟨wireMap_injective window, wireMap_surjective window⟩

private lemma control_wire {width : Nat} (window : Window width) :
    (ArithmeticWindowEncoding.controlBit window).wire.val = 2 * window.length + 1 +
      (2 * (window.above + window.below) + 4 * width.size + 3) := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) + ((window.above + window.below) +
      ((width.size + width.size) + ((width.size + width.size) + ((1 + 1) + (1 + 0)))))) = _
  omega

private lemma work_wire {width : Nat} (window : Window width) :
    (workBit window).wire.val = 2 * window.length + 1 +
      (2 * (window.above + window.below) + 4 * width.size + 2) := by
  change (window.length + window.length + 1) +
    ((window.above + window.below) + ((window.above + window.below) +
      ((width.size + width.size) + ((width.size + width.size) + ((1 + 1) + 0))))) = _
  omega

/-- The grouped Ctrl lens maps to the actual original source Ctrl wire. -/
lemma physicalIndex_control {width : Nat} (window : Window width) :
    physicalIndex window (ArithmeticWindowEncoding.controlBit window).wire.val =
      (SharedEEA.controlBit width).wire.val := by
  rw [control_wire, SharedEEA.controlBit_wire]
  unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
  split_ifs <;> omega

/-- The arbitrary work lens maps to the original retained Iter wire. -/
lemma physicalIndex_work {width : Nat} (window : Window width) :
    physicalIndex window (workBit window).wire.val = (iterationBit width).wire.val := by
  rw [work_wire, iterationBit_wire]
  unfold physicalIndex ArithmeticWindowCoordinates.physicalIndex complementPhysicalIndex
  split_ifs <;> omega

/-- The two existing control-work coordinates are physically distinct on every window. -/
lemma control_work_ne {width : Nat} (window : Window width) :
    (ArithmeticWindowEncoding.controlBit window).wire ≠ (workBit window).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [control_wire, work_wire] at values
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowFullCoordinates
