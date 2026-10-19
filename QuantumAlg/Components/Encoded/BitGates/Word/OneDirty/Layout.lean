/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.ZeroTest

/-!
# Balanced physical controls with one arbitrary borrowed bit

The controls are divided into two nearly equal groups. Each group can use
part of the other as temporary work in an elementary conjunction call.
Only the separately identified borrowed bit lies outside the controls and
the output. This is physical placement for the toggle cancellation principle
[G17, paper.tex:278-293] and the multi-control construction
[dW19, qcnotes.tex:1335-1337].
-/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Actual distinct source wires, one target, and one arbitrary borrowed wire. -/
structure OneDirtyLayout (controls : Nat) where
  source : Word encoding controls
  output : EncodedBit encoding
  work : EncodedBit encoding
  source_injective : Function.Injective (fun index => (source.bit index).wire)
  source_output_ne : ∀ index, (source.bit index).wire ≠ output.wire
  source_work_ne : ∀ index, (source.bit index).wire ≠ work.wire
  work_output_ne : work.wire ≠ output.wire

namespace OneDirtyLayout

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)

/-- The larger half is chosen first so that three controls also need no extra work. -/
def firstWidth (controls : Nat) : Nat := (controls + 1) / 2

/-- The remaining, possibly smaller group. -/
def secondWidth (controls : Nat) : Nat := controls - firstWidth controls

private lemma width_partition (controls : Nat) :
    firstWidth controls + secondWidth controls = controls := by
  simp only [secondWidth, firstWidth]
  omega

private lemma first_width_bound (controls : Nat) : firstWidth controls ≤ controls := by
  unfold firstWidth
  omega

/-- At least three controls make both elementary subcalls have at least two controls. -/
lemma balanced_widths (large : 3 ≤ controls) :
    2 ≤ firstWidth controls ∧ 1 ≤ secondWidth controls ∧
      firstWidth controls - 2 ≤ secondWidth controls ∧
      secondWidth controls - 1 ≤ firstWidth controls := by
  simp only [secondWidth, firstWidth]
  omega

def firstIndex (index : Fin (firstWidth controls)) : Fin controls :=
  ⟨index.val, lt_of_lt_of_le index.isLt (first_width_bound controls)⟩

def secondIndex (index : Fin (secondWidth controls)) : Fin controls :=
  ⟨firstWidth controls + index.val, by
    have bound := index.isLt
    have partition := width_partition controls
    omega⟩

/-- The first group reads actual leading control wires. -/
def firstBit (index : Fin (firstWidth controls)) : EncodedBit encoding :=
  layout.source.bit (firstIndex index)

/-- The second group reads the remaining actual control wires. -/
def secondBit (index : Fin (secondWidth controls)) : EncodedBit encoding :=
  layout.source.bit (secondIndex index)

lemma firstBit_injective : Function.Injective (fun index => (layout.firstBit index).wire) := by
  intro left right equal
  have indices := layout.source_injective equal
  have values := congrArg (fun index : Fin controls => index.val) indices
  exact Fin.ext values

lemma secondBit_injective : Function.Injective (fun index => (layout.secondBit index).wire) := by
  intro left right equal
  have values := congrArg Fin.val (layout.source_injective equal)
  apply Fin.ext
  change firstWidth controls + left.val = firstWidth controls + right.val at values
  omega

lemma firstBit_secondBit_ne (left : Fin (firstWidth controls))
    (right : Fin (secondWidth controls)) :
    (layout.firstBit left).wire ≠ (layout.secondBit right).wire := by
  intro equal
  have values := congrArg Fin.val (layout.source_injective equal)
  change left.val = firstWidth controls + right.val at values
  have bound := left.isLt
  omega

/-- Every original control belongs to exactly the two physically specified groups. -/
lemma source_all_iff (state : Data) :
    (∀ index, (layout.source.bit index).get state = true) ↔
      (∀ index, (layout.firstBit index).get state = true) ∧
        (∀ index, (layout.secondBit index).get state = true) := by
  constructor
  · intro allBits
    exact ⟨fun index => allBits (firstIndex index), fun index => allBits (secondIndex index)⟩
  · rintro ⟨first, second⟩ index
    by_cases leading : index.val < firstWidth controls
    · exact first ⟨index.val, leading⟩
    · have remaining : index.val - firstWidth controls < secondWidth controls := by
        have bound := index.isLt
        have partition := width_partition controls
        omega
      have selected := second ⟨index.val - firstWidth controls, remaining⟩
      have same : secondIndex (⟨index.val - firstWidth controls, remaining⟩ :
          Fin (secondWidth controls)) = index := by
        apply Fin.ext
        dsimp [secondIndex]
        omega
      simpa only [secondBit, same] using selected

end OneDirtyLayout

end

end QuantumAlg.EncodedBit.Word
