/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.WindowCoordinates

/-!
# Original bit prefixes and exact chronological concatenation

These mathematical labels retain the original MSB-first coordinates. The
append criterion compares every leading and trailing coordinate and imposes
no Fourier independence or physical implementation hypothesis.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

/-- The first original coordinates of a mathematical bit label. -/
def prefixBits {full : Nat} (count : Nat) (bounded : count ≤ full)
    (input : Bits full) : Bits count :=
  (binaryEquiv count).symm (BinaryBasis.bigEndianEquiv count
    (fun position => tupleCoordinates full input (Fin.castLE bounded position)))

/-- Prefix restriction retains each original coordinate literally. -/
lemma prefixBits_coordinate {full : Nat} (count : Nat) (bounded : count ≤ full)
    (input : Bits full) (position : Fin count) :
    tupleCoordinates count (prefixBits count bounded input) position =
      tupleCoordinates full input (Fin.castLE bounded position) := by
  simp only [tupleCoordinates, prefixBits, Equiv.apply_symm_apply]
  exact congrFun ((BinaryBasis.bigEndianEquiv count).symm_apply_apply _) position

/-- A complete prefix is the original label, without a bit reversal. -/
lemma prefixBits_all (full : Nat) (input : Bits full) :
    prefixBits full (Nat.le_refl full) input = input := by
  apply tupleCoordinates_injective full
  funext position
  exact prefixBits_coordinate full (Nat.le_refl full) input position

/-- The original leading and trailing coordinates determine the complete concatenated tuple. -/
lemma blockBits_eq_of_coordinates (head tail : Nat) (value : Bits (tail + head))
    (front : Bits head) (back : Bits tail)
    (frontReads : ∀ position : Fin head,
      tupleCoordinates (tail + head) value (prefixPosition head tail position) =
        tupleCoordinates head front position)
    (backReads : ∀ position : Fin tail,
      tupleCoordinates (tail + head) value (suffixPosition head tail position) =
        tupleCoordinates tail back position) :
    value = blockBits head tail front back := by
  apply tupleCoordinates_injective (tail + head)
  funext position
  by_cases inside : position.val < head
  · let previous : Fin head := ⟨position.val, inside⟩
    have same : prefixPosition head tail previous = position := Fin.ext rfl
    rw [← same, blockBits_prefix]
    exact frontReads previous
  · have bounded : position.val - head < tail := by have := position.isLt; omega
    let current : Fin tail := ⟨position.val - head, bounded⟩
    have same : suffixPosition head tail current = position := by
      apply Fin.ext
      change head + (position.val - head) = position.val
      omega
    rw [← same, blockBits_suffix]
    exact backReads current

/-- Appending the selected original source coordinates advances its unchanged prefix. -/
lemma prefixBits_append {full : Nat} (head tail : Nat)
    (bounded : tail + head ≤ full) (input : Bits full) (selected : Bits tail)
    (selectedReads : ∀ position : Fin tail,
      tupleCoordinates tail selected position =
        tupleCoordinates full input
          (Fin.castLE bounded (suffixPosition head tail position))) :
    prefixBits (tail + head) bounded input =
      blockBits head tail
        (prefixBits head ((Nat.le_add_left head tail).trans bounded) input) selected := by
  apply blockBits_eq_of_coordinates
  · intro position
    rw [prefixBits_coordinate, prefixBits_coordinate]
    rfl
  · intro position
    rw [prefixBits_coordinate]
    exact (selectedReads position).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
