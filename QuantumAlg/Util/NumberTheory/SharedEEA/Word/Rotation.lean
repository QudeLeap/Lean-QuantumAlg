/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Packing

/-!
# Exact circular rotation of the second shared EEA word

The source rotates the entire second word left by its actual shift count,
so the little-endian coefficient may occupy both ends of that word
[LYL+26, sec_EEA/sub_regshare.tex:19-20,259,263-264]. This module uses the
actual `BitVec.rotateLeft` operation, proves its right-rotation inverse,
and connects both operations to the existing literal word encoding.

The bit equations describe the wrapped coefficient and remainder positions
without treating the coefficient as divisible by a power of two. The shift
count remains an explicit input to decoding. No phase flag or shift count
is erased, and no physical gate cost is assigned by this arithmetic owner.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.WordRotation

variable {width coefficientWidth remainderWidth : Nat}

/-- Right rotation exactly reverses the source's complete circular left rotation. -/
lemma rotateRight_rotateLeft (word : BitVec width) (shift : Nat) :
    (word.rotateLeft shift).rotateRight shift = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have reducedBound : shift % width < width := Nat.mod_lt _ (by omega)
  by_cases beforeWrap : index < width - shift % width
  · have sourceWithin : shift % width + index < width := by omega
    have afterShift : ¬ shift % width + index < shift % width := by omega
    suffices entry : word[index] = word.getLsbD index by
      simpa [BitVec.getLsbD_rotateRight, beforeWrap, afterShift, sourceWithin] using entry
    exact (BitVec.getLsbD_eq_getElem within).symm
  · have wrappedLt : index - (width - shift % width) < shift % width := by omega
    have restored : width - shift % width + (index - (width - shift % width)) = index := by
      omega
    simp [beforeWrap, within, wrappedLt, restored]

/-- Successive actual circular shifts add their retained shift counts. -/
lemma rotateLeft_comp (word : BitVec width) (first second : Nat) :
    (word.rotateLeft first).rotateLeft second = word.rotateLeft (first + second) := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have wrappedWithin : (second + index) % width < width := Nat.mod_lt _ (by omega)
  simp only [BitVec.getMsbD_rotateLeft, within, wrappedWithin, decide_true, Bool.true_and]
  congr 1
  rw [Nat.add_mod_mod, Nat.add_assoc]

/-- Store the exact second-word payload at its source circular shift. -/
def packRotatedWork2 (shift : Nat)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    BitVec (coefficientWidth + remainderWidth) :=
  (WordPacking.packWork2 payload).rotateLeft shift

/-- Undo the actual circular shift before decoding the prescribed source boundaries. -/
def unpackRotatedWork2 (shift : Nat)
    (word : BitVec (coefficientWidth + remainderWidth)) :
    WordPacking.Work2Payload coefficientWidth remainderWidth :=
  WordPacking.unpackWork2 (word.rotateRight shift)

/-- Every rotated word recovers its complete coefficient and remainder at the retained shift. -/
lemma unpackRotatedWork2_packRotatedWork2 (shift : Nat)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    unpackRotatedWork2 shift (packRotatedWork2 shift payload) = payload := by
  rw [unpackRotatedWork2, packRotatedWork2, rotateRight_rotateLeft]
  exact WordPacking.unpackWork2_packWork2 payload

/-- Rotation cannot merge distinct source payloads at the same actual shift count. -/
lemma packRotatedWork2_injective (shift : Nat) :
    Function.Injective (packRotatedWork2 (coefficientWidth := coefficientWidth)
      (remainderWidth := remainderWidth) shift) := by
  intro left right same
  calc
    left = unpackRotatedWork2 shift (packRotatedWork2 shift left) :=
      (unpackRotatedWork2_packRotatedWork2 shift left).symm
    _ = unpackRotatedWork2 shift (packRotatedWork2 shift right) :=
      congrArg (unpackRotatedWork2 shift) same
    _ = right := unpackRotatedWork2_packRotatedWork2 shift right

/-- Every physical bit reads its exact wrapped source position. -/
lemma packRotatedWork2_bit (shift index : Nat)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    (packRotatedWork2 shift payload).getMsbD index =
      (decide (index < coefficientWidth + remainderWidth) &&
        (if coefficientWidth ≤ (shift + index) % (coefficientWidth + remainderWidth) then
          payload.remainderBits.getMsbD
            ((shift + index) % (coefficientWidth + remainderWidth) - coefficientWidth)
        else payload.coefficientBits.getLsbD
          ((shift + index) % (coefficientWidth + remainderWidth)))) := by
  simp only [packRotatedWork2, BitVec.getMsbD_rotateLeft, WordPacking.packWork2,
    BitVec.getMsbD_append, BitVec.getMsbD_reverse]

/-- A literal one-position source shift advances the encoded shift count by one. -/
lemma packRotatedWork2_shift (shift : Nat)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    (packRotatedWork2 shift payload).rotateLeft 1 = packRotatedWork2 (shift + 1) payload :=
  rotateLeft_comp (WordPacking.packWork2 payload) shift 1

/-- The actual inverse one-position shift recovers the preceding encoded word. -/
lemma packRotatedWork2_unshift (shift : Nat)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    (packRotatedWork2 (shift + 1) payload).rotateRight 1 = packRotatedWork2 shift payload := by
  rw [← packRotatedWork2_shift]
  exact rotateRight_rotateLeft (packRotatedWork2 shift payload) 1

end QuantumAlg.NumberTheory.SharedEEA.WordRotation
