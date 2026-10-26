/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.PortProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers.BitExt
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Correction

/-!
# Four existing physical positions for the fixed resident seed

Only the three original Work1 tail positions and the coefficient-length
low bit are initialized. The unknown complete Work2 word is retained.
The original source initialization and zero main workspace are specified
in [LYL+26, sec_EEA/sub_4phase.tex:104-117;
sec_point_add/sec_point_add.tex:45-79]. No input value selects the seed.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ResidentSeed

noncomputable section

open EncodedBit

/-- Three original tail positions, followed by the low coefficient-length position. -/
def target (width : Nat) (positive : 0 < width.size) : Word (encoding width) 4 :=
  ⟨fun index => if within : index.val < 3 then
    firstWordBit width ⟨width + 2 - index.val, by omega⟩
  else coefficientLengthBit width ⟨width.size - 1, by omega⟩⟩

lemma target_wire (width : Nat) (positive : 0 < width.size) (index : Fin 4) :
    ((target width positive).bit index).wire.val =
      if index.val < 3 then width + 2 - index.val else 2 * (width + 3) + width.size - 1 := by
  dsimp only [target]
  split
  · rw [firstWordBit_wire]
  · rw [coefficientLengthBit_wire]
    change 2 * (width + 3) + (width.size - 1) = 2 * (width + 3) + width.size - 1
    omega

/-- The complete native supports are distinct, including the small length bit. -/
lemma target_distinct (width : Nat) (positive : 0 < width.size) :
    Function.Injective (fun index => ((target width positive).bit index).wire) := by
  intro left right same
  have values := congrArg Fin.val same
  rw [target_wire, target_wire] at values
  have leftBound := left.isLt
  have rightBound := right.isLt
  apply Fin.ext
  split at values <;> split at values <;> omega

/-- Original source with its entire supplied second word and every other bit zero. -/
def blank (width : Nat) (input : BitVec (width + 3)) : Registers width :=
  { firstWord := 0#(width + 3)
    secondWord := input
    coefficientLength := 0#width.size
    quotientLength := 0#width.size
    divisorLength := 0#width.size
    shift := 0#width.size
    flags := ⟨false, false, false, false⟩
    control := false }

/-- A three-bit constant extends only into the original three Work1 tail positions. -/
def source (width : Nat) (tail : BitVec 3) (input : BitVec (width + 3)) : Registers width :=
  { blank width input with
    firstWord := tail.setWidth (width + 3)
    coefficientLength := BitVec.ofNat width.size 1 }

/-- The fixed four-position instruction word includes the actual coefficient-length one. -/
def constant (tail : BitVec 3) : Fin (2 ^ 4) :=
  BitVec.equivFin ((1#1) ++ tail)

lemma constant_read (tail : BitVec 3) (index : Fin 4) :
    (constant tail).val.testBit index.val =
      if index.val < 3 then tail.getLsbD index.val else true := by
  change (((1#1) ++ tail) : BitVec 4).getLsbD index.val = _
  rw [BitVec.getLsbD_append]
  split
  · rfl
  · have last : index.val = 3 := by omega
    simp only [last]
    rfl

lemma target_blank (width : Nat) (positive : 0 < width.size)
    (input : BitVec (width + 3)) (index : Fin 4) :
    ((target width positive).bit index).get (blank width input) = false := by
  dsimp only [target]
  split
  · rw [firstWordBit_get]
    exact BitVec.getMsbD_zero
  · rw [coefficientLengthBit_get]
    exact BitVec.getMsbD_zero

/-- The seed has exactly the prescribed complete source initialization outside Work2. -/
lemma source_inputFrame (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    source modulus.size
        ((InitialPortProgram.inputFrame modulus input).firstWord.setWidth 3)
        (InitialPortProgram.inputFrame modulus input).secondWord =
      InitialPortProgram.inputFrame modulus input := by
  have sameWord :
      ((InitialPortProgram.inputFrame modulus input).firstWord.setWidth 3).setWidth
          (modulus.size + 3) = (InitialPortProgram.inputFrame modulus input).firstWord := by
    apply BitVec.eq_of_getMsbD_eq
    intro index within
    by_cases payload : index < modulus.size
    · rw [InitialPortProgram.inputFrame_large_bit modulus input ⟨index, payload⟩,
        BitVec.getMsbD_setWidth]
      have below : ¬modulus.size + 3 - 3 ≤ index := by omega
      simp only [below, decide_false, Bool.false_and]
    · simp only [BitVec.getMsbD_setWidth]
      have outer : modulus.size + 3 - 3 = modulus.size := by omega
      have inner : 3 - (modulus.size + 3) = 0 := by omega
      have after : index + 3 - (modulus.size + 3) + (modulus.size + 3) - 3 = index := by
        omega
      simp only [outer, inner, show modulus.size ≤ index by omega, decide_true,
        Bool.true_and, Nat.zero_le, after]
  apply Registers.ext_fields
  · exact sameWord
  all_goals rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ResidentSeed
