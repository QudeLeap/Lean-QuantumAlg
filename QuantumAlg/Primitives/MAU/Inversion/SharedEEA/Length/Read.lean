/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Coordinates
import all QuantumAlg.Util.NumberTheory.SharedEEA.PhysicalWindow

/-!
# Exact actual work-word reads at a retained length boundary

After the work-word exchange, the coefficient refresh reads the physical
left region in little-endian arithmetic order; the divisor refresh reads
the right suffix at the newly retained coefficient boundary
[LYL+26, sec_EEA/sub_regshare.tex:309-313]. These are exactly the word reads
used by the source's serial old-length and new-length XOR writes
[LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341].

Every physical bit lens agrees with that complete finite read. Changing
the actual target length bit preserves both its retained boundary key and
the complete word being read, independently of the incoming output and
work-bit values. No bound on an arbitrary label's arithmetic size is added.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthRead

noncomputable section

open LengthCoordinates

/-- The actual original word selected by a static instruction parameter. -/
def sourceWord {width : Nat} (firstWord : Bool) (state : Registers width) : BitVec (width + 3) :=
  if firstWord then state.firstWord else state.secondWord

/-- The complete finite arithmetic value read from the actual static physical region. -/
def readWord (width : Nat) (field : Field) (key : BitVec width.size)
    (word : BitVec (width + 3)) : BitVec (region width field key) :=
  match field with
  | .coefficient => QuantumAlg.NumberTheory.SharedEEA.PhysicalWindow.read
      (region width .coefficient key) word
  | .divisor => word.extractLsb' 0 (region width .divisor key)

/-- Most-significant-first arithmetic reads have the proved literal physical word positions. -/
lemma readWord_getMsbD (width : Nat) (field : Field) (key : BitVec width.size)
    (word : BitVec (width + 3)) (index : Fin (region width field key)) :
    (readWord width field key word).getMsbD index.val =
      word.getMsbD (payloadPosition width field key index).val := by
  have within := index.isLt
  have bounded := region_le width field key
  have reverseBound : region width field key - 1 - index.val < region width field key := by
    omega
  cases field with
  | coefficient =>
      calc
        _ = (QuantumAlg.NumberTheory.SharedEEA.PhysicalWindow.read
            (region width .coefficient key) word).getLsbD
              (region width .coefficient key - 1 - index.val) := by
          simp only [readWord, BitVec.getMsbD_eq_getLsbD, within, decide_true, Bool.true_and]
        _ = word.getMsbD (region width .coefficient key - 1 - index.val) :=
          QuantumAlg.NumberTheory.SharedEEA.PhysicalWindow.read_bit word bounded _ reverseBound
        _ = _ := rfl
  | divisor =>
      have sourceBound : width + 3 - region width .divisor key + index.val < width + 3 := by
        omega
      have reversed : width + 3 - 1 -
          (width + 3 - region width .divisor key + index.val) =
            region width .divisor key - 1 - index.val := by omega
      simp only [readWord, payloadPosition, BitVec.getMsbD_eq_getLsbD, within, sourceBound,
        decide_true, Bool.true_and, BitVec.getLsbD_extractLsb', Nat.zero_add, reverseBound,
        reversed]

/-- Every actual native payload lens reads the corresponding bit of the complete finite value. -/
lemma payloadBit_get (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (index : Fin (region width field key)) (state : Registers width) :
    (payloadBit width field key firstWord index).get state =
      (readWord width field key (sourceWord firstWord state)).getMsbD index.val := by
  cases firstWord with
  | false =>
      change (secondWordBit width (payloadPosition width field key index)).get state =
        (readWord width field key state.secondWord).getMsbD index.val
      rw [secondWordBit_get]
      exact (readWord_getMsbD width field key state.secondWord index).symm
  | true =>
      change (firstWordBit width (payloadPosition width field key index)).get state =
        (readWord width field key state.firstWord).getMsbD index.val
      rw [firstWordBit_get]
      exact (readWord_getMsbD width field key state.firstWord index).symm

/-- The complete natural value obtained from the actual selected region. -/
def payloadValue {width : Nat} (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (state : Registers width) : Nat :=
  (readWord width field key (sourceWord firstWord state)).toNat

/-- The physical region read has its own exact finite-width bound, including the empty region. -/
lemma payloadValue_fits {width : Nat} (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (state : Registers width) :
    payloadValue field key firstWord state < 2 ^ region width field key :=
  (readWord width field key (sourceWord firstWord state)).isLt

/-- Native leading-position tests read exactly the corresponding natural-number test bits. -/
lemma payloadBit_testBit (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (index : Fin (region width field key)) (state : Registers width) :
    (payloadBit width field key firstWord index).get state =
      (payloadValue field key firstWord state).testBit
        (region width field key - 1 - index.val) := by
  rw [payloadBit_get]
  simp only [BitVec.getMsbD_eq_getLsbD, index.isLt, decide_true, Bool.true_and,
    BitVec.getLsbD, payloadValue]

/-- Matching all actual boundary-key sources is equality of the retained complete finite word. -/
lemma boundary_matches_iff (width : Nat) (field : Field) (key : BitVec width.size)
    (state : Registers width) :
    (∀ index : Fin width.size,
      (boundaryBit width field index).get state = key.getMsbD index.val) ↔
        boundaryValue field state = key := by
  constructor
  · intro matched
    apply BitVec.eq_of_getMsbD_eq
    intro index within
    exact (boundaryBit_get width field ⟨index, within⟩ state).symm.trans
      (matched ⟨index, within⟩)
  · intro same index
    rw [boundaryBit_get, same]

/-- A target length flip preserves the other complete length field used as the boundary key. -/
lemma boundaryValue_output_flip (width : Nat) (field : Field) (output : Fin width.size)
    (state : Registers width) :
    boundaryValue field ((outputBit width field output).flip state) =
      boundaryValue field state := by
  cases field <;> rfl

/-- A target length flip preserves the complete selected source work word. -/
lemma sourceWord_output_flip (width : Nat) (field : Field) (firstWord : Bool)
    (output : Fin width.size) (state : Registers width) :
    sourceWord firstWord ((outputBit width field output).flip state) =
      sourceWord firstWord state := by
  cases field <;> cases firstWord <;> rfl

/-- Every later actual predicate reads the same complete finite payload after a length flip. -/
lemma payloadValue_output_flip (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (output : Fin width.size) (state : Registers width) :
    payloadValue field key firstWord ((outputBit width field output).flip state) =
      payloadValue field key firstWord state := by
  unfold payloadValue
  rw [sourceWord_output_flip]

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthRead
