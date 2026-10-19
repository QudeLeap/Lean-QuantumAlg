/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Boundary.Predicate.Layout

/-!
# Exact complete-field reads of both terminal-aware boundary conjunctions

Each actual source pattern tests quotient, low shift, and divisor length.
The larger pattern additionally tests both physical high-clock bits.
These are the two extended conjunctions required to repair the source's
finite low-counter boundary [LYL+26, sec_EEA/sub_opt.tex:74-84]. All fields
are read from their original quantum coordinates, including nonzero high
bits on active states and empty finite length fields.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.BoundaryPredicateRead

noncomputable section

open EncodedBit BoundaryPredicateLayout

private lemma length_capacity (width : Nat) (withHigh : Bool) :
    3 * width.size ≤ sourceCount width withHigh := by
  unfold sourceCount
  split <;> omega

private def quotientIndex (width : Nat) (withHigh : Bool) (index : Fin width.size) :
    Fin (sourceCount width withHigh) :=
  ⟨index.val, by have within := index.isLt; have total := length_capacity width withHigh; omega⟩

private def lowIndex (width : Nat) (withHigh : Bool) (index : Fin width.size) :
    Fin (sourceCount width withHigh) :=
  ⟨width.size + index.val, by
    have within := index.isLt
    have total := length_capacity width withHigh
    omega⟩

private def divisorIndex (width : Nat) (withHigh : Bool) (index : Fin width.size) :
    Fin (sourceCount width withHigh) :=
  ⟨2 * width.size + index.val, by
    have within := index.isLt
    have total := length_capacity width withHigh
    omega⟩

private def highIndex (width : Nat) (index : Fin 2) : Fin (sourceCount width true) :=
  ⟨3 * width.size + index.val, by
    change 3 * width.size + index.val < 3 * width.size + 2
    have within := index.isLt
    omega⟩

private lemma quotient_get (width : Nat) (withHigh : Bool) (index : Fin width.size)
    (state : Registers width) :
    (sourceBit width withHigh (quotientIndex width withHigh index)).get state =
      state.quotientLength.getMsbD index.val := by
  rw [sourceBit_get]
  exact if_pos index.isLt

private lemma low_get (width : Nat) (withHigh : Bool) (index : Fin width.size)
    (state : Registers width) :
    (sourceBit width withHigh (lowIndex width withHigh index)).get state =
      state.shift.getMsbD index.val := by
  have afterQuotient : ¬width.size + index.val < width.size := by omega
  have beforeDivisor : width.size + index.val < 2 * width.size := by
    have within := index.isLt
    omega
  rw [sourceBit_get]
  change (if width.size + index.val < width.size then _
    else if width.size + index.val < 2 * width.size then
      state.shift.getMsbD (width.size + index.val - width.size) else _) = _
  rw [if_neg afterQuotient, if_pos beforeDivisor, Nat.add_sub_cancel_left]

private lemma divisor_get (width : Nat) (withHigh : Bool) (index : Fin width.size)
    (state : Registers width) :
    (sourceBit width withHigh (divisorIndex width withHigh index)).get state =
      state.divisorLength.getMsbD index.val := by
  have afterQuotient : ¬2 * width.size + index.val < width.size := by omega
  have afterLow : ¬2 * width.size + index.val < 2 * width.size := by omega
  have beforeHigh : 2 * width.size + index.val < 3 * width.size := by
    have within := index.isLt
    omega
  rw [sourceBit_get]
  change (if 2 * width.size + index.val < width.size then _
    else if 2 * width.size + index.val < 2 * width.size then _
    else if 2 * width.size + index.val < 3 * width.size then
      state.divisorLength.getMsbD (2 * width.size + index.val - 2 * width.size) else _) = _
  rw [if_neg afterQuotient, if_neg afterLow, if_pos beforeHigh, Nat.add_sub_cancel_left]

private lemma high_get (width : Nat) (index : Fin 2) (state : Registers width) :
    (sourceBit width true (highIndex width index)).get state =
      (NumberTheory.SharedEEA.PaddingClock.high state.firstWord).getMsbD index.val := by
  have afterQuotient : ¬3 * width.size + index.val < width.size := by omega
  have afterLow : ¬3 * width.size + index.val < 2 * width.size := by omega
  have afterDivisor : ¬3 * width.size + index.val < 3 * width.size := by omega
  rw [sourceBit_get]
  change (if 3 * width.size + index.val < width.size then _
    else if 3 * width.size + index.val < 2 * width.size then _
    else if 3 * width.size + index.val < 3 * width.size then _
    else (NumberTheory.SharedEEA.PaddingClock.high state.firstWord).getMsbD
      (3 * width.size + index.val - 3 * width.size)) = _
  rw [if_neg afterQuotient, if_neg afterLow, if_neg afterDivisor, Nat.add_sub_cancel_left]

/-- Exact quantum-source equality of the actual three-field and four-region zero patterns. -/
lemma source_zero_iff (width : Nat) (withHigh : Bool) (state : Registers width) :
    (layout width withHigh).PatternMatches (fun _ => false) state ↔
      state.quotientLength = 0 ∧ state.shift = 0 ∧ state.divisorLength = 0 ∧
        (withHigh = true → NumberTheory.SharedEEA.PaddingClock.high state.firstWord = 0) := by
  constructor
  · intro matched
    have zeros : ∀ index, (sourceBit width withHigh index).get state = false := matched
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply (NativePredicate.word_zero_iff state.quotientLength).mp
      intro index
      exact (quotient_get width withHigh index state).symm.trans
        (zeros (quotientIndex width withHigh index))
    · apply (NativePredicate.word_zero_iff state.shift).mp
      intro index
      exact (low_get width withHigh index state).symm.trans
        (zeros (lowIndex width withHigh index))
    · apply (NativePredicate.word_zero_iff state.divisorLength).mp
      intro index
      exact (divisor_get width withHigh index state).symm.trans
        (zeros (divisorIndex width withHigh index))
    · intro selected
      subst withHigh
      apply (NativePredicate.word_zero_iff
        (NumberTheory.SharedEEA.PaddingClock.high state.firstWord)).mp
      intro index
      exact (high_get width index state).symm.trans (zeros (highIndex width index))
  · rintro ⟨quotient, low, divisor, high⟩ index
    change (sourceBit width withHigh index).get state = false
    rw [sourceBit_get]
    split
    · rw [quotient]
      exact BitVec.getMsbD_zero (w := width.size) (i := index.val)
    · split
      · rw [low]
        exact BitVec.getMsbD_zero (w := width.size) (i := index.val - width.size)
      · split
        · rw [divisor]
          exact BitVec.getMsbD_zero (w := width.size) (i := index.val - 2 * width.size)
        · have selected : withHigh = true := by
            have within := index.isLt
            cases withHigh
            · change index.val < 3 * width.size + 0 at within
              omega
            · rfl
          rw [high selected]
          exact BitVec.getMsbD_zero (w := 2) (i := index.val - 3 * width.size)

end

end QuantumAlg.MAU.Inversion.SharedEEA.BoundaryPredicateRead
