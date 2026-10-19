/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Selection.Predicate
import all QuantumAlg.Util.NumberTheory.SharedEEA.SwapBoundary

/-!
# Exact finite keys and untruncated positions for the Sign selector

The baseline increments quotient length before the phase-2 swap, but swaps
before decrementing in phase 3 [LYL+26, sec_EEA/sub_regshare.tex:281-296].
With both updates moved after the swap, the old-length zero-based position
is `lt + lq + 1` in phase 2 and `lt + lq` in phase 3. This corrects the
missing phase-2 offset in the optimized listing [ibid., sub_opt.tex:52-59];
`NumberTheory.SharedEEA.SwapBoundary` records the exact packing discrepancy.
A selector key stores both complete
finite length values and the first phase; its equality pattern requires
the second phase to be the opposite value. Thus a frame matches at most
one key, and only when the original phase-xor condition is true.

Positions are sums in Nat after decoding both finite words. They are not
finite-word sums, and are never reduced modulo the length-register width.
The eventual gate list explicitly skips positions outside Work1. This
owner neither assumes a caller range promise nor supplies a quantum input
through an input-dependent classical preparation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SelectionKey

noncomputable section

open SelectionLayout SelectionPredicate

/-- Both complete length values and the first of the two opposite selected phases. -/
abbrev Key (width : Nat) := BitVec width.size × (BitVec width.size × Bool)

/-- Decode exactly the existing length and phase values of the actual frame. -/
def readKey {width : Nat} (state : Registers width) : Key width :=
  (state.coefficientLength, (state.quotientLength, state.flags.first))

/-- The source block is selected exactly when its two actual phase bits differ. -/
def phaseSelected {width : Nat} (state : Registers width) : Bool :=
  state.flags.first ^^ state.flags.second

/-- The native equality pattern includes the opposite second phase explicitly. -/
def pattern {width : Nat} (selected : Key width) : Pattern width := fun index =>
  if index.val < width.size then selected.1.getMsbD index.val
  else if index.val < 2 * width.size then selected.2.1.getMsbD (index.val - width.size)
  else if index.val = 2 * width.size then selected.2.2 else !selected.2.2

private def coefficientIndex (width : Nat) (index : Fin width.size) : Fin (2 * width.size + 2) :=
  ⟨index.val, by have within := index.isLt; omega⟩

private def quotientIndex (width : Nat) (index : Fin width.size) : Fin (2 * width.size + 2) :=
  ⟨width.size + index.val, by have within := index.isLt; omega⟩

private def firstIndex (width : Nat) : Fin (2 * width.size + 2) := ⟨2 * width.size, by omega⟩

private def secondIndex (width : Nat) : Fin (2 * width.size + 2) := ⟨2 * width.size + 1, by omega⟩

private lemma source_coefficient (width : Nat) (state : Registers width)
    (index : Fin width.size) :
    ((layout width).source.bit (coefficientIndex width index)).get state =
      state.coefficientLength.getMsbD index.val := by
  have initial : (coefficientIndex width index).val < width.size := index.isLt
  rw [layout_source_get, sourceBit_get, if_pos initial]
  rfl

private lemma pattern_coefficient (width : Nat) (selected : Key width) (index : Fin width.size) :
    pattern selected (coefficientIndex width index) = selected.1.getMsbD index.val := by
  have initial : (coefficientIndex width index).val < width.size := index.isLt
  rw [pattern, if_pos initial]
  rfl

private lemma source_quotient (width : Nat) (state : Registers width) (index : Fin width.size) :
    ((layout width).source.bit (quotientIndex width index)).get state =
      state.quotientLength.getMsbD index.val := by
  have notInitial : ¬(quotientIndex width index).val < width.size := by
    change ¬width.size + index.val < width.size
    omega
  have second : (quotientIndex width index).val < 2 * width.size := by
    change width.size + index.val < 2 * width.size
    have within := index.isLt
    omega
  rw [layout_source_get, sourceBit_get, if_neg notInitial, if_pos second]
  change state.quotientLength.getMsbD (width.size + index.val - width.size) = _
  rw [Nat.add_sub_cancel_left]

private lemma pattern_quotient (width : Nat) (selected : Key width) (index : Fin width.size) :
    pattern selected (quotientIndex width index) = selected.2.1.getMsbD index.val := by
  have notInitial : ¬(quotientIndex width index).val < width.size := by
    change ¬width.size + index.val < width.size
    omega
  have second : (quotientIndex width index).val < 2 * width.size := by
    change width.size + index.val < 2 * width.size
    have within := index.isLt
    omega
  rw [pattern, if_neg notInitial, if_pos second]
  change selected.2.1.getMsbD (width.size + index.val - width.size) = _
  rw [Nat.add_sub_cancel_left]

private lemma source_first (width : Nat) (state : Registers width) :
    ((layout width).source.bit (firstIndex width)).get state = state.flags.first := by
  rw [layout_source_get, sourceBit_get]
  have notInitial : ¬(firstIndex width).val < width.size := by
    change ¬2 * width.size < width.size
    omega
  have notSecond : ¬(firstIndex width).val < 2 * width.size := Nat.lt_irrefl _
  have first : (firstIndex width).val = 2 * width.size := rfl
  rw [if_neg notInitial, if_neg notSecond, if_pos first]

private lemma pattern_first (width : Nat) (selected : Key width) :
    pattern selected (firstIndex width) = selected.2.2 := by
  have notInitial : ¬(firstIndex width).val < width.size := by
    change ¬2 * width.size < width.size
    omega
  have notSecond : ¬(firstIndex width).val < 2 * width.size := Nat.lt_irrefl _
  have first : (firstIndex width).val = 2 * width.size := rfl
  rw [pattern, if_neg notInitial, if_neg notSecond, if_pos first]

private lemma source_second (width : Nat) (state : Registers width) :
    ((layout width).source.bit (secondIndex width)).get state = state.flags.second := by
  rw [layout_source_get, sourceBit_get]
  have notInitial : ¬(secondIndex width).val < width.size := by
    change ¬2 * width.size + 1 < width.size
    omega
  have notSecond : ¬(secondIndex width).val < 2 * width.size := by
    change ¬2 * width.size + 1 < 2 * width.size
    omega
  have notFirst : (secondIndex width).val ≠ 2 * width.size := by
    change 2 * width.size + 1 ≠ 2 * width.size
    omega
  rw [if_neg notInitial, if_neg notSecond, if_neg notFirst]

private lemma pattern_second (width : Nat) (selected : Key width) :
    pattern selected (secondIndex width) = !selected.2.2 := by
  have notInitial : ¬(secondIndex width).val < width.size := by
    change ¬2 * width.size + 1 < width.size
    omega
  have notSecond : ¬(secondIndex width).val < 2 * width.size := by
    change ¬2 * width.size + 1 < 2 * width.size
    omega
  have notFirst : (secondIndex width).val ≠ 2 * width.size := by
    change 2 * width.size + 1 ≠ 2 * width.size
    omega
  rw [pattern, if_neg notInitial, if_neg notSecond, if_neg notFirst]

/-- The native bit-equality predicate is exactly equality of both complete lengths and phases. -/
lemma matches_fields_iff (width : Nat) (selected : Key width) (state : Registers width) :
    Matches (pattern selected) state ↔
      state.coefficientLength = selected.1 ∧ state.quotientLength = selected.2.1 ∧
        state.flags.first = selected.2.2 ∧ state.flags.second = !selected.2.2 := by
  constructor
  · intro matched
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      exact (source_coefficient width state ⟨index, within⟩).symm.trans
        ((matched (coefficientIndex width ⟨index, within⟩)).trans
          (pattern_coefficient width selected ⟨index, within⟩))
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      exact (source_quotient width state ⟨index, within⟩).symm.trans
        ((matched (quotientIndex width ⟨index, within⟩)).trans
          (pattern_quotient width selected ⟨index, within⟩))
    · exact (source_first width state).symm.trans
        ((matched (firstIndex width)).trans (pattern_first width selected))
    · exact (source_second width state).symm.trans
        ((matched (secondIndex width)).trans (pattern_second width selected))
  · rintro ⟨coefficient, quotient, first, second⟩ index
    rw [layout_source_get, sourceBit_get, pattern, coefficient, quotient, first, second]

private lemma xor_true_iff (first second : Bool) :
    (first ^^ second) = true ↔ second = !first := by
  cases first <;> cases second <;> decide

/-- Exactly one full key can match, and only on the source's actual two-phase condition. -/
lemma matches_key_iff (width : Nat) (selected : Key width) (state : Registers width) :
    Matches (pattern selected) state ↔ readKey state = selected ∧ phaseSelected state = true := by
  rw [matches_fields_iff]
  constructor
  · rintro ⟨coefficient, quotient, first, second⟩
    refine ⟨Prod.ext coefficient (Prod.ext quotient first), ?_⟩
    change (state.flags.first ^^ state.flags.second) = true
    rw [first, second]
    cases selected.2.2 <;> rfl
  · rintro ⟨key, phase⟩
    have coefficient := congrArg (fun value : Key width => value.1) key
    have quotient := congrArg (fun value : Key width => value.2.1) key
    have first := congrArg (fun value : Key width => value.2.2) key
    have second := (xor_true_iff state.flags.first state.flags.second).mp phase
    exact ⟨coefficient, quotient, first, second.trans (congrArg Bool.not first)⟩

/-- The actual physical index retains the baseline's phase-dependent pre-update boundary. -/
def position {width : Nat} (selected : Key width) : Nat :=
  selected.1.toNat + selected.2.1.toNat + (if selected.2.2 then 0 else 1)

/-- The native phase-2 key targets exactly the baseline's next quotient-bit boundary. -/
lemma position_phase2 (width : Nat) (coefficient quotient : BitVec width.size) :
    position (coefficient, (quotient, false)) =
      NumberTheory.SharedEEA.SwapBoundary.phase2Position coefficient.toNat quotient.toNat := rfl

/-- The native phase-3 key retains the baseline's final existing quotient-bit boundary. -/
lemma position_phase3 (width : Nat) (coefficient quotient : BitVec width.size) :
    position (coefficient, (quotient, true)) =
      NumberTheory.SharedEEA.SwapBoundary.phase3Position coefficient.toNat quotient.toNat := rfl

/-- A matching key therefore selects the source's exact untruncated zero-based position. -/
lemma position_of_matches (width : Nat) (selected : Key width) (state : Registers width)
    (matched : Matches (pattern selected) state) :
    position selected = state.coefficientLength.toNat + state.quotientLength.toNat +
      (if state.flags.first then 0 else 1) := by
  obtain ⟨coefficient, quotient, first, _second⟩ :=
    (matches_fields_iff width selected state).mp matched
  unfold position
  rw [← coefficient, ← quotient, ← first]

/-- No frame can satisfy two different selector keys. -/
lemma matches_unique (width : Nat) (left right : Key width) (state : Registers width)
    (first : Matches (pattern left) state) (second : Matches (pattern right) state) :
    left = right :=
  ((matches_key_iff width left state).mp first).1.symm.trans
    ((matches_key_iff width right state).mp second).1

end

end QuantumAlg.MAU.Inversion.SharedEEA.SelectionKey
