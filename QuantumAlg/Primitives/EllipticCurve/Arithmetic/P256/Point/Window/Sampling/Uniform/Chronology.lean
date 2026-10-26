/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Coordinates
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

/-!
# Contiguous source consumption by the original chronological window list

Only integer offsets and the existing compact Fin-indexed list are used.
The generator stream's high four-bit tail and descending full windows
precede the target-inverse stream's same order. Adjacent current blocks
therefore consume the original paired source through its final position520.
No physical instruction list is expanded or reordered.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace WindowIndex

/-- First original mathematical source position after this complete current block. -/
def sourceEnd (index : WindowIndex) : Nat := index.sourceStart + (index.lowerWidth + 1)

end WindowIndex

-- Keep symbolic schedule fields boxed until their explicit elementary formula is requested.
attribute [local irreducible] WindowIndex.full WindowIndex.start WindowIndex.lowerWidth
  WindowIndex.sourceStart chronologicalIndex

private lemma stream_start (stream : Fin 2) (position : Fin 17) :
    (WindowIndex.mk stream position.rev).start =
      if position.val = 0 then 0 else 4 + 16 * (position.val - 1) := by
  unfold WindowIndex.start WindowIndex.full
  change (if 17 - (position.val + 1) < 16 then
    4 + 16 * (15 - (17 - (position.val + 1))) else 0) = _
  have bound := position.isLt
  split_ifs <;> omega

private lemma stream_width (stream : Fin 2) (position : Fin 17) :
    (WindowIndex.mk stream position.rev).lowerWidth + 1 =
      if position.val = 0 then 4 else 16 := by
  unfold WindowIndex.lowerWidth WindowIndex.full
  change (if 17 - (position.val + 1) < 16 then 15 else 3) + 1 = _
  have bound := position.isLt
  split_ifs <;> omega

private lemma first_stream_offset (logical : Fin 17) :
    (WindowIndex.mk 0 logical).sourceStart = (WindowIndex.mk 0 logical).start := by
  unfold WindowIndex.sourceStart
  rfl

private lemma second_stream_offset (logical : Fin 17) :
    (WindowIndex.mk 1 logical).sourceStart = 260 + (WindowIndex.mk 1 logical).start := by
  unfold WindowIndex.sourceStart
  rfl

private lemma paired_start_first (index : Fin 17) :
    (chronologicalIndex (index.castAdd 17)).sourceStart =
      if index.val = 0 then 0 else 4 + 16 * (index.val - 1) :=
  (congrArg WindowIndex.sourceStart (chronologicalIndex_first index)).trans
    ((first_stream_offset index.rev).trans (stream_start 0 index))

private lemma paired_start_second (index : Fin 17) :
    (chronologicalIndex (index.natAdd 17)).sourceStart =
      260 + (if index.val = 0 then 0 else 4 + 16 * (index.val - 1)) :=
  (congrArg WindowIndex.sourceStart (chronologicalIndex_second index)).trans
    ((second_stream_offset index.rev).trans
      (congrArg (fun offset : Nat => 260 + offset) (stream_start 1 index)))

private lemma second_start_formula (index : Nat) :
    260 + (if index = 0 then 0 else 4 + 16 * (index - 1)) =
      if 17 + index < 17 then
        if 17 + index = 0 then 0 else 4 + 16 * (17 + index - 1)
      else if 17 + index = 17 then 260 else 264 + 16 * (17 + index - 18) := by
  split_ifs <;> omega

private lemma paired_start (position : Fin 34) :
    (chronologicalIndex position).sourceStart =
      if position.val < 17 then
        if position.val = 0 then 0 else 4 + 16 * (position.val - 1)
      else if position.val = 17 then 260 else 264 + 16 * (position.val - 18) := by
  refine Fin.addCases (m := 17) (n := 17) (fun index => ?_) (fun index => ?_) position
  · refine (paired_start_first index).trans ?_
    simp only [Fin.val_castAdd, if_pos index.isLt]
  · refine (paired_start_second index).trans ?_
    simp only [Fin.val_natAdd]
    exact second_start_formula index.val

private lemma paired_width (position : Fin 34) :
    (chronologicalIndex position).lowerWidth + 1 =
      if position.val = 0 ∨ position.val = 17 then 4 else 16 := by
  refine Fin.addCases (m := 17) (n := 17) (fun index => ?_) (fun index => ?_) position
  · rw [chronologicalIndex_first, stream_width]
    have bound := index.isLt
    simp only [Fin.val_castAdd]
    split_ifs <;> omega
  · rw [chronologicalIndex_second, stream_width]
    simp only [Fin.val_natAdd]
    split_ifs <;> omega

private def chronologicalSourceOffset (position : Nat) : Nat :=
  if position < 17 then
    if position = 0 then 0 else 4 + 16 * (position - 1)
  else if position = 17 then 260 else 264 + 16 * (position - 18)

private def chronologicalSourceWidth (position : Nat) : Nat :=
  if position = 0 ∨ position = 17 then 4 else 16

private lemma chronologicalSourceOffset_next (position : Nat) (bound : position < 33) :
    chronologicalSourceOffset (position + 1) =
      chronologicalSourceOffset position + chronologicalSourceWidth position := by
  unfold chronologicalSourceOffset chronologicalSourceWidth
  by_cases zero : position = 0
  · subst position
    rfl
  · by_cases first : position < 16
    · have nextFirst : position + 1 < 17 := by omega
      have currentFirst : position < 17 := by omega
      have nextNonzero : position + 1 ≠ 0 := by omega
      have regular : ¬(position = 0 ∨ position = 17) := by omega
      rw [if_pos nextFirst, if_neg nextNonzero, if_pos currentFirst, if_neg zero,
        if_neg regular]
      omega
    · by_cases transition : position = 16
      · subst position
        rfl
      · by_cases second : position = 17
        · subst position
          rfl
        · have currentSecond : ¬position < 17 := by omega
          have nextSecond : ¬position + 1 < 17 := by omega
          have nextRegular : position + 1 ≠ 17 := by omega
          have regular : ¬(position = 0 ∨ position = 17) := by omega
          rw [if_neg nextSecond, if_neg nextRegular, if_neg currentSecond, if_neg second,
            if_neg regular]
          omega

/-- Adjacent original windows consume adjacent blocks of the same complete paired source. -/
lemma sampling_chronological_source_next (position : Fin 33) :
    (chronologicalIndex position.succ).sourceStart =
      (chronologicalIndex position.castSucc).sourceEnd := by
  rw [WindowIndex.sourceEnd, paired_start, paired_start, paired_width]
  simp only [Fin.val_succ, Fin.val_castSucc]
  exact chronologicalSourceOffset_next position.val position.isLt

/-- The original generator high tail begins at the original first source position. -/
lemma sampling_chronological_source_first : (chronologicalIndex 0).sourceStart = 0 := by
  rw [paired_start]
  rfl

/-- The final target-inverse full window ends at exactly the original paired width. -/
lemma sampling_chronological_source_last :
    (chronologicalIndex (Fin.last 33)).sourceEnd = 520 := by
  rw [WindowIndex.sourceEnd, paired_start, paired_width]
  rfl

/-- Every nonempty suffix consumes consecutive original blocks and ends at the same final width. -/
def SourceSuffix : List WindowIndex → Prop
  | [] => True
  | head :: [] => head.sourceEnd = 520
  | head :: next :: rest => next.sourceStart = head.sourceEnd ∧ SourceSuffix (next :: rest)

/-- Removing the actual head retains this original-source suffix invariant. -/
lemma sampling_sourceSuffix_tail (head : WindowIndex) (rest : List WindowIndex)
    (valid : SourceSuffix (head :: rest)) : SourceSuffix rest := by
  cases rest with
  | nil => trivial
  | cons next tail => exact valid.2

private lemma sourceSuffix_of_chain (indices : List WindowIndex)
    (chain : indices.IsChain (fun first second => second.sourceStart = first.sourceEnd))
    (last : ∀ index ∈ indices.getLast?, index.sourceEnd = 520) : SourceSuffix indices := by
  induction indices with
  | nil => trivial
  | cons head rest ih =>
      cases rest with
      | nil => exact last head (by simp)
      | cons next tail =>
          refine ⟨chain.rel, ih chain.tail ?_⟩
          intro index member
          exact last index (by simpa only [List.getLast?_cons_cons] using member)

/-- The unchanged compact actual34 schedule satisfies the full original-source suffix invariant. -/
lemma sampling_schedule_sourceSuffix : SourceSuffix schedule := by
  rw [schedule, ← List.ofFn_eq_map]
  apply sourceSuffix_of_chain
  · apply List.isChain_ofFn.mpr
    intro index within
    exact sampling_chronological_source_next ⟨index, by omega⟩
  · intro index member
    have nonempty : List.ofFn chronologicalIndex ≠ [] := by
      intro empty
      have lengths := congrArg List.length empty
      simp only [List.length_ofFn, List.length_nil] at lengths
      omega
    rw [List.getLast?_eq_some_getLast nonempty, List.getLast_ofFn_succ] at member
    simp only [Option.mem_some_iff] at member
    subst index
    exact sampling_chronological_source_last

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
