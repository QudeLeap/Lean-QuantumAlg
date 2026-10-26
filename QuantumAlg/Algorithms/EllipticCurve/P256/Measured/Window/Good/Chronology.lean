/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Chronology

/-!
# Original source cursors at every chronological window boundary

Each original stream consumes its high four-bit tail and then sixteen full
sixteen-bit windows. The two counters describe the same existing schedule,
including its stream transition and final position. These are only natural
number identities; no circuit or source distribution is changed.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open Sampling

/-- Original bits consumed after this many windows of one stream. -/
def streamPrefixCount (processed : Nat) : Nat :=
  if processed = 0 then 0 else 4 + 16 * (processed - 1)

/-- Consumed generator bits at the original paired chronological boundary. -/
def firstCount (processed : Nat) : Nat := streamPrefixCount (min processed 17)

/-- Consumed target-inverse bits at the original paired chronological boundary. -/
def secondCount (processed : Nat) : Nat := streamPrefixCount (processed - 17)

/-- Consumed bits of the unchanged complete paired source. -/
def consumedCount (processed : Nat) : Nat := firstCount processed + secondCount processed

/-- An untouched stream has no consumed source bits. -/
@[simp] lemma streamPrefixCount_zero : streamPrefixCount 0 = 0 := rfl

/-- All seventeen original windows consume exactly one complete260-bit stream. -/
@[simp] lemma streamPrefixCount_seventeen : streamPrefixCount 17 = 260 := rfl

/-- The first window consumes four bits and every later window consumes sixteen. -/
lemma streamPrefixCount_succ (processed : Nat) :
    streamPrefixCount (processed + 1) =
      streamPrefixCount processed + (if processed = 0 then 4 else 16) := by
  unfold streamPrefixCount
  split_ifs <;> omega

/-- Every valid single-stream cursor is at most the original full width. -/
lemma streamPrefixCount_le (processed : Nat) (within : processed ≤ 17) :
    streamPrefixCount processed ≤ 260 := by
  unfold streamPrefixCount
  split_ifs <;> omega

private lemma firstCount_before (processed : Nat) (within : processed ≤ 17) :
    firstCount processed = streamPrefixCount processed := by
  rw [firstCount, Nat.min_eq_left within]

private lemma secondCount_before (processed : Nat) (within : processed ≤ 17) :
    secondCount processed = 0 := by
  rw [secondCount, Nat.sub_eq_zero_of_le within, streamPrefixCount_zero]

private lemma firstCount_after (processed : Nat) (started : 17 ≤ processed) :
    firstCount processed = 260 := by
  rw [firstCount, Nat.min_eq_right started, streamPrefixCount_seventeen]

private lemma secondCount_add (processed : Nat) :
    secondCount (17 + processed) = streamPrefixCount processed := by
  unfold secondCount
  congr 1
  omega

/-- The generator cursor starts at zero. -/
@[simp] lemma firstCount_zero : firstCount 0 = 0 := rfl

/-- The target-inverse cursor starts at zero. -/
@[simp] lemma secondCount_zero : secondCount 0 = 0 := rfl

/-- The original paired cursor starts at zero. -/
@[simp] lemma consumedCount_zero : consumedCount 0 = 0 := rfl

/-- The generator cursor finishes at its original full width. -/
@[simp] lemma firstCount_final : firstCount 34 = 260 := rfl

/-- The target-inverse cursor finishes at its original full width. -/
@[simp] lemma secondCount_final : secondCount 34 = 260 := rfl

/-- The final paired cursor has consumed both original full streams. -/
@[simp] lemma consumedCount_final : consumedCount 34 = 520 := rfl

/-- The generator cursor never exceeds its complete source width. -/
lemma firstCount_le (processed : Nat) : firstCount processed ≤ 260 :=
  streamPrefixCount_le _ (Nat.min_le_right processed 17)

/-- A valid chronological boundary never overconsumes the target-inverse stream. -/
lemma secondCount_le (processed : Nat) (within : processed ≤ 34) :
    secondCount processed ≤ 260 :=
  streamPrefixCount_le _ (by omega)

/-- Both source cursors fit within the same original paired source. -/
lemma consumedCount_le (processed : Nat) (within : processed ≤ 34) :
    consumedCount processed ≤ 520 := by
  have first := firstCount_le processed
  have second := secondCount_le processed within
  unfold consumedCount
  omega

/-- The actual source block begins at the sum of the original two stream cursors. -/
lemma chronological_sourceStart (position : Fin 34) :
    (chronologicalIndex position).sourceStart = consumedCount position.val := by
  refine Fin.addCases (m := 17) (n := 17) (fun index => ?_) (fun index => ?_) position
  · rw [Sampling.paired_start_first]
    change streamPrefixCount index.val = consumedCount index.val
    rw [consumedCount,
      firstCount_before index.val (Nat.le_of_lt index.isLt),
      secondCount_before index.val (Nat.le_of_lt index.isLt), Nat.add_zero]
  · rw [Sampling.paired_start_second]
    change 260 + streamPrefixCount index.val = consumedCount (17 + index.val)
    rw [consumedCount,
      firstCount_after (17 + index.val) (Nat.le_add_right 17 index.val), secondCount_add]

/-- The same actual block ends at the next original paired-source cursor. -/
lemma chronological_sourceEnd (position : Fin 34) :
    (chronologicalIndex position).sourceEnd = consumedCount (position.val + 1) := by
  refine Fin.lastCases ?_ (fun index => ?_) position
  · exact Sampling.sampling_chronological_source_last
  · exact (Sampling.sampling_chronological_source_next index).symm.trans
      (chronological_sourceStart index.succ)

private lemma stream_end (stream : Fin 2) (position : Fin 17) :
    (WindowIndex.mk stream position.rev).lowerWidth + 1 +
        (WindowIndex.mk stream position.rev).start =
      streamPrefixCount (position.val + 1) := by
  rw [Sampling.stream_width, Sampling.stream_start]
  change (if position.val = 0 then 4 else 16) + streamPrefixCount position.val = _
  have advance := streamPrefixCount_succ position.val
  omega

/-- A generator window advances exactly its own cursor and leaves the other cursor unchanged. -/
lemma chronological_first_counts (position : Fin 34)
    (selected : (chronologicalIndex position).stream = 0) :
    (chronologicalIndex position).start = firstCount position.val ∧
      (chronologicalIndex position).lowerWidth + 1 + (chronologicalIndex position).start =
        firstCount (position.val + 1) ∧
      secondCount (position.val + 1) = secondCount position.val := by
  revert selected
  refine Fin.addCases (m := 17) (n := 17) (fun index => ?_) (fun index => ?_) position
  · intro _selected
    rw [chronologicalIndex_first]
    change (WindowIndex.mk 0 index.rev).start = firstCount index.val ∧
      (WindowIndex.mk 0 index.rev).lowerWidth + 1 + (WindowIndex.mk 0 index.rev).start =
        firstCount (index.val + 1) ∧
      secondCount (index.val + 1) = secondCount index.val
    rw [
      firstCount_before index.val (Nat.le_of_lt index.isLt),
      firstCount_before (index.val + 1) (Nat.succ_le_of_lt index.isLt),
      secondCount_before index.val (Nat.le_of_lt index.isLt),
      secondCount_before (index.val + 1) (Nat.succ_le_of_lt index.isLt)]
    exact ⟨Sampling.stream_start 0 index, stream_end 0 index, rfl⟩
  · intro impossible
    rw [chronologicalIndex_second] at impossible
    have values := congrArg Fin.val impossible
    change (1 : Nat) = 0 at values
    omega

/-- A target-inverse window advances its own cursor and preserves the completed generator. -/
lemma chronological_second_counts (position : Fin 34)
    (selected : (chronologicalIndex position).stream = 1) :
    (chronologicalIndex position).start = secondCount position.val ∧
      (chronologicalIndex position).lowerWidth + 1 + (chronologicalIndex position).start =
        secondCount (position.val + 1) ∧
      firstCount (position.val + 1) = firstCount position.val := by
  revert selected
  refine Fin.addCases (m := 17) (n := 17) (fun index => ?_) (fun index => ?_) position
  · intro impossible
    rw [chronologicalIndex_first] at impossible
    have values := congrArg Fin.val impossible
    change (0 : Nat) = 1 at values
    omega
  · intro _selected
    rw [chronologicalIndex_second]
    change (WindowIndex.mk 1 index.rev).start = secondCount (17 + index.val) ∧
      (WindowIndex.mk 1 index.rev).lowerWidth + 1 + (WindowIndex.mk 1 index.rev).start =
        secondCount (17 + index.val + 1) ∧
      firstCount (17 + index.val + 1) = firstCount (17 + index.val)
    rw [show 17 + index.val + 1 = 17 + (index.val + 1) by omega, secondCount_add,
      secondCount_add,
      firstCount_after (17 + index.val) (Nat.le_add_right 17 index.val),
      firstCount_after (17 + (index.val + 1)) (Nat.le_add_right 17 (index.val + 1))]
    exact ⟨Sampling.stream_start 1 index, stream_end 1 index, rfl⟩

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
