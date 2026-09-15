/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap

/-!
# Actual lattice row exchange correctness

The six final words equal the six opposite original words. The original
seven-cell separation derives every chronological frame; scratch may initially
contain any word and remains explicitly present in the final context.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap

open LatticeArithmetic (writeInput)
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem cell_ne (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width))
    (separation : PointSwapSeparation left right scratch) (a b : PointSwapCell)
    (different : a ≠ b) :
    pointSwapCellKey left right scratch a ≠ pointSwapCellKey left right scratch b :=
  fun equal => different (separation.keyInjective equal)

private theorem named_frame (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width))
    (separation : PointSwapSeparation left right scratch) (store : Store ctx)
    (a b source : PointSwapCell) (avoidA : a ≠ source) (avoidB : b ≠ source)
    (avoidScratch : .scratch ≠ source) :
    (coordinateSwapStore (pointSwapCellRef left right scratch a)
      (pointSwapCellRef left right scratch b) scratch store).read
        (writeInput (pointSwapCellRef left right scratch source)) =
      store.read (writeInput (pointSwapCellRef left right scratch source)) := by
  apply coordinateSwap_callerFrame
  · change pointSwapCellKey left right scratch a ∉ [pointSwapCellKey left right scratch source]
    simpa only [List.mem_singleton] using cell_ne left right scratch separation a source avoidA
  · change pointSwapCellKey left right scratch b ∉ [pointSwapCellKey left right scratch source]
    simpa only [List.mem_singleton] using cell_ne left right scratch separation b source avoidB
  · change pointSwapCellKey left right scratch .scratch ∉
      [pointSwapCellKey left right scratch source]
    simpa only [List.mem_singleton] using
      cell_ne left right scratch separation .scratch source avoidScratch

/-- Every actual final row word is exactly the corresponding original word from the opposite row. -/
theorem pointSwap_reads (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width))
    (separation : PointSwapSeparation left right scratch) (store : Store ctx) :
    (pointSwapStore left right scratch store).read (writeInput left.first) =
        store.read (writeInput right.first) ∧
      (pointSwapStore left right scratch store).read (writeInput left.second) =
        store.read (writeInput right.second) ∧
      (pointSwapStore left right scratch store).read (writeInput left.third) =
        store.read (writeInput right.third) ∧
      (pointSwapStore left right scratch store).read (writeInput right.first) =
        store.read (writeInput left.first) ∧
      (pointSwapStore left right scratch store).read (writeInput right.second) =
        store.read (writeInput left.second) ∧
      (pointSwapStore left right scratch store).read (writeInput right.third) =
        store.read (writeInput left.third) := by
  let afterFirst := coordinateSwapStore left.first right.first scratch store
  let afterSecond := coordinateSwapStore left.second right.second scratch afterFirst
  have firstResult := coordinateSwap_reads left.first right.first scratch store
    (cell_ne left right scratch separation .leftFirst .rightFirst (by decide))
    (cell_ne left right scratch separation .leftFirst .scratch (by decide))
    (cell_ne left right scratch separation .rightFirst .scratch (by decide))
  have secondResult := coordinateSwap_reads left.second right.second scratch afterFirst
    (cell_ne left right scratch separation .leftSecond .rightSecond (by decide))
    (cell_ne left right scratch separation .leftSecond .scratch (by decide))
    (cell_ne left right scratch separation .rightSecond .scratch (by decide))
  have thirdResult := coordinateSwap_reads left.third right.third scratch afterSecond
    (cell_ne left right scratch separation .leftThird .rightThird (by decide))
    (cell_ne left right scratch separation .leftThird .scratch (by decide))
    (cell_ne left right scratch separation .rightThird .scratch (by decide))
  unfold pointSwapStore
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [named_frame left right scratch separation _ .leftThird .rightThird
      .leftFirst (by decide) (by decide) (by decide)]
    rw [named_frame left right scratch separation _ .leftSecond .rightSecond
      .leftFirst (by decide) (by decide) (by decide)]
    rw [firstResult.1]
  · rw [named_frame left right scratch separation _ .leftThird .rightThird
      .leftSecond (by decide) (by decide) (by decide)]
    rw [secondResult.1]
    dsimp only [afterFirst, afterSecond]
    rw [named_frame left right scratch separation _ .leftFirst .rightFirst
      .rightSecond (by decide) (by decide) (by decide)]
  · rw [thirdResult.1]
    dsimp only [afterFirst, afterSecond]
    rw [named_frame left right scratch separation _ .leftSecond .rightSecond
      .rightThird (by decide) (by decide) (by decide)]
    rw [named_frame left right scratch separation _ .leftFirst .rightFirst
      .rightThird (by decide) (by decide) (by decide)]
  · rw [named_frame left right scratch separation _ .leftThird .rightThird
      .rightFirst (by decide) (by decide) (by decide)]
    rw [named_frame left right scratch separation _ .leftSecond .rightSecond
      .rightFirst (by decide) (by decide) (by decide)]
    rw [firstResult.2]
  · rw [named_frame left right scratch separation _ .leftThird .rightThird
      .rightSecond (by decide) (by decide) (by decide)]
    rw [secondResult.2]
    dsimp only [afterFirst, afterSecond]
    rw [named_frame left right scratch separation _ .leftFirst .rightFirst
      .leftSecond (by decide) (by decide) (by decide)]
  · rw [thirdResult.2]
    dsimp only [afterFirst, afterSecond]
    rw [named_frame left right scratch separation _ .leftSecond .rightSecond
      .leftThird (by decide) (by decide) (by decide)]
    rw [named_frame left right scratch separation _ .leftFirst .rightFirst
      .leftThird (by decide) (by decide) (by decide)]

/-- The actual word exchange preserves the original raw integer representation of both points. -/
theorem pointSwap_correct (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width))
    (separation : PointSwapSeparation left right scratch) (store : Store ctx)
    (leftValue rightValue : NumberTheory.IntegerPoint3)
    (leftRep : LatticeArithmetic.PointRawRepresents store left leftValue)
    (rightRep : LatticeArithmetic.PointRawRepresents store right rightValue) :
    LatticeArithmetic.PointRawRepresents (pointSwapStore left right scratch store) left rightValue ∧
      LatticeArithmetic.PointRawRepresents
        (pointSwapStore left right scratch store) right leftValue := by
  have reads := pointSwap_reads left right scratch separation store
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [reads.1]; exact rightRep.1
  · rw [reads.2.1]; exact rightRep.2.1
  · rw [reads.2.2.1]; exact rightRep.2.2
  · rw [reads.2.2.2.1]; exact leftRep.1
  · rw [reads.2.2.2.2.1]; exact leftRep.2.1
  · rw [reads.2.2.2.2.2]; exact leftRep.2.2

/-- The actual final scratch contains the original left row's third coordinate. -/
theorem pointSwap_scratch (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width))
    (separation : PointSwapSeparation left right scratch) (store : Store ctx) :
    (pointSwapStore left right scratch store).read (writeInput scratch) =
      store.read (writeInput left.third) := by
  unfold pointSwapStore
  rw [coordinateSwap_scratch _ _ _ _
    (cell_ne left right scratch separation .leftThird .scratch (by decide))
    (cell_ne left right scratch separation .rightThird .scratch (by decide))]
  rw [named_frame left right scratch separation _ .leftSecond .rightSecond .leftThird
    (by decide) (by decide) (by decide),
    named_frame left right scratch separation _ .leftFirst .rightFirst .leftThird
      (by decide) (by decide) (by decide)]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap
