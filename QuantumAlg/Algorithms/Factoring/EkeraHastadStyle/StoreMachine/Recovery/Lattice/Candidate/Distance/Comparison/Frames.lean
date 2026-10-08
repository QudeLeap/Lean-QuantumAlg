/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Comparison

/-!
# Actual near-target comparison frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

omit [BitWord.Selected model] in
/-- Actual writable inputs avoid every differently named destination. -/
theorem mutable_avoids (refs : Refs ctx width) (separation : Separation refs)
    {shape : CShape} (source : CWriteRef ctx shape) (saved written : MutableCell)
    (sourceKey : source.key = mutableKey refs saved) (different : saved ≠ written) :
    mutableKey refs written ∉ (writeInput source).storageKeys := by
  change mutableKey refs written ∉ [source.key]
  simp only [List.mem_singleton]
  rw [sourceKey]
  intro equal
  exact different (separation.mutableInjective equal.symm)

/-- Actual copying and all three shifts change only their supplied destination. -/
theorem copyScaleInto_callerFrame (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : output.key ∉ other.storageKeys) :
    (copyScaleStep (model := model) input output store).1.read other = store.read other := by
  change (ClassicalRoutines.Word.PowerOfTwo.shiftStore 3 output
    (store.applyOp (copyOp input output))).read other = _
  rw [ClassicalRoutines.Word.PowerOfTwo.shiftInto_callerFrame _ _ _ other avoids,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids]

/-- The actual store immediately before comparing the two completed operands. -/
def preparedStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((copyScaleStep (model := model) (writeInput refs.rangeSquare) refs.scaledRange
    ((copyScaleStep (model := model) refs.distance refs.scaledDistance store).1.applyOp
      (squareOp refs))).1).applyOp
      (addRangeOp refs)

/-- Reads outside the original four destinations form the complete caller frame. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ cell, mutableKey refs cell ∉ other.storageKeys) → after.read other = before.read other

/-- The eleven actual instructions preserve every read outside their original write footprint. -/
theorem scaleInto_callerFrame (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (scaleStep (model := model) refs store).1 := by
  intro shape other avoids
  change ((preparedStore refs store).applyOp (compareOp refs)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ (avoids .accepted)]
  unfold preparedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ (avoids .scaledRange),
    copyScaleInto_callerFrame _ _ _ other (avoids .scaledRange),
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ (avoids .rangeSquare),
    copyScaleInto_callerFrame _ _ _ other (avoids .scaledDistance)]

/-- The completed scaled distance survives all subsequent range arithmetic. -/
theorem preparedStore_distance_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (preparedStore (model := model) refs store).read (writeInput refs.scaledDistance) =
      (copyScaleStep (model := model) refs.distance refs.scaledDistance store).1.read
        (writeInput refs.scaledDistance) := by
  have range := mutable_avoids refs separation refs.scaledDistance
    .scaledDistance .scaledRange rfl (by decide)
  have square := mutable_avoids refs separation refs.scaledDistance
    .scaledDistance .rangeSquare rfl (by decide)
  unfold preparedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ range,
    copyScaleInto_callerFrame _ _ _ _ range,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ square]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale
