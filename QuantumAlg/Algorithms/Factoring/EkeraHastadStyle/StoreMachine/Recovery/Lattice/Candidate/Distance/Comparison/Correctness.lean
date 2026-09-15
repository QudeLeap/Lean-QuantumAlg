/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Comparison.Frames

/-!
# Actual near-target comparison correctness
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Copying followed by three actual shifts computes eight times the input modulo its width. -/
theorem copyScaleInto_read_mod (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((copyScaleStep input output store).1.read (writeInput output)).toNat =
      (8 * (store.read input).toNat) % 2 ^ width := by
  change ((ClassicalRoutines.Word.PowerOfTwo.shiftStore 3 output
    (store.applyOp (copyOp input output))).read (writeInput output)).toNat = _
  rw [ClassicalRoutines.Word.PowerOfTwo.shiftInto_read]
  have copied : (store.applyOp (copyOp input output)).read (writeInput output) =
      store.read input := by
    change (store.applyOp (copyOp input output)).read
      (.storage (copyOp input output).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    rfl
  rw [copied]
  norm_num [Nat.mul_comm]

/-- The original scaled operand bound gives exact unsigned scaling with arbitrary scratch. -/
theorem copyScaleInto_read (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) (value : Nat)
    (inputValue : (store.read input).toNat = value)
    (fits : 8 * value < CShape.wordModulus width) :
    ((copyScaleStep input output store).1.read (writeInput output)).toNat = 8 * value := by
  rw [copyScaleInto_read_mod, inputValue]
  exact Nat.mod_eq_of_lt fits

private theorem raw_of_toNat (word : CShape.Word width) (value : Nat)
    (equal : word.toNat = value) : RawSignedRepresents word (value : Int) := by
  change Int.ModEq _ (word.toNat : Int) (value : Int)
  rw [equal]

/-- The actual multiplication stores the exact original range square under its original bound. -/
theorem squareOp_read (refs : Refs ctx width) (store : Store ctx) (value : Nat)
    (input : (store.read refs.upperBound).toNat = value)
    (fits : value * value < CShape.wordModulus width) :
    ((store.applyOp (squareOp refs)).read (writeInput refs.rangeSquare)).toNat = value * value := by
  apply rawSignedRepresents_toNat_eq_of_lt _ _ fits
  change RawSignedRepresents ((store.applyOp (squareOp refs)).read
    (.storage (squareOp refs).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  change RawSignedRepresents (Resource.WordBinaryOpcode.eval .mulLow width
    (.product (store.read refs.upperBound) (store.read refs.upperBound)))
      ((value * value : Nat) : Int)
  simpa only [Nat.cast_mul] using rawSignedWordRepresents_mulLow
    (store.read refs.upperBound) (store.read refs.upperBound) (value : Int) (value : Int)
    (raw_of_toNat _ value input) (raw_of_toNat _ value input)

/-- The original range square remains available while its scaled copy is computed. -/
theorem rangeSquare_at_add (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (copyScaleStep (writeInput refs.rangeSquare) refs.scaledRange store).1.read
        (writeInput refs.rangeSquare) = store.read (writeInput refs.rangeSquare) :=
  copyScaleInto_callerFrame _ _ _ _
    (mutable_avoids refs separation refs.rangeSquare .rangeSquare .scaledRange rfl (by decide))

/-- The final actual range addition stores exactly nine times the original range square. -/
theorem addRangeOp_read (refs : Refs ctx width) (store : Store ctx) (square : Nat)
    (scaled : (store.read (writeInput refs.scaledRange)).toNat = 8 * square)
    (original : (store.read (writeInput refs.rangeSquare)).toNat = square)
    (fits : 9 * square < CShape.wordModulus width) :
    ((store.applyOp (addRangeOp refs)).read (writeInput refs.scaledRange)).toNat = 9 * square := by
  apply rawSignedRepresents_toNat_eq_of_lt _ _ fits
  change RawSignedRepresents ((store.applyOp (addRangeOp refs)).read
    (.storage (addRangeOp refs).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  have sum : ((9 * square : Nat) : Int) = ((8 * square : Nat) : Int) + (square : Int) := by
    push_cast
    ring
  rw [sum]
  exact rawSignedWordRepresents_add _ _ _ _
    (raw_of_toNat _ _ scaled) (raw_of_toNat _ _ original)

/-- The two actual stored comparison operands equal their original source arithmetic values. -/
theorem preparedStore_operands (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (distance upperBound : Nat)
    (initial : InitialConditions store refs distance upperBound) :
    ((preparedStore refs store).read (writeInput refs.scaledDistance)).toNat = 8 * distance ∧
      ((preparedStore refs store).read (writeInput refs.scaledRange)).toNat =
        9 * (upperBound * upperBound) := by
  have distanceInput :=
    rawSignedRepresents_toNat_eq_of_lt _ initial.distanceRaw initial.distanceFits
  have upperInput :=
    rawSignedRepresents_toNat_eq_of_lt _ initial.upperBoundRaw initial.upperBoundFits
  let copied := (copyScaleStep refs.distance refs.scaledDistance store).1
  have upperFrame : copied.read refs.upperBound = store.read refs.upperBound :=
    copyScaleInto_callerFrame _ _ _ _ (separation.sourceAvoidsMutable .upperBound .scaledDistance)
  have square := squareOp_read refs copied upperBound (by rw [upperFrame]; exact upperInput)
    initial.rangeSquareFits
  have eightFits : 8 * (upperBound * upperBound) < CShape.wordModulus width :=
    (show 8 * (upperBound * upperBound) ≤ 9 * (upperBound * upperBound) by omega).trans_lt
      initial.scaledRangeFits
  have eight := copyScaleInto_read (writeInput refs.rangeSquare) refs.scaledRange
    (copied.applyOp (squareOp refs)) (upperBound * upperBound) square eightFits
  refine ⟨?_, ?_⟩
  · rw [preparedStore_distance_frame refs separation store]
    exact copyScaleInto_read refs.distance refs.scaledDistance store distance
      distanceInput initial.scaledDistanceFits
  · apply addRangeOp_read refs _ (upperBound * upperBound) eight _ initial.scaledRangeFits
    rw [rangeSquare_at_add refs separation]
    exact square

/-- Actual less-than compares exactly the two words currently stored in the supplied cells. -/
theorem compareOp_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (compareOp refs)).read (writeInput refs.accepted)).toBool =
      decide ((store.read (writeInput refs.scaledDistance)).toNat <
        (store.read (writeInput refs.scaledRange)).toNat) := by
  change ((store.applyOp (compareOp refs)).read
    (.storage (compareOp refs).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  rfl

/-- Actual stored decision and the complete original four-cell caller frame. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (distance upperBound : Nat) : Prop where
  accepted : (after.read (writeInput refs.accepted)).toBool =
    decide (8 * distance < 9 * (upperBound * upperBound))
  callerFrame : CallerFrame refs before after

/-- The actual eleven-instruction circuit realizes the original scaled near-target comparison. -/
theorem scaleInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (distance upperBound : Nat)
    (initial : InitialConditions store refs distance upperBound) :
    Outcome refs store (scaleStep refs store).1 distance upperBound := by
  have operands := preparedStore_operands refs separation store distance upperBound initial
  refine ⟨?_, scaleInto_callerFrame refs store⟩
  change (((preparedStore refs store).applyOp (compareOp refs)).read
    (writeInput refs.accepted)).toBool = _
  rw [compareOp_read, operands.1, operands.2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale
