/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross

/-!
# Actual cross-product correctness

Each coordinate reads the original six source words. Separation also preserves
coordinates already written while the two product words are reused.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def sourceValue (left right : NumberTheory.IntegerPoint3) : SourceCell → Int
  | .leftFirst => left.1
  | .leftSecond => left.2.1
  | .leftThird => left.2.2
  | .rightFirst => right.1
  | .rightSecond => right.2.1
  | .rightThird => right.2.2

private lemma source_representations (left right : LatticeState.PointRefs ctx width)
    (store : Store ctx) (leftValue rightValue : NumberTheory.IntegerPoint3)
    (leftRep : LatticeArithmetic.PointRawRepresents store left leftValue)
    (rightRep : LatticeArithmetic.PointRawRepresents store right rightValue) (source : SourceCell) :
    RawSignedRepresents (store.read (sourceInput left right source))
      (sourceValue leftValue rightValue source) := by
  cases source with
  | leftFirst => exact leftRep.1
  | leftSecond => exact leftRep.2.1
  | leftThird => exact leftRep.2.2
  | rightFirst => exact rightRep.1
  | rightSecond => exact rightRep.2.1
  | rightThird => exact rightRep.2.2

private lemma mutable_avoids (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (separation : PointCrossSeparation left right output productLeft productRight)
    (readCell writeCell : MutableCell) (different : writeCell ≠ readCell) :
    mutableKey output productLeft productRight writeCell ∉
      (writeInput (mutableRef output productLeft productRight readCell)).storageKeys := by
  simp only [CInputRef.storageKeys, List.mem_singleton]
  exact fun equal => different (separation.mutableInjective equal)

private lemma coordinate_sources_preserved (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (separation : PointCrossSeparation left right output productLeft productRight)
    (a b c d : CInputRef ctx (.unsignedWord width)) (cell : MutableCell) (store : Store ctx)
    (source : SourceCell) :
    (coordinateStore a b c d (mutableRef output productLeft productRight cell)
      productLeft productRight store).read (sourceInput left right source) =
        store.read (sourceInput left right source) :=
  coordinateCross_callerFrame _ _ _ _ _ _ _ _ _
    (separation.sourceAvoidsMutable source cell)
    (separation.sourceAvoidsMutable source .productLeft)
    (separation.sourceAvoidsMutable source .productRight)

private lemma coordinate_mutable_preserved (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (separation : PointCrossSeparation left right output productLeft productRight)
    (a b c d : CInputRef ctx (.unsignedWord width)) (cell readCell : MutableCell)
    (different : cell ≠ readCell) (notLeft : .productLeft ≠ readCell)
    (notRight : .productRight ≠ readCell) (store : Store ctx) :
    (coordinateStore a b c d (mutableRef output productLeft productRight cell)
      productLeft productRight store).read
        (writeInput (mutableRef output productLeft productRight readCell)) =
          store.read (writeInput (mutableRef output productLeft productRight readCell)) :=
  coordinateCross_callerFrame _ _ _ _ _ _ _ _ _
    (mutable_avoids _ _ _ _ _ separation _ _ different)
    (mutable_avoids _ _ _ _ _ separation _ _ notLeft)
    (mutable_avoids _ _ _ _ _ separation _ _ notRight)

/-- The nine actual native writes produce the original integer cross product modulo the width. -/
lemma pointCrossInto_correct (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (separation : PointCrossSeparation left right output productLeft productRight)
    (store : Store ctx) (leftValue rightValue : NumberTheory.IntegerPoint3)
    (leftRep : LatticeArithmetic.PointRawRepresents store left leftValue)
    (rightRep : LatticeArithmetic.PointRawRepresents store right rightValue) :
    LatticeArithmetic.PointRawRepresents
      (pointStore left right output productLeft productRight store) output
      (NumberTheory.integerPointCross leftValue rightValue) := by
  let first := coordinateStore (writeInput left.second) (writeInput right.third)
    (writeInput left.third) (writeInput right.second) output.first productLeft productRight store
  let second := coordinateStore (writeInput left.third) (writeInput right.first)
    (writeInput left.first) (writeInput right.third) output.second productLeft productRight first
  have productsDifferent : productRight.key ≠ productLeft.key := by
    intro equal
    have impossible := separation.mutableInjective
      (show mutableKey output productLeft productRight .productRight =
        mutableKey output productLeft productRight .productLeft from equal)
    cases impossible
  have original := source_representations left right store leftValue rightValue leftRep rightRep
  have afterFirst (source : SourceCell) :
      RawSignedRepresents (first.read (sourceInput left right source))
        (sourceValue leftValue rightValue source) := by
    rw [coordinate_sources_preserved left right output productLeft productRight separation
      _ _ _ _ .outputFirst store source]
    exact original source
  have afterSecond (source : SourceCell) :
      RawSignedRepresents (second.read (sourceInput left right source))
        (sourceValue leftValue rightValue source) := by
    rw [coordinate_sources_preserved left right output productLeft productRight separation
      _ _ _ _ .outputSecond first source]
    exact afterFirst source
  have firstResult := coordinateCross_correct
    (sourceInput left right .leftSecond) (sourceInput left right .rightThird)
    (sourceInput left right .leftThird) (sourceInput left right .rightSecond)
    output.first productLeft productRight store
    (separation.sourceAvoidsMutable .leftThird .productLeft)
    (separation.sourceAvoidsMutable .rightSecond .productLeft) productsDifferent
    _ _ _ _ (original .leftSecond) (original .rightThird)
      (original .leftThird) (original .rightSecond)
  have secondResult := coordinateCross_correct
    (sourceInput left right .leftThird) (sourceInput left right .rightFirst)
    (sourceInput left right .leftFirst) (sourceInput left right .rightThird)
    output.second productLeft productRight first
    (separation.sourceAvoidsMutable .leftFirst .productLeft)
    (separation.sourceAvoidsMutable .rightThird .productLeft) productsDifferent
    _ _ _ _ (afterFirst .leftThird) (afterFirst .rightFirst)
      (afterFirst .leftFirst) (afterFirst .rightThird)
  have thirdResult := coordinateCross_correct
    (sourceInput left right .leftFirst) (sourceInput left right .rightSecond)
    (sourceInput left right .leftSecond) (sourceInput left right .rightFirst)
    output.third productLeft productRight second
    (separation.sourceAvoidsMutable .leftSecond .productLeft)
    (separation.sourceAvoidsMutable .rightFirst .productLeft) productsDifferent
    _ _ _ _ (afterSecond .leftFirst) (afterSecond .rightSecond)
      (afterSecond .leftSecond) (afterSecond .rightFirst)
  refine ⟨?_, ?_, thirdResult⟩
  · change RawSignedRepresents
      ((coordinateStore _ _ _ _ output.third productLeft productRight second).read
        (writeInput output.first)) _
    rw [coordinate_mutable_preserved left right output productLeft productRight separation
      _ _ _ _ .outputThird .outputFirst (by decide) (by decide) (by decide) second,
      coordinate_mutable_preserved left right output productLeft productRight separation
        _ _ _ _ .outputSecond .outputFirst (by decide) (by decide) (by decide) first]
    exact firstResult
  · change RawSignedRepresents
      ((coordinateStore _ _ _ _ output.third productLeft productRight second).read
        (writeInput output.second)) _
    rw [coordinate_mutable_preserved left right output productLeft productRight separation
      _ _ _ _ .outputThird .outputSecond (by decide) (by decide) (by decide) second]
    exact secondResult

/-- All six source reads survive the full actual cross-product circuit. -/
lemma pointCrossInto_sources (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (separation : PointCrossSeparation left right output productLeft productRight)
    (store : Store ctx) (source : SourceCell) :
    (pointStore left right output productLeft productRight store).read
      (sourceInput left right source) = store.read (sourceInput left right source) :=
  pointCrossInto_callerFrame left right output productLeft productRight store _
    (separation.sourceAvoidsMutable source)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross
