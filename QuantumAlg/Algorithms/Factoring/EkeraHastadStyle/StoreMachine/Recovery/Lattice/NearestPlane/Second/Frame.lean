/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second

/-!
# Actual second-phase caller frames

The frame includes every native cross, dot, numerator, division and reduction
write. Reads outside that complete footprint survive without arithmetic or
separation premises.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- All actual cells written by the cross and five dot refreshes. -/
def prefixKeys (refs : Refs ctx width) : List StorageKey :=
  [refs.cross.first.key, refs.cross.second.key, refs.cross.third.key,
    refs.crossProductLeft.key, refs.crossProductRight.key, refs.dotProduct.key,
    refs.g11.key, refs.g21.key, refs.targetDotSecond.key, refs.targetDotFirst.key,
    refs.denominator.key]

/-- The actual metric prefix preserves every read outside its complete written footprint. -/
lemma secondPrefixInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ key ∈ prefixKeys refs, key ∉ other.storageKeys) :
    (secondPrefixStore refs store).read other = store.read other := by
  unfold secondPrefixStore secondMetricPrefixStore metricStore
  rw [LatticeDotRefresh.refreshInto_callerFrame _ _ (metricRefs refs .denominator) _ other
    (avoids refs.denominator.key (by simp [prefixKeys]))
    (avoids refs.dotProduct.key (by simp [prefixKeys]))]
  rw [LatticeDotRefresh.refreshInto_callerFrame _ _ (metricRefs refs .targetFirst) _ other
    (avoids refs.targetDotFirst.key (by simp [prefixKeys]))
    (avoids refs.dotProduct.key (by simp [prefixKeys]))]
  rw [LatticeDotRefresh.refreshInto_callerFrame _ _ (metricRefs refs .targetSecond) _ other
    (avoids refs.targetDotSecond.key (by simp [prefixKeys]))
    (avoids refs.dotProduct.key (by simp [prefixKeys]))]
  rw [LatticeDotRefresh.refreshInto_callerFrame _ _ (metricRefs refs .g21) _ other
    (avoids refs.g21.key (by simp [prefixKeys]))
    (avoids refs.dotProduct.key (by simp [prefixKeys]))]
  rw [LatticeDotRefresh.refreshInto_callerFrame _ _ (metricRefs refs .g11) _ other
    (avoids refs.g11.key (by simp [prefixKeys]))
    (avoids refs.dotProduct.key (by simp [prefixKeys]))]
  apply LatticeCross.pointCrossInto_callerFrame
  intro cell
  cases cell <;> exact avoids _ (by simp [prefixKeys, LatticeCross.mutableKey])

/-- All cells actually written by the complete second phase. -/
def mutableKeys (refs : Refs ctx width) : List StorageKey :=
  prefixKeys refs ++ [refs.numerator.key, refs.numeratorProduct.key] ++
    RoundedDiv.mutableKeys refs.division ++
      [refs.reduceProduct.key, refs.target.first.key, refs.target.second.key, refs.target.third.key]

/-- Complete caller frame of the actual second-coordinate interpreter. -/
lemma secondInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ key ∈ mutableKeys refs, key ∉ other.storageKeys) :
    (secondStep refs store).1.read other = store.read other := by
  rw [secondStep_store]
  rw [LatticeArithmetic.pointReduce_callerFrame _ _ _ _ _ other
      (avoids refs.reduceProduct.key (by simp [mutableKeys]))
      (avoids refs.target.first.key (by simp [mutableKeys]))
      (avoids refs.target.second.key (by simp [mutableKeys]))
      (avoids refs.target.third.key (by simp [mutableKeys])),
    RoundedDiv.body_callerFrame _ _ other
      (fun key present => avoids key (by simp [mutableKeys, present])),
    numeratorInto_callerFrame _ _ other
      (avoids refs.numerator.key (by simp [mutableKeys]))
      (avoids refs.numeratorProduct.key (by simp [mutableKeys])),
    secondPrefixInto_callerFrame _ _ other
      (fun key present => avoids key (by simp [mutableKeys, present]))]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
