/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Exponent.Suffix

/-!
# Original candidate-exponent meaning of actual execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Every original raw output, Boolean check and external caller read after actual execution. -/
structure Outcome (refs : Refs ctx width) (exponentBits : Nat) (candidate : Int)
    (before after : Store ctx) : Prop where
  magnitude : RawSignedRepresents (after.read (writeInput refs.magnitude)) (candidate.natAbs : Int)
  exponent : RawSignedRepresents (after.read (writeInput refs.exponent)) (candidate.natAbs : Int)
  negative : (after.read (writeInput refs.negative)).toBool = decide (candidate < 0)
  positive : (after.read (writeInput refs.positive)).toBool = decide (candidate.natAbs ≠ 0)
  belowUpper : (after.read (writeInput refs.belowUpper)).toBool =
    decide (candidate.natAbs < 2 ^ exponentBits)
  nonnegative : (after.read (writeInput refs.nonnegative)).toBool = decide (0 ≤ candidate)
  accepted : (after.read (writeInput refs.accepted)).toBool =
    decide (ExponentInRange exponentBits candidate)
  callerFrame : CallerFrame refs before after

/-- The actual stored sign selects the magnitude used by the original strict candidate tests. -/
theorem candidateExponentInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (exponentBits : Nat) (candidate : Int)
    (initial : InitialConditions store refs exponentBits candidate) :
    Outcome refs exponentBits candidate store (exponentStep refs store).1 := by
  let normalized := (normalizeStep refs store).1
  have decoded := rawSignedSignMagnitude initial.widthPositive
    (store.read (candidateInput refs)) candidate initial.candidateRepresents
    initial.candidateSignedFits
  have magnitudeValue : (normalized.read (writeInput refs.magnitude)).toNat =
      candidate.natAbs :=
    (normalizeMagnitude_correct (model := model) (candidateInput refs)
      refs.negative refs.magnitude store
      (separation.sourceAvoidsMutable .candidateThird .negative)).trans decoded.2
  have different : refs.magnitude.key ≠ refs.negative.key := by
    intro equal
    have impossible : MutableCell.magnitude = .negative := separation.mutableKeyInjective equal
    cases impossible
  have negativeValue : (normalized.read (writeInput refs.negative)).toBool =
      decide (candidate < 0) :=
    (normalizeMagnitude_sign (model := model) (candidateInput refs)
      refs.negative refs.magnitude store
      different).trans decoded.1
  have zeroValue : (normalized.read refs.zero).toNat = 0 := by
    have frame := normalize_source_frame refs separation store .zero
    change normalized.read refs.zero = store.read refs.zero at frame
    rw [frame]
    exact rawSignedRepresents_toNat_eq_of_lt _ initial.zeroRepresents (CShape.wordModulus_pos width)
  have upperValue : (normalized.read refs.upperBound).toNat = 2 ^ exponentBits := by
    have frame := normalize_source_frame refs separation store .upperBound
    change normalized.read refs.upperBound = store.read refs.upperBound at frame
    rw [frame]
    exact rawSignedRepresents_toNat_eq_of_lt _ initial.upperBoundRepresents initial.upperBoundFits
  have suffix := suffixInto_correct refs separation normalized candidate.natAbs (2 ^ exponentBits)
    (decide (candidate < 0)) magnitudeValue negativeValue zeroValue upperValue
  refine ⟨?_, rawSignedRepresents_of_toNat _ _ suffix.exponent, ?_, suffix.positive,
    suffix.belowUpper, ?_, ?_, candidateExponentInto_callerFrame refs store⟩
  · apply rawSignedRepresents_of_toNat
    change ((suffixStore refs normalized).read (writeInput refs.magnitude)).toNat = _
    rw [suffix_magnitude_frame refs separation, magnitudeValue]
  · change ((suffixStore refs normalized).read (writeInput refs.negative)).toBool = _
    rw [suffix_negative_frame refs separation, negativeValue]
  · exact suffix.nonnegative.trans (notNegativeBit candidate)
  · exact suffix.accepted.trans (by rw [notNegativeBit, candidateRangeBit])

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent
