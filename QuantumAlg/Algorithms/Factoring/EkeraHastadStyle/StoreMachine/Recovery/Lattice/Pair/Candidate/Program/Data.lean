/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout

/-!
# Original pair-produced scan data in the actual stored coordinates
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- Pair-produced scan inputs, before later initializers supply shared constants. -/
structure PairScanData {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (samples : RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) ×
      RSA.ShortLogSample (shortLogBits N) (tradeoffBits N))
    (refs : Refs ctx N) (observation : Store ctx) : Prop where
  basis : LatticeCandidatePointMachine.BasisRawRepresents observation
    refs.scan.distance.candidate.nearest.basis
    (LatticeNearestPlaneShortLog.basis (shortLogBits N) (tradeoffBits N) samples)
  center : LatticeArithmetic.PointRawRepresents observation
    (LatticeShortLogCandidatePoint.centerRefs refs.scan.distance.candidate)
    (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N) samples).center
  originalTarget : LatticeArithmetic.PointRawRepresents observation
    refs.scan.distance.originalTarget
    (RSA.shortLogLatticeTarget (shortLogBits N) (tradeoffBits N) samples)

/-- The saved-target outcome supplies all pair-owned scan inputs. -/
theorem pairScanData_of_outcome {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before after : Store ctx)
    (outcome : LatticePairNearestPlaneSavedTarget.Outcome refs.pair before after) :
    PairScanData (LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair before)
      refs after := by
  rcases outcome with ⟨basis, first, second, third, _residual, saved, _frame⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [refs.scanNearest]
    exact ⟨basis .first, basis .second, basis .third⟩
  · simpa only [LatticeShortLogCandidatePoint.centerRefs, refs.scanNearest,
      LatticePairNearestPlaneSavedTarget.nearestRefs,
      LatticePairNearestPlaneMachine.nearestRefs, LatticeState.coordinateInput,
      ClassicalRoutines.NumberTheory.SignedWord.writeInput,
      LatticeArithmetic.writeInput] using first
  · simpa only [LatticeShortLogCandidatePoint.centerRefs, refs.scanNearest,
      LatticePairNearestPlaneSavedTarget.nearestRefs,
      LatticePairNearestPlaneMachine.nearestRefs, LatticeState.coordinateInput,
      ClassicalRoutines.NumberTheory.SignedWord.writeInput,
      LatticeArithmetic.writeInput] using second
  · simpa only [LatticeShortLogCandidatePoint.centerRefs, refs.scanNearest,
      LatticePairNearestPlaneSavedTarget.nearestRefs,
      LatticePairNearestPlaneMachine.nearestRefs, LatticeState.coordinateInput,
      ClassicalRoutines.NumberTheory.SignedWord.writeInput,
      LatticeArithmetic.writeInput] using third
  · simpa only [LatticeNearestPlaneShortLog.target,
      refs.scanOriginalTarget] using saved

/-- Equality of raw point coordinates transports a raw point representation. -/
private theorem pointRawRepresents_transport {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {before after : Store ctx}
    (pointRefs : LatticeState.PointRefs ctx width) (point : NumberTheory.IntegerPoint3)
    (represented : LatticeArithmetic.PointRawRepresents before pointRefs point)
    (firstFrame : after.read (LatticeState.coordinateInput pointRefs.first) =
      before.read (LatticeState.coordinateInput pointRefs.first))
    (secondFrame : after.read (LatticeState.coordinateInput pointRefs.second) =
      before.read (LatticeState.coordinateInput pointRefs.second))
    (thirdFrame : after.read (LatticeState.coordinateInput pointRefs.third) =
      before.read (LatticeState.coordinateInput pointRefs.third)) :
    LatticeArithmetic.PointRawRepresents after pointRefs point := by
  rcases represented with ⟨first, second, third⟩
  refine ⟨?_, ?_, ?_⟩
  · change RawSignedRepresents (after.read (LatticeState.coordinateInput pointRefs.first)) _
    rw [firstFrame]
    exact first
  · change RawSignedRepresents (after.read (LatticeState.coordinateInput pointRefs.second)) _
    rw [secondFrame]
    exact second
  · change RawSignedRepresents (after.read (LatticeState.coordinateInput pointRefs.third)) _
    rw [thirdFrame]
    exact third

/-- Pair-owned scan data survives any stage framing each named pair source. -/
theorem pairScanData_transport {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (samples : RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) ×
      RSA.ShortLogSample (shortLogBits N) (tradeoffBits N))
    (refs : Refs ctx N) (before after : Store ctx)
    (data : PairScanData samples refs before)
    (preserved : ∀ source : LatticeCandidateSlotFrames.ExternalSourceCell,
      IsPairSource source →
        after.read (LatticeCandidateSlotFrames.externalSourceInput refs.scan source) =
          before.read (LatticeCandidateSlotFrames.externalSourceInput refs.scan source)) :
    PairScanData samples refs after := by
  rcases data with ⟨basis, center, originalTarget⟩
  rcases basis with ⟨basisFirst, basisSecond, basisThird⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply pointRawRepresents_transport refs.scan.distance.candidate.nearest.basis.first
      _ basisFirst
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisFirstFirst) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisFirstSecond) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisFirstThird) (by trivial)
  · apply pointRawRepresents_transport refs.scan.distance.candidate.nearest.basis.second
      _ basisSecond
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisSecondFirst) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisSecondSecond) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisSecondThird) (by trivial)
  · apply pointRawRepresents_transport refs.scan.distance.candidate.nearest.basis.third
      _ basisThird
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisThirdFirst) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisThirdSecond) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput] using
        preserved (.candidateEntry .basisThirdThird) (by trivial)
  · apply pointRawRepresents_transport
      (LatticeShortLogCandidatePoint.centerRefs refs.scan.distance.candidate) _ center
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput,
        LatticeShortLogCandidatePoint.centerRefs] using
        preserved (.candidateEntry .centerFirst) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput,
        LatticeShortLogCandidatePoint.centerRefs] using
        preserved (.candidateEntry .centerSecond) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.candidateEntryInput,
        LatticeShortLogCandidatePoint.centerRefs] using
        preserved (.candidateEntry .centerThird) (by trivial)
  · apply pointRawRepresents_transport refs.scan.distance.originalTarget _ originalTarget
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.originalTargetInput] using
        preserved (.originalTarget .first) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.originalTargetInput] using
        preserved (.originalTarget .second) (by trivial)
    · simpa only [LatticeCandidateSlotFrames.externalSourceShape,
        LatticeCandidateSlotFrames.externalSourceInput,
        LatticeCandidateDistancePrefix.originalTargetInput] using
        preserved (.originalTarget .third) (by trivial)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
