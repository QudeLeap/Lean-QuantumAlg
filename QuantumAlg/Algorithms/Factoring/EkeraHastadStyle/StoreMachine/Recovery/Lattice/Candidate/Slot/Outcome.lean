/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Widths
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Values
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Frames

/-!
# Original source outcome of actual short-log candidate execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotOutcome

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeCandidateSlotFrames

noncomputable section

/-- The original public entry facts for an actual candidate slot. -/
structure InitialConditions {N m ell : Nat} {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (before : Store ctx) : Prop where
  basis :
    LatticeCandidatePointMachine.BasisRawRepresents before
      refs.distance.candidate.nearest.basis
      (LatticeNearestPlaneShortLog.basis m ell samples)
  center :
    LatticeArithmetic.PointRawRepresents before
      (LatticeShortLogCandidatePoint.centerRefs refs.distance.candidate)
      (LatticeNearestPlaneShortLog.trace m ell samples).center
  originalTarget :
    LatticeArithmetic.PointRawRepresents before refs.distance.originalTarget
      (RSA.shortLogLatticeTarget m ell samples)
  zero : RawSignedRepresents (before.read refs.zero) 0
  upperBound : RawSignedRepresents (before.read refs.upperBound) ((2 ^ m : Nat) : Int)
  powerModulus : (before.read refs.power.modulus).toNat = N
  powerGenerator :
    (before.read refs.power.generator).residueEncoding.val = (generator : ZMod N).val
  powerTarget :
    (before.read refs.power.targetPower).toNat =
      (RSA.targetUnit generator : ZMod N).val

/-- One actual slot preserves its original external entry invariant and retains the first
source-validated candidate for its fixed coefficient offset. -/
structure Outcome {N m ell : Nat} {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (before after : Store ctx) : Prop where
  initial : InitialConditions input generator samples refs after
  selected : LatticeCandidateSlotMachine.selectedOption refs.selector.selection after =
    RSA.retainFirstShortLogCandidate
      (LatticeCandidateSlotMachine.selectedOption refs.selector.selection before)
      (RSA.shortLogCandidateAtOffset m ell generator samples offset)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- Equality of the actual named external reads transports the original semantic entry invariant. -/
lemma initialConditions_transport {N m ell : Nat} {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (before after : Store ctx) (initial : InitialConditions input generator samples refs before)
    (preserved : ∀ source, after.read (externalSourceInput refs source) =
      before.read (externalSourceInput refs source)) :
    InitialConditions input generator samples refs after := by
  have transport (source : ExternalSourceCell)
      (predicate : CShape.Value (externalSourceShape
        (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N) source) → Prop)
      (holds : predicate (before.read (externalSourceInput refs source))) :
      predicate (after.read (externalSourceInput refs source)) := by
    rw [preserved source]
    exact holds
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact transport (.candidateEntry .basisFirstFirst)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).first.1)
      initial.basis.1.1
  · exact transport (.candidateEntry .basisFirstSecond)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).first.2.1)
      initial.basis.1.2.1
  · exact transport (.candidateEntry .basisFirstThird)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).first.2.2)
      initial.basis.1.2.2
  · exact transport (.candidateEntry .basisSecondFirst)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).second.1)
      initial.basis.2.1.1
  · exact transport (.candidateEntry .basisSecondSecond)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).second.2.1)
      initial.basis.2.1.2.1
  · exact transport (.candidateEntry .basisSecondThird)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).second.2.2)
      initial.basis.2.1.2.2
  · exact transport (.candidateEntry .basisThirdFirst)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).third.1)
      initial.basis.2.2.1
  · exact transport (.candidateEntry .basisThirdSecond)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).third.2.1)
      initial.basis.2.2.2.1
  · exact transport (.candidateEntry .basisThirdThird)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.basis m ell samples).third.2.2)
      initial.basis.2.2.2.2
  · exact transport (.candidateEntry .centerFirst)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.trace m ell samples).center.1)
      initial.center.1
  · exact transport (.candidateEntry .centerSecond)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.trace m ell samples).center.2.1)
      initial.center.2.1
  · exact transport (.candidateEntry .centerThird)
      (fun raw => RawSignedRepresents raw
        (LatticeNearestPlaneShortLog.trace m ell samples).center.2.2)
      initial.center.2.2
  · exact transport (.originalTarget .first)
      (fun raw => RawSignedRepresents raw (RSA.shortLogLatticeTarget m ell samples).1)
      initial.originalTarget.1
  · exact transport (.originalTarget .second)
      (fun raw => RawSignedRepresents raw (RSA.shortLogLatticeTarget m ell samples).2.1)
      initial.originalTarget.2.1
  · exact transport (.originalTarget .third)
      (fun raw => RawSignedRepresents raw (RSA.shortLogLatticeTarget m ell samples).2.2)
      initial.originalTarget.2.2
  · exact transport (.zero)
      (fun raw => RawSignedRepresents raw 0)
      initial.zero
  · exact transport (.upperBound)
      (fun raw => RawSignedRepresents raw ((2 ^ m : Nat) : Int))
      initial.upperBound
  · exact transport (.modulus)
      (fun raw => raw.toNat = N)
      initial.powerModulus
  · exact transport (.generator)
      (fun raw => raw.residueEncoding.val = (generator : ZMod N).val)
      initial.powerGenerator
  · exact transport (.targetPower)
      (fun raw => raw.toNat = (RSA.targetUnit generator : ZMod N).val)
      initial.powerTarget

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotOutcome
