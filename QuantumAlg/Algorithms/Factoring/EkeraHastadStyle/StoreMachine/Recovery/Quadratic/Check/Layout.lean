/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Layout
import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Layout

/-!
# Actual cells and original numerical domains for quadratic candidate checks
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

/-- Read the actual writable cell used by a later native instruction. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Candidate word width produced by the quadratic candidate machine. -/
abbrev CandidateWidth (shortWidth : Nat) : Nat :=
  QuadraticPrefix.centerWidth shortWidth + 1

/-- Public modulus width used by the quadratic discriminant. -/
abbrev ModulusWidth (shortWidth : Nat) : Nat :=
  QuadraticPrefix.discriminantWidth shortWidth

/-- Caller-owned cells for checking one positive factor candidate. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- Input reference for the candidate value. -/
  candidate : CInputRef ctx (.unsignedWord (CandidateWidth shortWidth))
  /-- Input reference for the modulus value. -/
  modulus : CInputRef ctx (.unsignedWord (ModulusWidth shortWidth))
  /-- Input reference for the zero value. -/
  zero : CInputRef ctx (.unsignedWord (CandidateWidth shortWidth))
  /-- Writable cell for the candidate wide value. -/
  candidateWide : CWriteRef ctx (.unsignedWord (ModulusWidth shortWidth))
  candidateWideRole : candidateWide.toCStorageRef.role = .workspace
  /-- Writable cell for the below modulus value. -/
  belowModulus : CWriteRef ctx .bit
  belowModulusRole : belowModulus.toCStorageRef.role = .workspace
  /-- Nested references for the modulus check stage. -/
  modulusCheck : NatModCheck.Refs ctx (ModulusWidth shortWidth) (CandidateWidth shortWidth)
  modulusCheckNumerator : modulusCheck.numerator = modulus
  modulusCheckDivisor : modulusCheck.divisor = candidate
  modulusCheckZero : modulusCheck.zero = zero
  /-- Writable cell for the eligible value. -/
  eligible : CWriteRef ctx .bit
  eligibleRole : eligible.toCStorageRef.role = .workspace

/-- Cross-stage separation for widening, range comparison, remainder, and conjunction. -/
structure PositiveSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) : Prop where
  candidateAvoidsWide : refs.candidateWide.toCStorageRef.key ∉ refs.candidate.storageKeys
  modulusAvoidsWide : refs.candidateWide.toCStorageRef.key ∉ refs.modulus.storageKeys
  zeroAvoidsWide : refs.candidateWide.toCStorageRef.key ∉ refs.zero.storageKeys
  candidateAvoidsBelow : refs.belowModulus.toCStorageRef.key ∉ refs.candidate.storageKeys
  modulusAvoidsBelow : refs.belowModulus.toCStorageRef.key ∉ refs.modulus.storageKeys
  zeroAvoidsBelow : refs.belowModulus.toCStorageRef.key ∉ refs.zero.storageKeys
  wideAvoidsBelow :
    refs.belowModulus.toCStorageRef.key ∉ (writeInput refs.candidateWide).storageKeys
  modulusCheck : NatModCheck.Separation refs.modulusCheck
  belowAvoidsDivision :
    refs.modulusCheck.division.toCStorageRef.key ∉ (writeInput refs.belowModulus).storageKeys
  belowAvoidsModAccepted :
    refs.modulusCheck.accepted.toCStorageRef.key ∉ (writeInput refs.belowModulus).storageKeys
  belowAvoidsEligible :
    refs.eligible.toCStorageRef.key ∉ (writeInput refs.belowModulus).storageKeys
  modAcceptedAvoidsEligible :
    refs.eligible.toCStorageRef.key ∉ (writeInput refs.modulusCheck.accepted).storageKeys

/-- Entry values needed by the positive-candidate suffix. -/
def PositiveInitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (before : Store ctx)
    (refs : Refs ctx shortWidth) : Prop :=
  0 < (before.read refs.candidate).toNat ∧
    0 < (before.read refs.modulus).toNat ∧ (before.read refs.zero).toNat = 0

/-- Avoidance of every write in the positive-candidate suffix. -/
structure PositiveCallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  candidateWide : refs.candidateWide.toCStorageRef.key ∉ other.storageKeys
  belowModulus : refs.belowModulus.toCStorageRef.key ∉ other.storageKeys
  division : refs.modulusCheck.division.toCStorageRef.key ∉ other.storageKeys
  modulusAccepted : refs.modulusCheck.accepted.toCStorageRef.key ∉ other.storageKeys
  eligible : refs.eligible.toCStorageRef.key ∉ other.storageKeys

/-- Caller-owned cells for the complete check, including the strict lower bound. -/
structure TotalRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- Nested references for the positive check stage. -/
  positiveCheck : Refs ctx shortWidth
  /-- Input reference for the one value. -/
  one : CInputRef ctx (.unsignedWord (CandidateWidth shortWidth))
  /-- Writable cell for the greater than one value. -/
  greaterThanOne : CWriteRef ctx .bit
  greaterThanOneRole : greaterThanOne.toCStorageRef.role = .workspace

/-- Cross-stage separation for the lower-bound decision and positive suffix. -/
structure TotalSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : TotalRefs ctx shortWidth) : Prop where
  positive : PositiveSeparation refs.positiveCheck
  oneAvoidsDecision :
    refs.greaterThanOne.toCStorageRef.key ∉ refs.one.storageKeys
  candidateAvoidsDecision :
    refs.greaterThanOne.toCStorageRef.key ∉ refs.positiveCheck.candidate.storageKeys
  modulusAvoidsDecision :
    refs.greaterThanOne.toCStorageRef.key ∉ refs.positiveCheck.modulus.storageKeys
  zeroAvoidsDecision :
    refs.greaterThanOne.toCStorageRef.key ∉ refs.positiveCheck.zero.storageKeys
  candidateFrame :
    PositiveCallerFrameAvoids refs.positiveCheck refs.positiveCheck.candidate
  modulusFrame :
    PositiveCallerFrameAvoids refs.positiveCheck refs.positiveCheck.modulus
  zeroFrame : PositiveCallerFrameAvoids refs.positiveCheck refs.positiveCheck.zero

/-- Entry values for a total candidate check. -/
def TotalInitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (before : Store ctx)
    (refs : TotalRefs ctx shortWidth) : Prop :=
  (before.read refs.one).toNat = 1 ∧
    0 < (before.read refs.positiveCheck.modulus).toNat ∧
      (before.read refs.positiveCheck.zero).toNat = 0

/-- Avoidance of every output written by the total check. -/
structure TotalCallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : TotalRefs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  decision : refs.greaterThanOne.toCStorageRef.key ∉ other.storageKeys
  positive : PositiveCallerFrameAvoids refs.positiveCheck other

/-- Exact positive-candidate range-and-divisibility flag and unconditional structural frame. -/
structure PositiveRelation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  eligible : (after.read (writeInput refs.eligible)).toBool =
    decide ((before.read refs.candidate).toNat < (before.read refs.modulus).toNat ∧
      (before.read refs.modulus).toNat % (before.read refs.candidate).toNat = 0)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    PositiveCallerFrameAvoids refs other → after.read other = before.read other

/-- Exact nontrivial-divisor flag and unconditional structural frame of the complete check. -/
structure TotalRelation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : TotalRefs ctx shortWidth) (before after : Store ctx) : Prop where
  eligible : (after.read (writeInput refs.positiveCheck.eligible)).toBool =
    decide (1 < (before.read refs.positiveCheck.candidate).toNat ∧
      (before.read refs.positiveCheck.candidate).toNat <
        (before.read refs.positiveCheck.modulus).toNat ∧
      (before.read refs.positiveCheck.modulus).toNat %
        (before.read refs.positiveCheck.candidate).toNat = 0)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    TotalCallerFrameAvoids refs other → after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck
