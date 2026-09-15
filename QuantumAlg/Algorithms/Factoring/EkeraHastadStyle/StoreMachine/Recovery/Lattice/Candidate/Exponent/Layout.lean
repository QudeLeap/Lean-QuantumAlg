/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.State
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification.Normalization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Exponent.Values

/-!
# Original candidate-exponent data with direct sign extraction
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- Caller-owned cells for classifying one candidate point's third coordinate. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The candidate point whose third coordinate is the prospective exponent. -/
  point : LatticeState.PointRefs ctx width
  /-- A caller-provided raw zero word. -/
  zero : CInputRef ctx (.unsignedWord width)
  /-- A caller-provided raw word encoding the strict upper bound `2^m`. -/
  upperBound : CInputRef ctx (.unsignedWord width)
  /-- Stored two's-complement sign bit. -/
  negative : CWriteRef ctx .bit
  negativeRole : negative.toCStorageRef.role = .workspace
  /-- Unsigned magnitude selected from the candidate's raw word. -/
  magnitude : CWriteRef ctx (.unsignedWord width)
  magnitudeRole : magnitude.toCStorageRef.role = .workspace
  /-- Caller-owned copy of the selected magnitude for exponent consumers. -/
  exponent : CWriteRef ctx (.unsignedWord width)
  exponentRole : exponent.toCStorageRef.role = .workspace
  /-- Temporary nonzero test of the selected magnitude. -/
  positive : CWriteRef ctx .bit
  positiveRole : positive.toCStorageRef.role = .workspace
  /-- Temporary strict upper-bound comparison. -/
  belowUpper : CWriteRef ctx .bit
  belowUpperRole : belowUpper.toCStorageRef.role = .workspace
  /-- Negation of the stored sign bit. -/
  nonnegative : CWriteRef ctx .bit
  nonnegativeRole : nonnegative.toCStorageRef.role = .workspace
  /-- Final acceptance bit for a positive, bounded exponent. -/
  accepted : CWriteRef ctx .bit
  acceptedRole : accepted.toCStorageRef.role = .workspace

/-- Every read-only word used by the exponent classifier. -/
inductive SourceCell where
  | candidateThird
  | zero
  | upperBound
deriving DecidableEq

/-- Every caller-owned cell overwritten by the exponent classifier. -/
inductive MutableCell where
  | negative
  | magnitude
  | exponent
  | positive
  | belowUpper
  | nonnegative
  | accepted
deriving DecidableEq

/-- Resolve one source name to the structural input consumed by the routine. -/
def sourceInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : SourceCell → CInputRef ctx (.unsignedWord width)
  | .candidateThird => LatticeState.coordinateInput refs.point.third
  | .zero => refs.zero
  | .upperBound => refs.upperBound

/-- Structural input of the candidate coordinate consumed by this machine. -/
def candidateInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : CInputRef ctx (.unsignedWord width) :=
  sourceInput refs .candidateThird

/-- Storage identity of one mutable classifier cell. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : MutableCell → StorageKey
  | .negative => refs.negative.toCStorageRef.key
  | .magnitude => refs.magnitude.toCStorageRef.key
  | .exponent => refs.exponent.toCStorageRef.key
  | .positive => refs.positive.toCStorageRef.key
  | .belowUpper => refs.belowUpper.toCStorageRef.key
  | .nonnegative => refs.nonnegative.toCStorageRef.key
  | .accepted => refs.accepted.toCStorageRef.key

/-- Every actual input avoids every write, and all writable cells are distinct. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  sourceAvoidsMutable : ∀ source cell,
    mutableKey refs cell ∉ (sourceInput refs source).storageKeys
  mutableKeyInjective : Function.Injective (mutableKey refs)

/-- Entry facts needed to interpret the literal raw operations semantically. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (before : Store ctx) (refs : Refs ctx width)
    (exponentBits : Nat) (candidate : Int) : Prop where
  /-- The literal sign classifier has its standard positive-width meaning. -/
  widthPositive : 0 < width
  /-- The candidate's third raw coordinate represents the supplied integer. -/
  candidateRepresents :
    RawSignedRepresents (before.read (candidateInput refs)) candidate
  /-- The candidate lies in the canonical signed decoding interval. -/
  candidateSignedFits :
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width candidate
  /-- The supplied zero word has its intended raw signed representation. -/
  zeroRepresents : RawSignedRepresents (before.read refs.zero) 0
  /-- The supplied upper-bound word represents exactly `2^m`. -/
  upperBoundRepresents :
    RawSignedRepresents (before.read refs.upperBound) ((2 ^ exponentBits : Nat) : Int)
  /-- `2^m` fits as an unsigned comparison operand at this word width. -/
  upperBoundFits : 2 ^ exponentBits < CShape.wordModulus width


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent
