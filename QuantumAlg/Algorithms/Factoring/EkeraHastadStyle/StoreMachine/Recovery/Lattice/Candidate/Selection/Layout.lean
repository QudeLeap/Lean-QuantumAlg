/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Resources

/-!
# Original candidate-selection data with direct stored-bit control
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural input of an original writable candidate-selection cell. -/
abbrev writeInput {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Original three predicates, candidate, two conjunction cells and persistent first-success
result. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  nearTarget : CInputRef ctx .bit
  exponentInRange : CInputRef ctx .bit
  powerMatches : CInputRef ctx .bit
  candidate : CInputRef ctx (.unsignedWord width)
  intermediate : CWriteRef ctx .bit
  intermediateRole : intermediate.toCStorageRef.role = .workspace
  eligible : CWriteRef ctx .bit
  eligibleRole : eligible.toCStorageRef.role = .workspace
  selection : ClassicalRoutines.FirstAccepted.Direct.Refs ctx width

/-- Every actual destination in the closing candidate suffix. -/
inductive MutableCell where
  | intermediate
  | eligible
  | accepted
  | selected
deriving DecidableEq

/-- Resolve each original mutable output to its actual storage identity. -/
def mutableKey (refs : Refs ctx width) : MutableCell → StorageKey
  | .intermediate => refs.intermediate.key
  | .eligible => refs.eligible.key
  | .accepted => refs.selection.accepted.key
  | .selected => refs.selection.selected.key

/-- The original predicate and candidate sources avoid all distinct actual outputs. -/
structure Separation (refs : Refs ctx width) : Prop where
  nearTargetAvoidsMutable : ∀ cell, mutableKey refs cell ∉ refs.nearTarget.storageKeys
  exponentInRangeAvoidsMutable : ∀ cell, mutableKey refs cell ∉ refs.exponentInRange.storageKeys
  powerMatchesAvoidsMutable : ∀ cell, mutableKey refs cell ∉ refs.powerMatches.storageKeys
  candidateAvoidsMutable : ∀ cell, mutableKey refs cell ∉ refs.candidate.storageKeys
  mutableKeyInjective : Function.Injective (mutableKey refs)

/-- The original three-check candidate predicate, computed from the actual input store. -/
def eligibility (refs : Refs ctx width) (store : Store ctx) : Bool :=
  ((store.read refs.nearTarget).toBool && (store.read refs.exponentInRange).toBool) &&
    (store.read refs.powerMatches).toBool

/-- The actual selection suffix preserves every caller read outside its four original
destinations. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ cell, mutableKey refs cell ∉ other.storageKeys) → after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector
