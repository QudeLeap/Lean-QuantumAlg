/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Layout
import all QuantumAlg.Components.Classical.FirstAccepted.Option

/-!
# Actual references and original checked-selection contract

A total proper-divisor check supplies the canonical first-accepted selector.
Its scratch cells need no initial values and may name the same writable cell.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect

open Execution
open ClassicalRoutines

noncomputable section

/-- Caller-owned cells for one checked persistent-selection step. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- References for the complete proper-divisor check. -/
  check : QuadraticCandidateCheck.TotalRefs ctx shortWidth
  /-- Persistent latches and scratch cells of the canonical selector. -/
  selection : FirstAccepted.Refs ctx (QuadraticCandidateCheck.CandidateWidth shortWidth)

/-- The selector consumes the actual eligibility cell and the original candidate input. -/
def selectionInputs {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) :
    FirstAccepted.Inputs ctx (QuadraticCandidateCheck.CandidateWidth shortWidth) where
  eligible := QuadraticCandidateCheck.writeInput refs.check.positiveCheck.eligible
  candidate := refs.check.positiveCheck.candidate

/-- Original check separation and preservation of the persistent selector latches. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) : Prop where
  check : QuadraticCandidateCheck.TotalSeparation refs.check
  selection : FirstAccepted.Separated (selectionInputs refs) refs.selection
  acceptedFrame : QuadraticCandidateCheck.TotalCallerFrameAvoids refs.check
    (FirstAccepted.cellRead refs.selection.accepted)
  selectedFrame : QuadraticCandidateCheck.TotalCallerFrameAvoids refs.check
    (FirstAccepted.cellRead refs.selection.selected)

/-- Avoidance of all actual check writes and the four canonical selector references. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  check : QuadraticCandidateCheck.TotalCallerFrameAvoids refs.check other
  accepted : refs.selection.accepted.key ∉ other.storageKeys
  selected : refs.selection.selected.key ∉ other.storageKeys
  available : refs.selection.available.key ∉ other.storageKeys
  take : refs.selection.take.key ∉ other.storageKeys

/-- Interpret the selector's existing optional bounded word as a natural factor candidate. -/
def selectedOption {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : FirstAccepted.Refs ctx width) (store : Store ctx) : Option Nat :=
  (FirstAccepted.selectedOption refs store).map CShape.Value.toNat

/-- Independent proper-divisor result on the original candidate and modulus values. -/
def candidateOption {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) (store : Store ctx) : Option Nat :=
  let candidate := (store.read refs.check.positiveCheck.candidate).toNat
  let modulus := (store.read refs.check.positiveCheck.modulus).toNat
  if 1 < candidate ∧ candidate < modulus ∧ modulus % candidate = 0 then
    some candidate else none

/-- Exact ordered option update and complete structural frame of the actual checked selection. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  selected : selectedOption refs.selection after =
    FirstAccepted.retainFirst (selectedOption refs.selection before) (candidateOption refs before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect
