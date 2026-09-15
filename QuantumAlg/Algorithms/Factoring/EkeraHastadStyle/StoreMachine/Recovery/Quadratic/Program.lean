/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Pair
import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Typed quadratic factor recovery

This module connects the literal quadratic candidate generator to two ordered
proper-divisor checks and their shared first-success selector.  Its public
relation is expressed only through the entry short logarithm, modulus, and
persistent selection state.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticRecoveryMachine

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Candidate generation wired to two checked selectors. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- Nested references for the candidates stage. -/
  candidates : QuadraticCandidates.Refs ctx shortWidth
  /-- Nested references for the pair stage. -/
  pair : QuadraticCandidatePairSelect.Refs ctx shortWidth
  firstCandidate : pair.first.check.positiveCheck.candidate =
    QuadraticCandidates.firstCandidate candidates
  secondCandidate : pair.second.check.positiveCheck.candidate =
    QuadraticCandidates.secondCandidate candidates
  firstModulus : pair.first.check.positiveCheck.modulus =
    candidates.quadraticPrefix.modulus
  secondModulus : pair.second.check.positiveCheck.modulus =
    candidates.quadraticPrefix.modulus

/-- Candidate generation frames every constant and persistent latch used later. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) : Prop where
  candidates : QuadraticCandidates.Separation refs.candidates
  pair : QuadraticCandidatePairSelect.Separation refs.pair
  firstOneFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    refs.pair.first.check.one
  firstModulusFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    refs.pair.first.check.positiveCheck.modulus
  firstZeroFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    refs.pair.first.check.positiveCheck.zero
  secondOneFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    refs.pair.second.check.one
  secondModulusFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    refs.pair.second.check.positiveCheck.modulus
  secondZeroFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    refs.pair.second.check.positiveCheck.zero
  acceptedFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    (FirstAccepted.cellRead refs.pair.first.selection.accepted)
  selectedFrame : QuadraticCandidates.CallerFrameAvoids refs.candidates
    (FirstAccepted.cellRead refs.pair.first.selection.selected)

/-- Entry values for candidate generation and both total checks. -/
def InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (before : Store ctx)
    (refs : Refs ctx shortWidth) : Prop :=
  QuadraticCandidatePairSelect.InitialConditions before refs.pair

/-- Avoidance of every write in candidate generation and both checks. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  candidates : QuadraticCandidates.CallerFrameAvoids refs.candidates other
  pair : QuadraticCandidatePairSelect.CallerFrameAvoids refs.pair other

/-- First pure quadratic candidate at one entry observation. -/
def firstCandidateValue {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth)
    (before : Store ctx) : Nat :=
  (before.read refs.candidates.quadraticPrefix.shortLog).toNat + 1 -
    Nat.sqrt
      (((before.read refs.candidates.quadraticPrefix.shortLog).toNat + 1) ^ 2 -
        (before.read refs.candidates.quadraticPrefix.modulus).toNat)

/-- Second pure quadratic candidate at one entry observation. -/
def secondCandidateValue {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth)
    (before : Store ctx) : Nat :=
  (before.read refs.candidates.quadraticPrefix.shortLog).toNat + 1 +
    Nat.sqrt
      (((before.read refs.candidates.quadraticPrefix.shortLog).toNat + 1) ^ 2 -
        (before.read refs.candidates.quadraticPrefix.modulus).toNat)

/-- Proper-divisor option for one pure natural candidate. -/
def checkedCandidateOption (candidate modulus : Nat) : Option Nat :=
  if 1 < candidate ∧ candidate < modulus ∧ modulus % candidate = 0 then
    some candidate
  else
    none

/-- Pure first candidate option. -/
def firstOption {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth)
    (before : Store ctx) : Option Nat :=
  checkedCandidateOption (firstCandidateValue refs before)
    (before.read refs.candidates.quadraticPrefix.modulus).toNat

/-- Pure second candidate option. -/
def secondOption {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth)
    (before : Store ctx) : Option Nat :=
  checkedCandidateOption (secondCandidateValue refs before)
    (before.read refs.candidates.quadraticPrefix.modulus).toNat

/-- Closed pure value selected by the same two ordered candidate checks. -/
def recoveryValue (modulus shortLog : Nat) : Option Nat :=
  let center := shortLog + 1
  let root := Nat.sqrt (center ^ 2 - modulus)
  FirstAccepted.retainFirst
    (FirstAccepted.retainFirst none
      (checkedCandidateOption (center - root) modulus))
    (checkedCandidateOption (center + root) modulus)

/-- The closed machine value is the public RSA short-log recovery value. -/
theorem recoveryValue_eq_recoverFactorFromShortLog (modulus shortLog : Nat) :
    recoveryValue modulus shortLog =
      RSA.recoverFactorFromShortLog modulus shortLog := by
  rw [RSA.recoverFactorFromShortLog_eq]
  unfold recoveryValue RSA.quadraticDiscriminant
  simp only [RSA.quadraticCenter]
  by_cases firstValid :
      1 < shortLog + 1 - Nat.sqrt ((shortLog + 1) ^ 2 - modulus) ∧
        shortLog + 1 - Nat.sqrt ((shortLog + 1) ^ 2 - modulus) < modulus ∧
          modulus % (shortLog + 1 - Nat.sqrt ((shortLog + 1) ^ 2 - modulus)) = 0
  · simp [checkedCandidateOption, FirstAccepted.retainFirst,
      firstValid]
  · by_cases secondValid :
        1 < shortLog + 1 + Nat.sqrt ((shortLog + 1) ^ 2 - modulus) ∧
          shortLog + 1 + Nat.sqrt ((shortLog + 1) ^ 2 - modulus) < modulus ∧
            modulus % (shortLog + 1 + Nat.sqrt
              ((shortLog + 1) ^ 2 - modulus)) = 0
    · simp [checkedCandidateOption, FirstAccepted.retainFirst,
        firstValid, secondValid]
    · simp [checkedCandidateOption, FirstAccepted.retainFirst,
        firstValid, secondValid]

/-- The actual execution retains the first factor and preserves every disjoint caller read. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  selected : QuadraticCandidateSelect.selectedOption refs.pair.first.selection after =
    FirstAccepted.retainFirst
      (FirstAccepted.retainFirst
        (QuadraticCandidateSelect.selectedOption refs.pair.first.selection before)
        (firstOption refs before)) (secondOption refs before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}

/-- Generate both candidates, then check and select them in their original order. -/
def into (refs : Refs ctx shortWidth) : Circuit ctx ctx :=
  .seq (QuadraticCandidates.into refs.candidates) (QuadraticCandidatePairSelect.into refs.pair)

/-- The complete actual caller store and chronological path of candidate construction and checks. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  let candidates := QuadraticCandidates.step refs.candidates store
  let pair := QuadraticCandidatePairSelect.step refs.pair candidates.1
  (pair.1, (candidates.2, pair.2))

/-- The full interpreter equation holds for every history and external quantum reference. -/
theorem into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) := by
  simp only [into, step, Circuit.execute_seq, QuadraticCandidates.into_execute,
    QuadraticCandidatePairSelect.into_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Every disjoint caller read survives both actual computation stages. -/
theorem into_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other :=
  (QuadraticCandidatePairSelect.into_callerFrame refs.pair _ other avoids.pair).trans
    (QuadraticCandidates.into_callerFrame refs.candidates store other avoids.candidates)

/-- Actual candidate construction followed by the checked selector realizes quadratic recovery. -/
theorem into_correct (refs : Refs ctx shortWidth) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    Relation refs store (step refs store).1 := by
  let middle := (QuadraticCandidates.step refs.candidates store).1
  have candidates := QuadraticCandidates.step_correct refs.candidates separation.candidates store
  have one₁ := candidates.callerFrame _ separation.firstOneFrame
  have modulus₁ := candidates.callerFrame _ separation.firstModulusFrame
  have zero₁ := candidates.callerFrame _ separation.firstZeroFrame
  have one₂ := candidates.callerFrame _ separation.secondOneFrame
  have modulus₂ := candidates.callerFrame _ separation.secondModulusFrame
  have zero₂ := candidates.callerFrame _ separation.secondZeroFrame
  have pairInitial : QuadraticCandidatePairSelect.InitialConditions middle refs.pair := by
    unfold QuadraticCandidatePairSelect.InitialConditions
      QuadraticCandidateCheck.TotalInitialConditions
    rw [one₁, modulus₁, zero₁, one₂, modulus₂, zero₂]
    exact initial
  have pair := QuadraticCandidatePairSelect.into_correct refs.pair separation.pair
    middle pairInitial
  have accepted := candidates.callerFrame _ separation.acceptedFrame
  have selected := candidates.callerFrame _ separation.selectedFrame
  have previous : QuadraticCandidateSelect.selectedOption refs.pair.first.selection middle =
      QuadraticCandidateSelect.selectedOption refs.pair.first.selection store := by
    unfold QuadraticCandidateSelect.selectedOption FirstAccepted.selectedOption
    rw [accepted, selected]
  have firstValue : (middle.read refs.pair.first.check.positiveCheck.candidate).toNat =
      firstCandidateValue refs store := by
    rw [refs.firstCandidate]
    exact candidates.first
  have secondValue : (middle.read refs.pair.second.check.positiveCheck.candidate).toNat =
      secondCandidateValue refs store := by
    rw [refs.secondCandidate]
    exact candidates.second
  have firstOptionValue : QuadraticCandidateSelect.candidateOption refs.pair.first middle =
      firstOption refs store := by
    unfold QuadraticCandidateSelect.candidateOption firstOption checkedCandidateOption
    rw [firstValue, modulus₁, refs.firstModulus]
  have secondOptionValue : QuadraticCandidateSelect.candidateOption refs.pair.second middle =
      secondOption refs store := by
    unfold QuadraticCandidateSelect.candidateOption secondOption checkedCandidateOption
    rw [secondValue, modulus₂, refs.secondModulus]
  refine ⟨?_, into_callerFrame refs store⟩
  change QuadraticCandidateSelect.selectedOption refs.pair.first.selection
    (QuadraticCandidatePairSelect.step refs.pair middle).1 = _
  simpa only [previous, firstOptionValue, secondOptionValue] using pair.selected

/-- Independent allowance for candidate construction and both ordered proper-divisor checks. -/
def eventEnvelope (shortWidth : Nat) : ResourcePool kind :=
  QuadraticCandidates.eventEnvelope shortWidth +
    QuadraticCandidatePairSelect.eventEnvelope shortWidth

/-- The same actual path emits candidate instructions followed by both checked selections. -/
theorem into_events (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path =
      (QuadraticCandidates.into refs.candidates).eventTrace path.1 ++
        (QuadraticCandidatePairSelect.into refs.pair).eventTrace path.2 := rfl

/-- Every native coordinate is bounded by the independent sum of the two component allowances. -/
theorem into_pool_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope shortWidth := by
  change ResourcePool.ofList ((QuadraticCandidates.into refs.candidates).eventTrace path.1 ++
    (QuadraticCandidatePairSelect.into refs.pair).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (QuadraticCandidates.into_pool_le refs.candidates path.1)
    (QuadraticCandidatePairSelect.into_pool_le refs.pair path.2)

/-- Original sequential dependencies include both complete checked selections. -/
theorem into_depth_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path ≤
      7 * QuadraticPrefix.discriminantWidth shortWidth + 34 := by
  change (QuadraticCandidates.into refs.candidates).depth (fun _ => 1) path.1 +
    (QuadraticCandidatePairSelect.into refs.pair).depth (fun _ => 1) path.2 ≤ _
  rw [QuadraticCandidates.into_depth]
  have bound := QuadraticCandidatePairSelect.into_depth_le refs.pair path.2
  omega

/-- Candidate construction and checked selection keep every supplied runtime entry live. -/
theorem into_visited (refs : Refs ctx shortWidth) (path : (into refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (QuadraticCandidates.into refs.candidates).visitedContexts path.1 ++
    (QuadraticCandidatePairSelect.into refs.pair).visitedContexts path.2 at present
  rcases List.mem_append.mp present with candidates | pair
  · exact QuadraticCandidates.into_visited refs.candidates path.1 visited candidates
  · exact QuadraticCandidatePairSelect.into_visited refs.pair path.2 visited pair

/-- Resident space includes the complete supplied caller and scratch context. -/
theorem into_resident_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Auxiliary space preserves all supplied workspace roles throughout the same execution. -/
theorem into_auxiliary_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Actual quadratic recovery restores borrowed storage jointly with arbitrary references. -/
theorem into_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact QuadraticCandidates.into_borrowedRestored refs.candidates Reference state
  · exact QuadraticCandidatePairSelect.into_borrowedRestored refs.pair Reference _

/-- The machine retains an earlier factor and otherwise adopts the public RSA
recovery value for the current short logarithm. -/
theorem relation_retains_recoverFactorFromShortLog {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shortWidth : Nat} (refs : Refs ctx shortWidth)
    (before after : Store ctx)
    (holds : Relation refs before after)
    (shortLog : Nat)
    (shortLogValue :
      (before.read refs.candidates.quadraticPrefix.shortLog).toNat = shortLog)
    (modulus : Nat)
    (modulusValue :
      (before.read refs.candidates.quadraticPrefix.modulus).toNat = modulus) :
    QuadraticCandidateSelect.selectedOption refs.pair.first.selection after =
      FirstAccepted.retainFirst
        (QuadraticCandidateSelect.selectedOption refs.pair.first.selection before)
        (RSA.recoverFactorFromShortLog modulus shortLog) := by
  have recovered := holds.selected
  have firstEq : firstOption refs before =
      checkedCandidateOption
        (shortLog + 1 - Nat.sqrt ((shortLog + 1) ^ 2 - modulus)) modulus := by
    unfold firstOption firstCandidateValue
    rw [shortLogValue, modulusValue]
  have secondEq : secondOption refs before =
      checkedCandidateOption
        (shortLog + 1 + Nat.sqrt ((shortLog + 1) ^ 2 - modulus)) modulus := by
    unfold secondOption secondCandidateValue
    rw [shortLogValue, modulusValue]
  let previous := QuadraticCandidateSelect.selectedOption refs.pair.first.selection before
  calc
    QuadraticCandidateSelect.selectedOption refs.pair.first.selection after =
        FirstAccepted.retainFirst
          (FirstAccepted.retainFirst previous
            (checkedCandidateOption
              (shortLog + 1 - Nat.sqrt ((shortLog + 1) ^ 2 - modulus)) modulus))
          (checkedCandidateOption
            (shortLog + 1 + Nat.sqrt ((shortLog + 1) ^ 2 - modulus)) modulus) := by
      simpa only [previous, firstEq, secondEq] using recovered
    _ = FirstAccepted.retainFirst previous
        (recoveryValue modulus shortLog) := by
      unfold recoveryValue FirstAccepted.retainFirst
      cases previous <;> rfl
    _ = FirstAccepted.retainFirst previous
        (RSA.recoverFactorFromShortLog modulus shortLog) := by
      rw [recoveryValue_eq_recoverFactorFromShortLog]

/-- An initially empty latch returns exactly the public RSA recovery value. -/
theorem relation_recoversFactorFromShortLog {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shortWidth : Nat} (refs : Refs ctx shortWidth)
    (before after : Store ctx)
    (holds : Relation refs before after)
    (empty : QuadraticCandidateSelect.selectedOption
      refs.pair.first.selection before = none)
    (shortLog : Nat)
    (shortLogValue :
      (before.read refs.candidates.quadraticPrefix.shortLog).toNat = shortLog)
    (modulus : Nat)
    (modulusValue :
      (before.read refs.candidates.quadraticPrefix.modulus).toNat = modulus) :
    QuadraticCandidateSelect.selectedOption refs.pair.first.selection after =
      RSA.recoverFactorFromShortLog modulus shortLog := by
  have retained := relation_retains_recoverFactorFromShortLog refs before after
    holds shortLog shortLogValue modulus modulusValue
  simpa only [empty, FirstAccepted.retainFirst] using retained

end

end QuadraticRecoveryMachine
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
