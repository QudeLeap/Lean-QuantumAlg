/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Candidate.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Candidate.Resources

/-!
# Actual ordered selection of two quadratic factor candidates

Both checks update the same persistent selector in source order. The first
execution preserves the second candidate and its constants, so the complete
actual store implements the original ordered first-success fold.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidatePairSelect

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Two checked candidates sharing one persistent selector. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  first : QuadraticCandidateSelect.Refs ctx shortWidth
  second : QuadraticCandidateSelect.Refs ctx shortWidth
  sharedSelection : second.selection = first.selection

/-- Original separation for both steps and preservation of the second inputs. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) : Prop where
  first : QuadraticCandidateSelect.Separation refs.first
  second : QuadraticCandidateSelect.Separation refs.second
  secondCandidateFrame : QuadraticCandidateSelect.CallerFrameAvoids refs.first
    refs.second.check.positiveCheck.candidate
  secondOneFrame : QuadraticCandidateSelect.CallerFrameAvoids refs.first refs.second.check.one
  secondModulusFrame : QuadraticCandidateSelect.CallerFrameAvoids refs.first
    refs.second.check.positiveCheck.modulus
  secondZeroFrame : QuadraticCandidateSelect.CallerFrameAvoids refs.first
    refs.second.check.positiveCheck.zero

/-- Entry values required by both original total candidate checks. -/
def InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (before : Store ctx) (refs : Refs ctx shortWidth) : Prop :=
  QuadraticCandidateCheck.TotalInitialConditions before refs.first.check ∧
    QuadraticCandidateCheck.TotalInitialConditions before refs.second.check

/-- Avoidance of all actual writes in both ordered selector steps. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  first : QuadraticCandidateSelect.CallerFrameAvoids refs.first other
  second : QuadraticCandidateSelect.CallerFrameAvoids refs.second other

/-- The actual final latch is the ordered first-success fold, with the full caller frame. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  selected : QuadraticCandidateSelect.selectedOption refs.first.selection after =
    FirstAccepted.retainFirst
      (FirstAccepted.retainFirst
        (QuadraticCandidateSelect.selectedOption refs.first.selection before)
        (QuadraticCandidateSelect.candidateOption refs.first before))
      (QuadraticCandidateSelect.candidateOption refs.second before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Execute both actual checks and selectors in their original order. -/
def into (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (QuadraticCandidateSelect.into refs.first) (QuadraticCandidateSelect.into refs.second)

/-- The actual returned store and both recorded selection paths. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  Circuit.sequenceStoreRecord (QuadraticCandidateSelect.into refs.first)
    (QuadraticCandidateSelect.into refs.second)
    (QuadraticCandidateSelect.step refs.first) (QuadraticCandidateSelect.step refs.second) store

/-- Both real executions preserve their entire quantum-reference blocks and history. -/
theorem into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord (QuadraticCandidateSelect.into refs.first)
    (QuadraticCandidateSelect.into refs.second)
    (QuadraticCandidateSelect.step refs.first) (QuadraticCandidateSelect.step refs.second)
    (QuadraticCandidateSelect.into_execute refs.first)
    (QuadraticCandidateSelect.into_execute refs.second) Reference state

/-- Every original caller read outside the two write footprints remains unchanged. -/
theorem into_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other :=
  (QuadraticCandidateSelect.into_callerFrame refs.second _ other avoids.second).trans
    (QuadraticCandidateSelect.into_callerFrame refs.first store other avoids.first)

/-- The same actual pair execution implements the original ordered option fold. -/
theorem into_correct (refs : Refs ctx shortWidth) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    Relation refs store (step refs store).1 := by
  let middle := (QuadraticCandidateSelect.step refs.first store).1
  have first := QuadraticCandidateSelect.into_correct refs.first separation.first store initial.1
  have candidate := QuadraticCandidateSelect.into_callerFrame refs.first store
    refs.second.check.positiveCheck.candidate separation.secondCandidateFrame
  have one := QuadraticCandidateSelect.into_callerFrame refs.first store
    refs.second.check.one separation.secondOneFrame
  have modulus := QuadraticCandidateSelect.into_callerFrame refs.first store
    refs.second.check.positiveCheck.modulus separation.secondModulusFrame
  have zero := QuadraticCandidateSelect.into_callerFrame refs.first store
    refs.second.check.positiveCheck.zero separation.secondZeroFrame
  have secondInitial : QuadraticCandidateCheck.TotalInitialConditions middle refs.second.check := by
    unfold QuadraticCandidateCheck.TotalInitialConditions
    rw [one, modulus, zero]
    exact initial.2
  have second := QuadraticCandidateSelect.into_correct refs.second separation.second
    middle secondInitial
  have secondOption : QuadraticCandidateSelect.candidateOption refs.second middle =
      QuadraticCandidateSelect.candidateOption refs.second store := by
    unfold QuadraticCandidateSelect.candidateOption
    rw [candidate, modulus]
  refine ⟨?_, into_callerFrame refs store⟩
  have selected := second.selected
  rw [refs.sharedSelection, secondOption, first.selected] at selected
  exact selected

/-- Independent native allowance for two complete checked selectors. -/
def eventEnvelope (shortWidth : Nat) : ResourcePool model :=
  QuadraticCandidateSelect.eventEnvelope shortWidth +
    QuadraticCandidateSelect.eventEnvelope shortWidth

/-- Both recorded paths contribute their actual native events in order. -/
theorem into_events (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path =
      (QuadraticCandidateSelect.into refs.first).eventTrace path.1 ++
        (QuadraticCandidateSelect.into refs.second).eventTrace path.2 := rfl

/-- The actual native coordinates meet the sum of the two independent allowances. -/
theorem into_pool_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope shortWidth := by
  change ResourcePool.ofList
    ((QuadraticCandidateSelect.into refs.first).eventTrace path.1 ++
      (QuadraticCandidateSelect.into refs.second).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (QuadraticCandidateSelect.into_pool_le refs.first path.1)
    (QuadraticCandidateSelect.into_pool_le refs.second path.2)

/-- All measurement-free classical dependencies lie within twenty native instruction steps. -/
theorem into_depth_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path ≤ 20 := by
  change (QuadraticCandidateSelect.into refs.first).depth (fun _ => 1) path.1 +
    (QuadraticCandidateSelect.into refs.second).depth (fun _ => 1) path.2 ≤ 20
  have first := QuadraticCandidateSelect.into_depth_le refs.first path.1
  have second := QuadraticCandidateSelect.into_depth_le refs.second path.2
  omega

/-- Both complete executions keep precisely the supplied runtime context live. -/
theorem into_visited (refs : Refs ctx shortWidth) (path : (into refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (QuadraticCandidateSelect.into refs.first).visitedContexts path.1 ++
    (QuadraticCandidateSelect.into refs.second).visitedContexts path.2 at present
  rcases List.mem_append.mp present with first | second
  · exact QuadraticCandidateSelect.into_visited refs.first path.1 visited first
  · exact QuadraticCandidateSelect.into_visited refs.second path.2 visited second

/-- Resident space includes every supplied caller and workspace cell. -/
theorem into_resident_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Auxiliary space retains the supplied roles throughout both actual paths. -/
theorem into_auxiliary_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Both actual selections restore borrowed storage jointly with any external reference. -/
theorem into_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact QuadraticCandidateSelect.into_borrowedRestored refs.first Reference state
  · exact QuadraticCandidateSelect.into_borrowedRestored refs.second Reference _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidatePairSelect
