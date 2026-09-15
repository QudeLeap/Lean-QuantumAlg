/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Selection.Layout

/-!
# Actual three-check eligibility and first-success candidate selection
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual first conjunction combines the original distance and exponent checks. -/
def intermediateOp (refs : Refs ctx width) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product refs.nearTarget refs.exponentInRange) refs.intermediate

/-- Actual second conjunction includes the stored original modular-power check. -/
def eligibleOp (refs : Refs ctx width) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (writeInput refs.intermediate) refs.powerMatches) refs.eligible

/-- Both original conjunctions execute before persistent first-success selection. -/
def candidateEligibilityInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (intermediateOp refs)) (.classical (eligibleOp refs))

/-- The actual two chronological eligibility writes and their native paths. -/
def eligibilityStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidateEligibilityInto refs).Path :=
  ((store.applyOp (intermediateOp refs)).applyOp (eligibleOp refs), ((), ()))

/-- The direct actual selector reads the stored eligibility and existing persistent accepted
latch. -/
def selectionInto (refs : Refs ctx width) : Circuit ctx ctx :=
  ClassicalRoutines.FirstAccepted.Direct.into
    (writeInput refs.eligible) refs.candidate refs.selection

/-- The actual first-success store and paths for the already materialized candidate predicate. -/
def selectionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (selectionInto refs).Path :=
  ClassicalRoutines.FirstAccepted.Direct.step
    (writeInput refs.eligible) refs.candidate refs.selection
    store

/-- Original three-check candidate selection, with no additional available/take cells. -/
def candidateSelectorInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (candidateEligibilityInto refs) (selectionInto refs)

/-- Complete actual eligibility and persistent-selection store, with both component paths. -/
def selectorStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidateSelectorInto refs).Path :=
  let eligible := eligibilityStep refs store
  let selected := selectionStep refs eligible.1
  (selected.1, (eligible.2, selected.2))

/-- Both actual Boolean operations retain the complete incoming quantum-reference blocks. -/
theorem candidateEligibilityInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateEligibilityInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((eligibilityStep refs entry.1).1, (entry.2, (eligibilityStep refs entry.1).2))) := by
  simp only [candidateEligibilityInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual closing suffix follows its stored three-way predicate and persistent accepted
latch. -/
theorem candidateSelectorInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateSelectorInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((selectorStep refs entry.1).1, (entry.2, (selectorStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (candidateEligibilityInto refs) (selectionInto refs)
    (eligibilityStep refs) (selectionStep refs) (candidateEligibilityInto_execute refs)
    (ClassicalRoutines.FirstAccepted.Direct.into_execute
      (writeInput refs.eligible) refs.candidate refs.selection) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector
