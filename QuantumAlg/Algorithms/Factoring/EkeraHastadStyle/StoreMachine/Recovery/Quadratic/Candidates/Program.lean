/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Program
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual construction of the two original natural factor candidates
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates

open Execution
open ClassicalRoutines.NumberTheory
open QuadraticPrefix (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Resize the actual computed center into the original extra-bit candidate cell. -/
def centerOp (refs : Refs ctx shortWidth) :=
  ClassicalOp.wordResize (QuadraticPrefix.centerWidth shortWidth) (candidateWidth shortWidth) ctx
    (writeInput refs.quadraticPrefix.center) refs.centerWide

/-- Resize the actual computed square root into the original candidate cell. -/
def rootOp (refs : Refs ctx shortWidth) :=
  ClassicalOp.wordResize (QuadraticPrefix.discriminantWidth shortWidth)
    (candidateWidth shortWidth) ctx (writeInput refs.quadraticPrefix.sqrt.output) refs.rootWide

/-- Add the original widened center and root, retaining the real carry flag. -/
def secondOp (refs : Refs ctx shortWidth) :=
  ClassicalOp.addCarry (candidateWidth shortWidth) ctx
    (.product (writeInput refs.centerWide) (writeInput refs.rootWide)) refs.second

/-- Actual center resize, root resize, truncated first subtraction and second addition. -/
def suffixInto (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (centerOp refs))
    (.seq (BitWord.instruction (execution := model) (rootOp refs))
      (.seq (NatSub.into refs.first)
        (BitWord.instruction (execution := model) (secondOp refs))))

/-- The suffix record follows the true intermediate stores and natural-subtraction branch. -/
def suffixStep (refs : Refs ctx shortWidth) (store : Store ctx) :
    Store ctx × (suffixInto refs).Path :=
  let center := BitWord.instructionStep (execution := model) (centerOp refs) store
  let root := BitWord.instructionStep (execution := model) (rootOp refs) center.1
  let firstResult := NatSub.step refs.first root.1
  let second := BitWord.instructionStep (execution := model) (secondOp refs) firstResult.1
  (second.1, (center.2, (root.2, (firstResult.2, second.2))))

/-- The actual suffix preserves incoming history and every external quantum-reference block. -/
lemma suffixInto_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (suffixInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := suffixStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [suffixInto, suffixStep, Circuit.execute_seq, NatSub.into_execute,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual quadratic prefix followed by the original two-candidate construction. -/
def into (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (QuadraticPrefix.into refs.quadraticPrefix) (suffixInto refs)

/-- One actual record includes the discriminant branch, all root rounds and both candidates. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  Circuit.sequenceStoreRecord (QuadraticPrefix.into refs.quadraticPrefix) (suffixInto refs)
    (QuadraticPrefix.step refs.quadraticPrefix) (suffixStep refs) store

/-- Complete actual execution preserves original history and arbitrary quantum correlations. -/
lemma into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord
    (environment := environment) (QuadraticPrefix.into refs.quadraticPrefix) (suffixInto refs)
    (QuadraticPrefix.step refs.quadraticPrefix) (suffixStep refs)
    (QuadraticPrefix.into_execute refs.quadraticPrefix) (suffixInto_execute refs) Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates
