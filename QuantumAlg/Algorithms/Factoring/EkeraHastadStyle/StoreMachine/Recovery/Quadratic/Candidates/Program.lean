/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Program

/-!
# Actual construction of the two original natural factor candidates
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates

open Execution
open ClassicalRoutines.NumberTheory
open QuadraticPrefix (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}

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
def suffixInto (refs : Refs ctx shortWidth) : Circuit ctx ctx :=
  .seq (.classical (centerOp refs)) (.seq (.classical (rootOp refs))
    (.seq (NatSub.into refs.first) (.classical (secondOp refs))))

/-- The suffix record follows the true intermediate stores and natural-subtraction branch. -/
def suffixStep (refs : Refs ctx shortWidth) (store : Store ctx) :
    Store ctx × (suffixInto refs).Path :=
  let afterCenter := store.applyOp (centerOp refs)
  let afterRoot := afterCenter.applyOp (rootOp refs)
  let firstResult := NatSub.step refs.first afterRoot
  (firstResult.1.applyOp (secondOp refs), ((), ((), (firstResult.2, ()))))

/-- The actual suffix preserves incoming history and every external quantum-reference block. -/
theorem suffixInto_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (suffixInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((suffixStep refs entry.1).1, (entry.2, (suffixStep refs entry.1).2))) := by
  simp only [suffixInto, suffixStep, Circuit.execute_seq, NatSub.into_execute,
    Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual quadratic prefix followed by the original two-candidate construction. -/
def into (refs : Refs ctx shortWidth) : Circuit ctx ctx :=
  .seq (QuadraticPrefix.into refs.quadraticPrefix) (suffixInto refs)

/-- One actual record includes the discriminant branch, all root rounds and both candidates. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  Circuit.sequenceRecord (QuadraticPrefix.into refs.quadraticPrefix) (suffixInto refs)
    (QuadraticPrefix.step refs.quadraticPrefix) (suffixStep refs) store

/-- Complete actual execution preserves original history and arbitrary quantum correlations. -/
theorem into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) :=
  Circuit.execute_sequenceRecord (QuadraticPrefix.into refs.quadraticPrefix) (suffixInto refs)
    (QuadraticPrefix.step refs.quadraticPrefix) (suffixStep refs)
    (QuadraticPrefix.into_execute refs.quadraticPrefix) (suffixInto_execute refs) Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates
