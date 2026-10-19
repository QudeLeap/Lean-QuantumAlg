/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Layout
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Program
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual quadratic center and discriminant computation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- The original short logarithm is widened by one bit into its supplied center cell. -/
def resizeOp (refs : Refs ctx shortWidth) :
    ClassicalOp (.unsignedWord shortWidth) (.unsignedWord (centerWidth shortWidth)) ctx ctx :=
  .wordResize shortWidth (centerWidth shortWidth) ctx refs.shortLog refs.center

/-- The widened original short logarithm is incremented by one native operation. -/
def incrementOp (refs : Refs ctx shortWidth) :
    ClassicalOp (.unsignedWord (centerWidth shortWidth))
      (.unsignedWord (centerWidth shortWidth)) ctx ctx :=
  .wordUnary .increment (centerWidth shortWidth) ctx (writeInput refs.center) refs.center

/-- Both original center factors feed the full-width multiplication. -/
def squareOp (refs : Refs ctx shortWidth) :
    ClassicalOp (.product (.unsignedWord (centerWidth shortWidth))
      (.unsignedWord (centerWidth shortWidth)))
      (.unsignedWord (discriminantWidth shortWidth)) ctx ctx :=
  .mulFull (centerWidth shortWidth) (centerWidth shortWidth) ctx
    (.product (writeInput refs.center) (writeInput refs.center)) refs.centerSquare

/-- The actual three-operation center and square preparation. -/
def prepareInto (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (resizeOp refs))
    (.seq (BitWord.instruction (execution := model) (incrementOp refs))
      (BitWord.instruction (execution := model) (squareOp refs)))

/-- Actual chronological preparation store and all three native paths. -/
def prepareStep (refs : Refs ctx shortWidth) (store : Store ctx) :
    Store ctx × (prepareInto refs).Path :=
  let resized := BitWord.instructionStep (execution := model) (resizeOp refs) store
  let incremented := BitWord.instructionStep (execution := model) (incrementOp refs) resized.1
  let squared := BitWord.instructionStep (execution := model) (squareOp refs) incremented.1
  (squared.1, (resized.2, (incremented.2, squared.2)))

/-- The three original preparation writes preserve every history and quantum-reference block. -/
lemma prepareInto_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (prepareInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := prepareStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [prepareInto, prepareStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual square feeds natural truncated subtraction of the original modulus. -/
def discriminantInto (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (prepareInto refs) (NatSub.into refs.subtract)

/-- The actual discriminant store records the real underflow branch taken by subtraction. -/
def discriminantStep (refs : Refs ctx shortWidth) (store : Store ctx) :
    Store ctx × (discriminantInto refs).Path :=
  Circuit.sequenceStoreRecord (prepareInto refs) (NatSub.into refs.subtract)
    (prepareStep refs) (NatSub.step refs.subtract) store

/-- Original preparation and natural subtraction compose on their actual intermediate store. -/
lemma discriminantInto_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (discriminantInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := discriminantStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord
    (environment := environment) (prepareInto refs) (NatSub.into refs.subtract)
    (prepareStep refs) (NatSub.step refs.subtract)
    (prepareInto_execute refs) (NatSub.into_execute refs.subtract) Reference state

/-- The actual truncated discriminant feeds the original finite square-root driver. -/
def into (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (discriminantInto refs) (NatSqrt.into refs.sqrt)

/-- One chronological record includes every prefix write and square-root refinement branch. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  Circuit.sequenceStoreRecord (discriminantInto refs) (NatSqrt.into refs.sqrt)
    (discriminantStep refs) (NatSqrt.step refs.sqrt) store

/-- Actual execution retains the incoming history and all external quantum-reference blocks. -/
lemma into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord
    (environment := environment) (discriminantInto refs) (NatSqrt.into refs.sqrt)
    (discriminantStep refs) (NatSqrt.step refs.sqrt)
    (discriminantInto_execute refs) (NatSqrt.into_execute refs.sqrt) Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix
