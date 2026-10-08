/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Layout
import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Program
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual native quadratic candidate checks and stored-decision branch
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Native candidate widening into the public modulus width. -/
def widenOp (refs : Refs ctx shortWidth) :=
  ClassicalOp.wordResize (CandidateWidth shortWidth) (ModulusWidth shortWidth) ctx
    refs.candidate refs.candidateWide

/-- Native strict comparison of the actual widened candidate with the modulus. -/
def belowOp (refs : Refs ctx shortWidth) :=
  ClassicalOp.wordBinary .lessThan (ModulusWidth shortWidth) ctx
    (.product (writeInput refs.candidateWide) refs.modulus) refs.belowModulus

/-- Native conjunction of the real range and remainder acceptance bits. -/
def combineOp (refs : Refs ctx shortWidth) :=
  ClassicalOp.bit .and ctx
    (.product (writeInput refs.belowModulus) (writeInput refs.modulusCheck.accepted)) refs.eligible

/-- The original five native operations of the positive-candidate suffix. -/
def positiveInto (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (widenOp refs))
    (.seq (BitWord.instruction (execution := model) (belowOp refs))
      (.seq (NatModCheck.into refs.modulusCheck)
        (BitWord.instruction (execution := model) (combineOp refs))))

/-- The actual store after candidate widening and range comparison. -/
def positiveSeed (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx :=
  (store.applyOp (widenOp refs)).applyOp (belowOp refs)

/-- Actual positive-suffix store and every chronological native path. -/
def positiveStep (refs : Refs ctx shortWidth) (store : Store ctx) :
    Store ctx × (positiveInto refs).Path :=
  let widened := BitWord.instructionStep (execution := model) (widenOp refs) store
  let below := BitWord.instructionStep (execution := model) (belowOp refs) widened.1
  let checked := NatModCheck.step refs.modulusCheck below.1
  let combined := BitWord.instructionStep (execution := model) (combineOp refs) checked.1
  (combined.1, (widened.2, (below.2, (checked.2, combined.2))))

/-- The positive suffix executes its complete record on every incoming reference block. -/
theorem positiveInto_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (positiveInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := positiveStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [positiveInto, positiveStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, NatModCheck.into_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Native strict lower-bound decision using the supplied one input. -/
def decisionOp (refs : TotalRefs ctx shortWidth) :=
  ClassicalOp.wordBinary .lessThan (CandidateWidth shortWidth) ctx
    (.product refs.one refs.positiveCheck.candidate) refs.greaterThanOne

/-- Charged self-XOR rejects by overwriting any incoming eligibility bit with false. -/
def rejectOp (refs : TotalRefs ctx shortWidth) :=
  ClassicalOp.bit .xor ctx
    (.product (writeInput refs.positiveCheck.eligible) (writeInput refs.positiveCheck.eligible))
    refs.positiveCheck.eligible

/-- Actual selected positive suffix or native rejection write. -/
def arm (refs : TotalRefs ctx shortWidth) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => BitWord.instruction (execution := model) (rejectOp refs)
  | .bit true => positiveInto refs.positiveCheck

/-- Actual selected-arm store and native path. -/
def armStep (refs : TotalRefs ctx shortWidth) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (arm refs flag).Path :=
  match flag with
  | .bit false => BitWord.instructionStep (execution := model) (rejectOp refs) store
  | .bit true => positiveStep refs.positiveCheck store

/-- Read the real decision cell to select the executed instruction body. -/
def chooseInto (refs : TotalRefs ctx shortWidth) : Circuit model ctx ctx :=
  .branch (writeInput refs.greaterThanOne) (arm refs)

/-- The selected-arm record includes the value read from the actual decision cell. -/
def chooseStep (refs : TotalRefs ctx shortWidth) (store : Store ctx) :
    Store ctx × (chooseInto refs).Path :=
  let flag := store.read (writeInput refs.greaterThanOne)
  let chosen := armStep refs flag store
  (chosen.1, ⟨flag, chosen.2⟩)

/-- Total actual decision followed by the stored-flag branch. -/
def into (refs : TotalRefs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (decisionOp refs)) (chooseInto refs)

/-- Full actual store and chronological total-check path, including its stored decision. -/
def step (refs : TotalRefs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  let decision := BitWord.instructionStep (execution := model) (decisionOp refs) store
  let chosen := chooseStep refs decision.1
  (chosen.1, (decision.2, chosen.2))

/-- The actual selected store follows the original true-positive, false-reject branch. -/
theorem chooseStep_store (refs : TotalRefs ctx shortWidth) (store : Store ctx) :
    (chooseStep refs store).1 =
      if (store.read (writeInput refs.greaterThanOne)).toBool then
        (positiveStep refs.positiveCheck store).1 else store.applyOp (rejectOp refs) := by
  unfold chooseStep
  cases value : store.read (writeInput refs.greaterThanOne) with
  | bit flag => cases flag <;> rfl

private theorem arm_execute (refs : TotalRefs ctx shortWidth) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (arm refs flag).execute Reference state = state.mapClassical (fun entry =>
      let actual := armStep refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
      cases flag with
      | false =>
          exact BitWord.bitWord_instruction_execute (rejectOp refs) state
      | true => exact positiveInto_execute refs.positiveCheck Reference state

/-- Actual stored-value dispatch preserves every incoming history and reference block. -/
theorem chooseInto_execute (refs : TotalRefs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (chooseInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := chooseStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  exact Circuit.execute_branchStoreRecord (writeInput refs.greaterThanOne) (arm refs)
    (armStep refs) (arm_execute refs) Reference state

/-- The total checker executes precisely its actual full-state record. -/
theorem into_execute (refs : TotalRefs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    chooseInto_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck
