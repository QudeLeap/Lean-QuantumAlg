/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual reusable quadratic-recovery scratch reset

Four charged self-XOR instructions clear the reusable square-root words before
optional recovery. They preserve all caller reads outside those destinations,
including persistent selectors and constants. The square-root driver initializes
its own work state; this reset imposes no numerical or scratch-entry premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticRecoveryReset

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The square-root input width in one quadratic recovery. -/
abbrev InputWidth (shortWidth : Nat) : Nat := QuadraticPrefix.discriminantWidth shortWidth

/-- Exact word width used by the square-root round state. -/
abbrev WorkWidth (shortWidth : Nat) : Nat := NatSqrt.workWidth (InputWidth shortWidth)

/-- A quadratic recovery whose square-root output is reusable workspace. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- Actual candidate and persistent factor-selection references. -/
  recovery : QuadraticRecoveryMachine.Refs ctx shortWidth
  sqrtOutputRole :
    recovery.candidates.quadraticPrefix.sqrt.output.toCStorageRef.role = .workspace

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- The natural-square-root cells reset before every quadratic recovery. -/
def sqrtRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) : NatSqrt.Refs ctx (InputWidth shortWidth) :=
  refs.recovery.candidates.quadraticPrefix.sqrt

/-- Cross-clear separation of the four reusable words. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) : Prop where
  wideAvoidsRoot : (sqrtRefs refs).round.root.key ∉
    (QuadraticPrefix.writeInput (sqrtRefs refs).wideInput).storageKeys
  wideAvoidsHalf : (sqrtRefs refs).round.half.key ∉
    (QuadraticPrefix.writeInput (sqrtRefs refs).wideInput).storageKeys
  wideAvoidsOutput : (sqrtRefs refs).output.key ∉
    (QuadraticPrefix.writeInput (sqrtRefs refs).wideInput).storageKeys
  rootAvoidsHalf : (sqrtRefs refs).round.half.key ∉
    (QuadraticPrefix.writeInput (sqrtRefs refs).round.root).storageKeys
  rootAvoidsOutput : (sqrtRefs refs).output.key ∉
    (QuadraticPrefix.writeInput (sqrtRefs refs).round.root).storageKeys
  halfAvoidsOutput : (sqrtRefs refs).output.key ∉
    (QuadraticPrefix.writeInput (sqrtRefs refs).round.half).storageKeys

/-- One caller read avoids all four actual reset destinations. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  wideInput : (sqrtRefs refs).wideInput.key ∉ other.storageKeys
  root : (sqrtRefs refs).round.root.key ∉ other.storageKeys
  half : (sqrtRefs refs).round.half.key ∉ other.storageKeys
  output : (sqrtRefs refs).output.key ∉ other.storageKeys

/-- A paid self-XOR overwrites the actual input word with its zero value. -/
def clearOp {width : Nat} (output : CWriteRef ctx (.unsignedWord width)) :=
  ClassicalOp.wordBinary .bitXor width ctx
    (.product (QuadraticPrefix.writeInput output) (QuadraticPrefix.writeInput output)) output

/-- Four native self-XOR writes run in the original wide/root/half/output order. -/
def into (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).wideInput))
    (.seq (BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).round.root))
      (.seq (BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).round.half))
        (BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).output))))

/-- Complete actual store and chronological native path of the scratch reset. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  let wide := BitWord.instructionStep (execution := model)
    (clearOp (sqrtRefs refs).wideInput) store
  let root := BitWord.instructionStep (execution := model)
    (clearOp (sqrtRefs refs).round.root) wide.1
  let half := BitWord.instructionStep (execution := model)
    (clearOp (sqrtRefs refs).round.half) root.1
  let output := BitWord.instructionStep (execution := model)
    (clearOp (sqrtRefs refs).output) half.1
  (output.1, (wide.2, (root.2, (half.2, output.2))))

/-- Reset executes its entire store and native path on every history and external reference. -/
lemma into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every structural caller read avoiding the four real writes retains its whole value. -/
lemma into_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other := by
  dsimp only [step, BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).output)
      other avoids.output,
    Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).round.half)
      other avoids.half,
    Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).round.root)
      other avoids.root,
    Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).wideInput)
      other avoids.wideInput]

/-- Full zero values of the four destinations and complete unconditional caller frame. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  wideZero : after.read (QuadraticPrefix.writeInput (sqrtRefs refs).wideInput) =
    CShape.initialValue (.unsignedWord (WorkWidth shortWidth + WorkWidth shortWidth))
  rootZero : after.read (QuadraticPrefix.writeInput (sqrtRefs refs).round.root) =
    CShape.initialValue (.unsignedWord (WorkWidth shortWidth))
  halfZero : after.read (QuadraticPrefix.writeInput (sqrtRefs refs).round.half) =
    CShape.initialValue (.unsignedWord (WorkWidth shortWidth))
  outputZero : after.read (QuadraticPrefix.writeInput (sqrtRefs refs).output) =
    CShape.initialValue (.unsignedWord (WorkWidth shortWidth))
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

omit [BitWord.Selected model] in
private lemma clear_value {width : Nat} (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (store.applyOp (clearOp output)).read (QuadraticPrefix.writeInput output) =
      CShape.initialValue (.unsignedWord width) := by
  change (store.applyOp (clearOp output)).read
    (.storage (clearOp output).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change CShape.wordBitXor width (store.read (QuadraticPrefix.writeInput output))
    (store.read (QuadraticPrefix.writeInput output)) = _
  simp [CShape.wordBitXor, CShape.initialValue]

/-- Four actual clears establish zero work cells from arbitrary incoming values. -/
lemma into_correct (refs : Refs ctx shortWidth) (separation : Separation refs)
    (store : Store ctx) : Relation refs store (step refs store).1 := by
  refine ⟨?_, ?_, ?_, ?_, into_callerFrame refs store⟩
  · dsimp only [step, BitWord.instructionStep]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).output)
        _ separation.wideAvoidsOutput,
      Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).round.half)
        _ separation.wideAvoidsHalf,
      Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).round.root)
        _ separation.wideAvoidsRoot]
    exact clear_value (sqrtRefs refs).wideInput store
  · dsimp only [step, BitWord.instructionStep]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).output)
        _ separation.rootAvoidsOutput,
      Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).round.half)
        _ separation.rootAvoidsHalf]
    exact clear_value (sqrtRefs refs).round.root _
  · dsimp only [step, BitWord.instructionStep]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (clearOp (sqrtRefs refs).output)
      _ separation.halfAvoidsOutput]
    exact clear_value (sqrtRefs refs).round.half _
  · exact clear_value (sqrtRefs refs).output _

/-- Independent chronological native formula of the four paid clears. -/
def nativeTrace (shortWidth : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (WorkWidth shortWidth + WorkWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (WorkWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (WorkWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (WorkWidth shortWidth)))]

/-- Original independent four-clear native coordinate allowance. -/
def resetEventEnvelope (shortWidth : Nat) : ResourcePool model :=
  ResourcePool.ofList (nativeTrace shortWidth)

/-- Every reset path contains precisely the original four native self-XOR instructions. -/
lemma into_events (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path = nativeTrace shortWidth := by
  change (BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).wideInput)).eventTrace
      path.1 ++
    ((BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).round.root)).eventTrace
      path.2.1 ++
      ((BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).round.half)).eventTrace
        path.2.2.1 ++
        (BitWord.instruction (execution := model) (clearOp (sqrtRefs refs).output)).eventTrace
          path.2.2.2)) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The actual reset native multiplicities equal their independent four-clear formula. -/
lemma into_resourcePool (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path = resetEventEnvelope shortWidth := by
  change ResourcePool.ofList ((into refs).eventTrace path) = _
  rw [into_events]
  rfl

/-- Every actual reset path satisfies the original independent native coordinate allowance. -/
lemma into_pool_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ resetEventEnvelope shortWidth :=
  le_of_eq (into_resourcePool refs path)

/-- Exactly four paid instructions run even when the later recovery branch will be skipped. -/
lemma into_eventCount (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    ((into refs).eventTrace path).length = 4 := rfl

/-- Unit-duration dependency depth counts all four ordered native clears. -/
lemma into_depth (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path = 4 := rfl

/-- Each of the four reset instructions retains the original complete context. -/
lemma into_visited (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).visitedContexts path = List.replicate 4 ctx := rfl

/-- Every original caller resource remains resident throughout reset. -/
lemma into_resident_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary accounting retains all existing workspace and borrowed roles. -/
lemma into_auxiliary_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- All four writes restore the full borrowed-reference joint state on every input. -/
lemma into_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).BorrowedRestored
      Reference state ((into refs).execute environment Reference state) := by
  refine Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model)
        (clearOp (sqrtRefs refs).wideInput)) _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment) _ _ _
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model)
        (clearOp (sqrtRefs refs).round.root)) _) ?_
  exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model)
        (clearOp (sqrtRefs refs).round.half)) _)
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model)
        (clearOp (sqrtRefs refs).output)) _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticRecoveryReset
