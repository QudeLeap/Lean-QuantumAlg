/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

/-!
# Complete records of the original GF(2) decisions

Each actual equality latch and original failure marker follows the preceding
real store. Both lexical cells are really initialized and popped, preserving
all original Store, Reference and History correlations without a zero promise.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {environment : model.Environment}
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (BitWord.instruction (execution := model) op).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := BitWord.instructionStep (execution := model) op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_instruction_execute (environment := environment) (execution := model) op state

omit [BitWord.Selected model] in
private lemma idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.id (allowAllocation := true) (model := model) ctx).execute environment Reference state
      =
      state.mapClassical (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  exact (Circuit.execute_id_mapClassical (environment := environment) (allowAllocation := true)
    (model := model) Reference state).trans
    (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The original copy marker and stable self-XOR use the same actual success cell. -/
def markFailureStep (success : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (markFailure success).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (pivotRejectedOp success))
    (BitWord.instruction (execution := model) (pivotClearOp success))
    (BitWord.instructionStep (execution := model) (pivotRejectedOp success))
    (BitWord.instructionStep (execution := model) (pivotClearOp success)) store

/-- Both original failure events preserve the full quantum-reference and history state. -/
lemma gf2MarkFailure_execute (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (markFailure (model := model) success).execute environment Reference state =
      state.mapClassical (fun entry =>
      ((markFailureStep success entry.1).1,
        (entry.2.1, (entry.2.2, (markFailureStep success entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model)
    (BitWord.instruction (execution := model) (pivotRejectedOp success))
    (BitWord.instruction (execution := model) (pivotClearOp success))
    (BitWord.instructionStep (execution := model) (pivotRejectedOp success))
    (BitWord.instructionStep (execution := model) (pivotClearOp success))
    (operation_execute (pivotRejectedOp success))
    (operation_execute (pivotClearOp success)) Reference state

/-- The original stored equality outcome selects its actual failure record or identity. -/
def decisionChoiceStep (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (decisionChoice reject success value).Path :=
  match value with
  | .bit value =>
      match reject, value with
      | false, false => markFailureStep success store
      | false, true => (store, ())
      | true, false => (store, ())
      | true, true => markFailureStep success store

private lemma decisionChoice_execute (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decisionChoice (model := model) reject success value).execute environment Reference state =
      state.mapClassical (fun entry =>
      ((decisionChoiceStep reject success value entry.1).1,
        (entry.2.1, (entry.2.2, (decisionChoiceStep reject success value entry.1).2)))) := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · refine (gf2MarkFailure_execute (model := model) success Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · refine (idle_execute (model := model) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · refine (idle_execute (model := model) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · refine (gf2MarkFailure_execute (model := model) success Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- A real equality write precedes the branch reading its actual updated latch. -/
def decisionTestStep (reject : Bool) (left right : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (decisionTest reject left right success flag).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success))
    (BitWord.instructionStep (execution := model) (decisionEqualityOp left right flag))
    (fun current =>
      let value := current.read (.storage flag.toCStorageRef)
      let actual := decisionChoiceStep reject success value current
      (actual.1, ⟨value, actual.2⟩)) store

/-- The actual written equality bit controls the complete state transformation. -/
lemma gf2DecisionTest_execute (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decisionTest (model := model) reject left right success flag).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((decisionTestStep reject left right success flag entry.1).1,
          (entry.2.1, (entry.2.2,
            (decisionTestStep reject left right success flag entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model)
    (BitWord.instruction (execution := model) (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success))
    (BitWord.instructionStep (execution := model) (decisionEqualityOp left right flag))
    (fun current =>
      let value := current.read (.storage flag.toCStorageRef)
      let actual := decisionChoiceStep reject success value current
      (actual.1, ⟨value, actual.2⟩))
    (operation_execute (decisionEqualityOp left right flag))
    (fun reference {_} _ current => Circuit.execute_branchStoreRecord
      (environment := environment) (model := model)
      (.storage flag.toCStorageRef) (decisionChoice (model := model) reject success)
      (decisionChoiceStep reject success)
      (decisionChoice_execute (model := model) reject success) reference current)
    Reference state

/-- The two original equalities consume the actual decrement and mask outputs in order. -/
def uniqueFreeBodyStep (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (uniqueFreeBody free zero work success flag).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (decisionDecrementOp free work))
    (.seq (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag)))
    (BitWord.instructionStep (execution := model) (decisionDecrementOp free work))
    (Circuit.sequenceStoreRecord
      (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag))
      (BitWord.instructionStep (execution := model) (decisionMaskOp free work))
      (Circuit.sequenceStoreRecord
        (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag)
        (decisionTestStep false work zero success flag)
        (decisionTestStep true free zero success flag))) store

/-- All original uniqueness stages preserve the complete arbitrary input state. -/
lemma gf2UniqueFreeBody_execute (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (uniqueFreeBody (model := model) free zero work success flag).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((uniqueFreeBodyStep free zero work success flag entry.1).1,
          (entry.2.1, (entry.2.2,
            (uniqueFreeBodyStep free zero work success flag entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (operation_execute (decisionDecrementOp free work))
    (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
      (operation_execute (decisionMaskOp free work))
      (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
        (gf2DecisionTest_execute (model := model) false work zero success flag)
        (gf2DecisionTest_execute (model := model) true free zero success flag))) Reference state

/-- The original free decision closes its actual flag before its word scope. -/
def scopedUniqueFreeStep (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store (pivotMaskContext ctx width)) :
    Store (pivotMaskContext ctx width) × (scopedUniqueFree free zero success).Path :=
  let actual := uniqueFreeBodyStep (decisionWrite width free) (decisionWrite width zero)
    (decisionWork ctx width) (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width))
    (store.pushWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
      (pivotMaskContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
    (pivotMaskContext ctx width).canonicalFreshKey_fresh actual.1, actual.2)

private lemma scopedUniqueFree_execute (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (pivotMaskContext ctx width) Reference (model.HiddenState × History)) :
    (scopedUniqueFree (model := model) free zero success).execute environment Reference state =
      state.mapClassical (fun entry =>
      ((scopedUniqueFreeStep free zero success entry.1).1,
        (entry.2.1, (entry.2.2, (scopedUniqueFreeStep free zero success entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (gf2UniqueFreeBody_execute (model := model) _ _ _ _ _) Reference state

/-- The actual outer word is allocated and popped even when the check never reads it. -/
def selectUniqueFreeStep (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (selectUniqueFree free zero success).Path :=
  let actual := scopedUniqueFreeStep free zero success
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The complete original check preserves arbitrary Store, Reference and History correlations. -/
lemma gf2UniqueFree_execute (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectUniqueFree (model := model) free zero success).execute environment Reference state =
      state.mapClassical (fun entry =>
      ((selectUniqueFreeStep free zero success entry.1).1,
        (entry.2.1, (entry.2.2, (selectUniqueFreeStep free zero success entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (scopedUniqueFree_execute (model := model) free zero success) Reference state

/-- The original candidate decision closes its actual flag before its word scope. -/
def scopedCandidateNonzeroStep (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store (pivotMaskContext ctx width)) :
    Store (pivotMaskContext ctx width) × (scopedCandidateNonzero candidate zero success).Path :=
  let actual := decisionTestStep true (decisionWrite width candidate) (decisionWrite width zero)
    (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width))
    (store.pushWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
      (pivotMaskContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
    (pivotMaskContext ctx width).canonicalFreshKey_fresh actual.1, actual.2)

private lemma scopedCandidateNonzero_execute
    (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (pivotMaskContext ctx width) Reference (model.HiddenState × History)) :
    (scopedCandidateNonzero (model := model) candidate zero success).execute environment
      Reference state =
      state.mapClassical (fun entry =>
      ((scopedCandidateNonzeroStep candidate zero success entry.1).1,
        (entry.2.1,
          (entry.2.2, (scopedCandidateNonzeroStep candidate zero success entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (gf2DecisionTest_execute (model := model) true _ _ _ _) Reference state

/-- The actual outer word is allocated and popped even when the check never reads it. -/
def checkCandidateNonzeroStep (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (checkCandidateNonzero candidate zero success).Path :=
  let actual := scopedCandidateNonzeroStep candidate zero success
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The complete original check preserves arbitrary Store, Reference and History correlations. -/
lemma gf2CandidateNonzero_execute (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (checkCandidateNonzero (model := model) candidate zero success).execute environment
      Reference state =
      state.mapClassical (fun entry =>
      ((checkCandidateNonzeroStep candidate zero success entry.1).1,
        (entry.2.1,
          (entry.2.2, (checkCandidateNonzeroStep candidate zero success entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (scopedCandidateNonzero_execute (model := model) candidate zero success) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
