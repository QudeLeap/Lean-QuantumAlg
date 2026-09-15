/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision
import all QuantumAlg.Core.Execution.Classical.Composition.Record

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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.classical op).execute Reference state =
      state.mapClassical (D := Store ctx × (History × (Circuit.classical op).Path))
        (fun entry => (entry.1.applyOp op, (entry.2, ()))) := by
  refine (Circuit.execute_classical_mapClassical op Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.id ctx).execute Reference state =
      state.mapClassical (D := Store ctx × (History × (Circuit.id ctx).Path))
        (fun entry => (entry.1, (entry.2, ()))) := by
  refine (Circuit.execute_id_mapClassical Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The original copy marker and stable self-XOR use the same actual success cell. -/
def markFailureStep (success : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (markFailure success).Path :=
  Circuit.sequenceRecord (.classical (pivotRejectedOp success))
    (.classical (pivotClearOp success))
    (fun current => (current.applyOp (pivotRejectedOp success), ()))
    (fun current => (current.applyOp (pivotClearOp success), ())) store

/-- Both original failure events preserve the full quantum-reference and history state. -/
theorem gf2MarkFailure_execute (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (markFailure success).execute Reference state =
      state.mapClassical (fun entry =>
      ((markFailureStep success entry.1).1, (entry.2, (markFailureStep success entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (pivotRejectedOp success))
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

private theorem decisionChoice_execute (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (decisionChoice reject success value).execute Reference state =
      state.mapClassical (fun entry =>
      ((decisionChoiceStep reject success value entry.1).1,
        (entry.2, (decisionChoiceStep reject success value entry.1).2))) := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · exact gf2MarkFailure_execute success Reference state
      · exact idle_execute Reference state
      · exact idle_execute Reference state
      · exact gf2MarkFailure_execute success Reference state

/-- A real equality write precedes the branch reading its actual updated latch. -/
def decisionTestStep (reject : Bool) (left right : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (decisionTest reject left right success flag).Path :=
  Circuit.sequenceRecord (.classical (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef) (decisionChoice reject success))
    (fun current => (current.applyOp (decisionEqualityOp left right flag), ()))
    (fun current =>
      let value := current.read (.storage flag.toCStorageRef)
      let actual := decisionChoiceStep reject success value current
      (actual.1, ⟨value, actual.2⟩)) store

/-- The actual written equality bit controls the complete state transformation. -/
theorem gf2DecisionTest_execute (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (decisionTest reject left right success flag).execute Reference state =
      state.mapClassical (fun entry =>
        ((decisionTestStep reject left right success flag entry.1).1,
          (entry.2, (decisionTestStep reject left right success flag entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (decisionEqualityOp left right flag))
    (fun reference {_} _ current => Circuit.execute_branch_mapClassical
      (.storage flag.toCStorageRef) (decisionChoice reject success)
      (decisionChoiceStep reject success) (decisionChoice_execute reject success) reference current)
    Reference state

/-- The two original equalities consume the actual decrement and mask outputs in order. -/
def uniqueFreeBodyStep (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (uniqueFreeBody free zero work success flag).Path :=
  Circuit.sequenceRecord (.classical (decisionDecrementOp free work))
    (.seq (.classical (decisionMaskOp free work))
      (.seq (decisionTest false work zero success flag)
        (decisionTest true free zero success flag)))
    (fun current => (current.applyOp (decisionDecrementOp free work), ()))
    (Circuit.sequenceRecord (.classical (decisionMaskOp free work))
      (.seq (decisionTest false work zero success flag)
        (decisionTest true free zero success flag))
      (fun current => (current.applyOp (decisionMaskOp free work), ()))
      (Circuit.sequenceRecord (decisionTest false work zero success flag)
        (decisionTest true free zero success flag)
        (decisionTestStep false work zero success flag)
        (decisionTestStep true free zero success flag))) store

/-- All original uniqueness stages preserve the complete arbitrary input state. -/
theorem gf2UniqueFreeBody_execute (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (uniqueFreeBody free zero work success flag).execute Reference state =
      state.mapClassical (fun entry =>
        ((uniqueFreeBodyStep free zero work success flag entry.1).1,
          (entry.2, (uniqueFreeBodyStep free zero work success flag entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (decisionDecrementOp free work))
    (Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (decisionMaskOp free work))
      (Circuit.execute_sequenceRecord _ _ _ _
        (gf2DecisionTest_execute false work zero success flag)
        (gf2DecisionTest_execute true free zero success flag))) Reference state

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

private theorem scopedUniqueFree_execute (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (pivotMaskContext ctx width) Reference History) :
    (scopedUniqueFree free zero success).execute Reference state =
      state.mapClassical (fun entry =>
      ((scopedUniqueFreeStep free zero success entry.1).1,
        (entry.2, (scopedUniqueFreeStep free zero success entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (gf2UniqueFreeBody_execute _ _ _ _ _) Reference state

/-- The actual outer word is allocated and popped even when the check never reads it. -/
def selectUniqueFreeStep (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (selectUniqueFree free zero success).Path :=
  let actual := scopedUniqueFreeStep free zero success
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The complete original check preserves arbitrary Store, Reference and History correlations. -/
theorem gf2UniqueFree_execute (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (selectUniqueFree free zero success).execute Reference state =
      state.mapClassical (fun entry =>
      ((selectUniqueFreeStep free zero success entry.1).1,
        (entry.2, (selectUniqueFreeStep free zero success entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (scopedUniqueFree_execute free zero success) Reference state

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

private theorem scopedCandidateNonzero_execute
    (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (pivotMaskContext ctx width) Reference History) :
    (scopedCandidateNonzero candidate zero success).execute Reference state =
      state.mapClassical (fun entry =>
      ((scopedCandidateNonzeroStep candidate zero success entry.1).1,
        (entry.2, (scopedCandidateNonzeroStep candidate zero success entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (gf2DecisionTest_execute true _ _ _ _) Reference state

/-- The actual outer word is allocated and popped even when the check never reads it. -/
def checkCandidateNonzeroStep (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (checkCandidateNonzero candidate zero success).Path :=
  let actual := scopedCandidateNonzeroStep candidate zero success
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The complete original check preserves arbitrary Store, Reference and History correlations. -/
theorem gf2CandidateNonzero_execute (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (checkCandidateNonzero candidate zero success).execute Reference state =
      state.mapClassical (fun entry =>
      ((checkCandidateNonzeroStep candidate zero success entry.1).1,
        (entry.2, (checkCandidateNonzeroStep candidate zero success entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (scopedCandidateNonzero_execute candidate zero success) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
