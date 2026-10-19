/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual lexical scratch for extended-Euclidean coefficient updates

The product and updated coefficient occupy two real fresh word cells. Their
identities follow from the context, and both cells are released after the
four native operations. The persistent coefficient cells remain live; their
values and all unrelated classical reads are observed in the parent context.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Allocate the product cell at the next actual fresh storage identity. -/
@[reducible] def coefficientProductCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Allocate the updated-coefficient cell after the product cell. -/
@[reducible] def coefficientScratchCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (coefficientProductCtx ctx width).addWorkspace
    (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (coefficientProductCtx ctx width).canonicalFreshKey_fresh

/-- Lift an existing read through exactly the two scratch scopes. -/
def coefficientUnderScratch {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (coefficientScratchCtx ctx width) shape :=
  (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh

/-- Lift a persistent coefficient cell through those same two scopes. -/
def coefficientWriteUnderScratch (cell : CWriteRef ctx (.unsignedWord width)) :
    CWriteRef (coefficientScratchCtx ctx width) (.unsignedWord width) :=
  (cell.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh

/-- Product scratch is the first allocated cell, beneath the later update cell. -/
def coefficientProductCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (coefficientScratchCtx ctx width) (.unsignedWord width) :=
  (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh

/-- Updated coefficient scratch is the actual head cell. -/
def coefficientUpdatedCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (coefficientScratchCtx ctx width) (.unsignedWord width) :=
  CWriteRef.workspaceHead (coefficientProductCtx ctx width)
    (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (coefficientProductCtx ctx width).canonicalFreshKey_fresh

variable {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Execute the four-operation recurrence inside two actual lexical allocations. -/
def scopedCoefficientUpdate (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (.workspace (coefficientProductCtx ctx width)
      (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (coefficientProductCtx ctx width).canonicalFreshKey_fresh
      (coefficientUpdateBody (model := model) (coefficientUnderScratch quotient width)
        (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
        (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width)))

/-- The concrete store transformation includes both matching allocation and release pairs. -/
def scopedCoefficientStep (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (scopedCoefficientUpdate (model := model) quotient first second).Path :=
  let entered := (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh
  let final := coefficientUpdateStep (model := model) (coefficientUnderScratch quotient width)
    (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
    (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width) entered
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh final.1),
    final.2)

/-- Both lexical scopes preserve every full quantum-reference block and the actual body path. -/
lemma xgcdScopedCoefficient_execute (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scopedCoefficientUpdate (model := model) quotient first second).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((scopedCoefficientStep (model := model) quotient first second entry.1).1,
          (entry.2.1, (entry.2.2, (scopedCoefficientStep
            (model := model) quotient first second entry.1).2)))) := by
  let body := coefficientUpdateBody (model := model) (coefficientUnderScratch quotient width)
    (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
    (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width)
  let update := fun before : Store (coefficientScratchCtx ctx width) × model.HiddenState =>
    let actual := coefficientUpdateStep (model := model) (coefficientUnderScratch quotient width)
      (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
      (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width) before.1
    ((actual.1, before.2), actual.2)
  let inner := Circuit.workspace (coefficientProductCtx ctx width)
    (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (coefficientProductCtx ctx width).canonicalFreshKey_fresh body
  let innerUpdate := fun before : Store (coefficientProductCtx ctx width) × model.HiddenState =>
    let final := update
      (before.1.pushWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
        (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh, before.2)
    ((Store.popWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh final.1.1,
      final.1.2), final.2)
  refine (Circuit.execute_workspace_mapClassical
    (environment := environment) ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh inner innerUpdate
    (fun reference {_} _ initial => ?_) Reference state).trans ?_
  · exact Circuit.execute_workspace_mapClassical (environment := environment)
      (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (coefficientProductCtx ctx width).canonicalFreshKey_fresh body update
      (fun reference {_} _ initial => by
        refine (xgcdCoefficientUpdate_execute (coefficientUnderScratch quotient width)
          (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
          (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width)
          reference initial).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl) reference initial
  · congr 1

omit [BitWord.Selected model] in
private lemma coefficientFresh_ne_cell {shape : CShape} (cell : CWriteRef ctx shape) :
    ctx.canonicalFreshKey ≠ cell.key := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  rw [same]
  exact List.mem_map_of_mem cell.toCStorageRef.present

omit [BitWord.Selected model] in
private lemma coefficientWriteUnderScratch_key (cell : CWriteRef ctx (.unsignedWord width)) :
    (coefficientWriteUnderScratch cell).key = cell.key := rfl

/-- Every original read outside the persistent coefficient cells survives both scratch releases. -/
lemma xgcdScopedCoefficient_read_other (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width)) {observed : CShape}
    (other : CInputRef ctx observed)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (store : Store ctx) :
    ((scopedCoefficientStep (model := model) quotient first second store).1).read other =
      store.read other := by
  unfold scopedCoefficientStep
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (Store.popWorkspace
      (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (coefficientProductCtx ctx width).canonicalFreshKey_fresh
      (coefficientUpdateStore (coefficientUnderScratch quotient width)
        (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
        (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width)
        ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh).pushWorkspace
            (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
            (coefficientProductCtx ctx width).canonicalFreshKey_fresh)))).read other = _
  rw [Store.read_popWorkspace_underWorkspace, Store.read_popWorkspace_underWorkspace]
  rw [xgcdCoefficientUpdate_read_other]
  · rw [Store.read_pushWorkspace_underWorkspace, Store.read_pushWorkspace_underWorkspace]
  · simpa only [CInputRef.storageKeys_underWorkspace, coefficientWriteUnderScratch_key]
      using firstFree
  · simpa only [CInputRef.storageKeys_underWorkspace, coefficientWriteUnderScratch_key]
      using secondFree
  · rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
    exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)
  · rw [CInputRef.storageKeys_underWorkspace]
    exact fun present => (coefficientProductCtx ctx width).canonicalFreshKey_fresh
      ((other.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

/-- The actual allocated scratch leaves only persistent-cell separation to the state layout. -/
lemma xgcdScopedCoefficient_store_values (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width)) (different : first.key ≠ second.key)
    (store : Store ctx) :
    let final := (scopedCoefficientStep (model := model) quotient first second store).1
    final.read (coefficientRead first) =
        Resource.WordBinaryOpcode.eval .sub width
          (.product (store.read (coefficientRead second))
            (Resource.WordBinaryOpcode.eval .mulLow width
              (.product (store.read quotient) (store.read (coefficientRead first))))) ∧
      final.read (coefficientRead second) = store.read (coefficientRead first) := by
  have actual := xgcdCoefficientUpdate_store_values (coefficientUnderScratch quotient width)
    (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
    (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width)
    different (coefficientFresh_ne_cell first) (coefficientFresh_ne_cell second)
    (coefficientFresh_ne_cell (first.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh))
    (Ne.symm (coefficientFresh_ne_cell (second.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh)))
    ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh).pushWorkspace (coefficientProductCtx ctx width).canonicalFreshKey
        (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh)
  have liftRead {ambient : RuntimeCtx model.kind} (cell : CWriteRef ambient (.unsignedWord width))
      (key : StorageKey) (fresh : key ∉ ambient.keys) :
      coefficientRead (cell.underWorkspace key (.unsignedWord width) fresh) =
        (coefficientRead cell).underWorkspace key (.unsignedWord width) fresh := rfl
  simpa only [scopedCoefficientStep, coefficientUpdateStep, BitWord.instructionStep,
    coefficientUpdateStore, Store.read_popWorkspace_underWorkspace,
    coefficientUnderScratch, coefficientWriteUnderScratch, liftRead,
    Store.read_pushWorkspace_underWorkspace] using actual

/-- Lexical allocation adds no padding operation to the original four-instruction trace. -/
lemma xgcdScopedCoefficient_eventTrace (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (path : (scopedCoefficientUpdate (model := model) quotient first second).Path) :
    (scopedCoefficientUpdate (model := model) quotient first second).eventTrace path =
      coefficientUpdateEvents model width :=
  xgcdCoefficientUpdate_eventTrace _ _ _ _ _ path

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
