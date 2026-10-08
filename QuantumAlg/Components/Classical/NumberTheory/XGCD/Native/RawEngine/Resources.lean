/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Depth

/-!
# Independent native event allowance of the actual raw XGCD engine

Every native coordinate keeps its original operand width. Actual inactive
slots emit no arithmetic events. The fixed allowance includes initialization,
at most one full active sequence per original public slot, and all three
final result copies. Internal lexical entry and release add no events.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The independent original initialization, public active slots, and result copies. -/
def rawEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ResourcePool.ofList (initializationEvents model width) +
    (ResourcePool.scale (Euclid.gcdFuel width) (ResourcePool.ofList (activeEvents model width)) +
      ResourcePool.ofList (rawOutputEvents model width))

/-- Each selected actual branch stays within one full original active sequence. -/
theorem xgcdNativeGuardedActive_pool_le (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (guardedActive (model := model) cells zero).Path) :
    (guardedActive (model := model) cells zero).resourcePool path ≤
      ResourcePool.ofList (activeEvents model width) :=
    by
  rw [Circuit.resourcePool, xgcdNativeGuardedActive_eventTrace]
  split
  · exact le_rfl
  · exact zero_le

/-- The actual finite path vector contains at most one active allowance per scheduled iteration. -/
theorem xgcdNativeLoop_pool_le (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (count : Nat) :
    ∀ path : (Circuit.iterate count (guardedActive (model := model) cells zero)).Path,
      (Circuit.iterate count (guardedActive (model := model) cells zero)).resourcePool path ≤
        ResourcePool.scale count (ResourcePool.ofList (activeEvents model width)) := by
  induction count with
  | zero =>
      intro path
      exact le_rfl
  | succ count ih =>
      intro path
      change ResourcePool.ofList ((List.ofFn (fun index : Fin (count + 1) =>
        (guardedActive (model := model) cells zero).eventTrace (path index))).flatten) ≤ _
      rw [List.ofFn_succ, List.flatten_cons, ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (xgcdNativeGuardedActive_pool_le cells zero (path 0))
        (ih (fun index => path index.succ))

/-- Actual initialization, selected iterations and final copies satisfy the original ledger. -/
theorem xgcdNativeScheduledRaw_pool_le (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (scheduledRawBody (model := model) cells input zero outputs).Path) :
    (scheduledRawBody (model := model) cells input zero outputs).resourcePool path ≤
      rawEnvelope model width := by
  change ResourcePool.ofList
    ((initializationBody (model := model) cells input zero).eventTrace path.1 ++
      ((Circuit.iterate (Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).eventTrace path.2.1 ++
        (copyRawOutputs (model := model) cells outputs).eventTrace path.2.2)) ≤ _
  rw [xgcdNativeInitialization_eventTrace, xgcdNativeCopyRawOutputs_eventTrace]
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (xgcdNativeLoop_pool_le cells zero (Euclid.gcdFuel width) path.2.1) le_rfl)

/-- The original seven state scopes introduce no hidden arithmetic events. -/
theorem xgcdNativeWithRawState_pool_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (withRawState (model := model) input zero outputs).Path) :
    (withRawState (model := model) input zero outputs).resourcePool path ≤
      rawEnvelope model width := by
  exact withCellsFrom_pool_le (Transport.id ctx) (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody (model := model) cells (transport.liftInput input)
      (transport.liftInput zero) (outputs.transport transport)) (rawEnvelope model width)
    (fun cells _ transport _ selected => xgcdNativeScheduledRaw_pool_le cells _ _ _ selected) path

omit [BitWord.Selected model] in
private theorem lexical_pool_le {inner : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit model (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (budget : ResourcePool model) (bound : ∀ selected, body.resourcePool selected ≤ budget)
    (path : (Circuit.workspace inner key shape fresh body).Path) :
    (Circuit.workspace inner key shape fresh body).resourcePool path ≤ budget := bound path

/-- The entire actual raw engine obeys the same independent native coordinate allowance. -/
theorem xgcdNativeRawEngine_pool_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (path : (rawEngine (model := model) input outputs).Path) :
    (rawEngine (model := model) input outputs).resourcePool path ≤ rawEnvelope model width :=
  lexical_pool_le ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (withRawState (model := model)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero)
    (rawEnvelope model width)
    (xgcdNativeWithRawState_pool_le
      (ctx := ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh) (width := width)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero) path

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
