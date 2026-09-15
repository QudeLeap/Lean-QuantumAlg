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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The independent original initialization, public active slots, and result copies. -/
def rawEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (initializationEvents kind width) +
    (ResourcePool.scale (Euclid.gcdFuel width) (ResourcePool.ofList (activeEvents kind width)) +
      ResourcePool.ofList (rawOutputEvents kind width))

/-- Each selected actual branch stays within one full original active sequence. -/
theorem xgcdNativeGuardedActive_pool_le (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (path : (guardedActive cells zero).Path) :
    (guardedActive cells zero).resourcePool path ≤ ResourcePool.ofList (activeEvents kind width) :=
    by
  rw [Circuit.resourcePool, xgcdNativeGuardedActive_eventTrace]
  split
  · exact le_rfl
  · exact zero_le

/-- The actual finite path vector contains at most one active allowance per scheduled iteration. -/
theorem xgcdNativeLoop_pool_le (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (count : Nat) :
    ∀ path : (Circuit.iterate count (guardedActive cells zero)).Path,
      (Circuit.iterate count (guardedActive cells zero)).resourcePool path ≤
        ResourcePool.scale count (ResourcePool.ofList (activeEvents kind width)) := by
  induction count with
  | zero =>
      intro path
      exact le_rfl
  | succ count ih =>
      intro path
      change ResourcePool.ofList ((List.ofFn (fun index : Fin (count + 1) =>
        (guardedActive cells zero).eventTrace (path index))).flatten) ≤ _
      rw [List.ofFn_succ, List.flatten_cons, ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (xgcdNativeGuardedActive_pool_le cells zero (path 0))
        (ih (fun index => path index.succ))

/-- Actual initialization, selected iterations and final copies satisfy the original ledger. -/
theorem xgcdNativeScheduledRaw_pool_le (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (scheduledRawBody cells input zero outputs).Path) :
    (scheduledRawBody cells input zero outputs).resourcePool path ≤ rawEnvelope kind width := by
  change ResourcePool.ofList (initializationEvents kind width ++
    ((Circuit.iterate (Euclid.gcdFuel width) (guardedActive cells zero)).eventTrace path.2.1 ++
      rawOutputEvents kind width)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (xgcdNativeLoop_pool_le cells zero (Euclid.gcdFuel width) path.2.1) le_rfl)

/-- The original seven state scopes introduce no hidden arithmetic events. -/
theorem xgcdNativeWithRawState_pool_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (withRawState input zero outputs).Path) :
    (withRawState input zero outputs).resourcePool path ≤ rawEnvelope kind width := by
  exact withCellsFrom_pool_le (Transport.id ctx) (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody cells (transport.liftInput input)
      (transport.liftInput zero) (outputs.transport transport)) (rawEnvelope kind width)
    (fun cells _ transport _ selected => xgcdNativeScheduledRaw_pool_le cells _ _ _ selected) path

private theorem lexical_pool_le {inner : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (budget : ResourcePool kind) (bound : ∀ selected, body.resourcePool selected ≤ budget)
    (path : (Circuit.workspace inner key shape fresh body).Path) :
    (Circuit.workspace inner key shape fresh body).resourcePool path ≤ budget := bound path

/-- The entire actual raw engine obeys the same independent native coordinate allowance. -/
theorem xgcdNativeRawEngine_pool_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (path : (rawEngine input outputs).Path) :
    (rawEngine input outputs).resourcePool path ≤ rawEnvelope kind width :=
  lexical_pool_le ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (withRawState
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero)
    (rawEnvelope kind width)
    (xgcdNativeWithRawState_pool_le
      (ctx := ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh) (width := width)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero) path

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
