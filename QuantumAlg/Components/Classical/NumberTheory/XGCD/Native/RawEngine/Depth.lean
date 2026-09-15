/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Resources

/-!
# Original serial duration of the actual raw XGCD engine

The fixed allowance contains six initialization operations, fourteen per
public Euclidean slot and three final copies. Actual inactive slots execute
identity, contributing zero duration. The bound covers arbitrary native
durations and the original zero-width input case.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent duration of the original initialization, public slots and final copies. -/
def rawDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  ((initializationEvents kind width).map duration).sum +
    (Euclid.gcdFuel width * ((activeEvents kind width).map duration).sum +
      ((rawOutputEvents kind width).map duration).sum)

/-- The actual branch emits the original active sequence precisely in its true arm. -/
theorem xgcdNativeGuardedActive_eventTrace (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (path : (guardedActive cells zero).Path) :
    (guardedActive cells zero).eventTrace path =
      if path.1.toBool then activeEvents kind width else [] := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact xgcdNativeScopedActive_eventTrace cells zero path

/-- An inactive slot costs zero; an active slot retains every actual serial dependency. -/
theorem xgcdNativeGuardedActive_depth_le (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (guardedActive cells zero).Path) :
    (guardedActive cells zero).depth duration path ≤
      ((activeEvents kind width).map duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact (xgcdNativeScopedActive_durationDepth cells zero duration path).le

/-- The real path vector contributes at most one complete active duration per public slot. -/
theorem xgcdNativeLoop_depth_le (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (count : Nat)
    (duration : Resource.Event kind → Nat)
    (path : (Circuit.iterate count (guardedActive cells zero)).Path) :
    (Circuit.iterate count (guardedActive cells zero)).depth duration path ≤
      count * ((activeEvents kind width).map duration).sum := by
  change 0 + ∑ index : Fin count, (guardedActive cells zero).depth duration (path index) ≤ _
  rw [Nat.zero_add]
  calc
    _ ≤ ∑ _index : Fin count, ((activeEvents kind width).map duration).sum :=
      Finset.sum_le_sum (fun index _ =>
        xgcdNativeGuardedActive_depth_le cells zero duration (path index))
    _ = _ := by simp

private theorem initialization_duration (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (initializationBody cells input zero).Path) :
    (initializationBody cells input zero).depth duration path =
      ((initializationEvents kind width).map duration).sum := by
  simp [initializationBody, initializationEvents, Circuit.depth, Circuit.eventDepth,
    DepthExpr.depthEval, copyFirstOp, copySecondOp, incrementFirstLeftOp, incrementSecondRightOp,
    GCD.testActiveOp, GCD.negateActiveOp, ClassicalOp.event, ClassicalOp.label]

private theorem copyRawOutputs_duration (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (duration : Resource.Event kind → Nat)
    (path : (copyRawOutputs cells outputs).Path) :
    (copyRawOutputs cells outputs).depth duration path =
      ((rawOutputEvents kind width).map duration).sum := by
  simp [copyRawOutputs, rawOutputEvents, Circuit.depth, Circuit.eventDepth,
    DepthExpr.depthEval, ClassicalOp.event, ClassicalOp.label]

/-- Initialization, selected actual iterations and final raw copies retain the original budget. -/
theorem xgcdNativeScheduledRaw_depth_le (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (duration : Resource.Event kind → Nat)
    (path : (scheduledRawBody cells input zero outputs).Path) :
    (scheduledRawBody cells input zero outputs).depth duration path ≤
      rawDepthLimit width duration := by
  change (initializationBody cells input zero).depth duration path.1 +
    ((Circuit.iterate (Euclid.gcdFuel width) (guardedActive cells zero)).depth duration path.2.1 +
      (copyRawOutputs cells outputs).depth duration path.2.2) ≤ _
  rw [initialization_duration, copyRawOutputs_duration]
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (xgcdNativeLoop_depth_le cells zero (Euclid.gcdFuel width) duration path.2.1) _) _

/-- The seven actual state scopes add no hidden native duration. -/
theorem xgcdNativeWithRawState_depth_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (duration : Resource.Event kind → Nat) (path : (withRawState input zero outputs).Path) :
    (withRawState input zero outputs).depth duration path ≤ rawDepthLimit width duration := by
  exact withCellsFrom_depth_le (Transport.id ctx) (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody cells (transport.liftInput input)
      (transport.liftInput zero) (outputs.transport transport)) duration
    (rawDepthLimit width duration)
    (fun cells _ transport _ selected =>
      xgcdNativeScheduledRaw_depth_le cells _ _ _ duration selected) path

private theorem lexical_depth_le {inner : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (duration : Resource.Event kind → Nat) (budget : Nat)
    (bound : ∀ selected, body.depth duration selected ≤ budget)
    (path : (Circuit.workspace inner key shape fresh body).Path) :
    (Circuit.workspace inner key shape fresh body).depth duration path ≤ budget := bound path

/-- The original independent zero-word allocation retains the same whole-engine duration bound. -/
theorem xgcdNativeRawEngine_depth_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (duration : Resource.Event kind → Nat)
    (path : (rawEngine input outputs).Path) :
    (rawEngine input outputs).depth duration path ≤ rawDepthLimit width duration :=
  lexical_depth_le ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (withRawState
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero)
    duration (rawDepthLimit width duration)
    (xgcdNativeWithRawState_depth_le
      (ctx := ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh) (width := width)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero duration) path

/-- Unit native durations specialize the original schedule to its explicit linear bound. -/
theorem xgcdNativeRawDepthLimit_unit (kind : ProblemKind) (width : Nat) :
    rawDepthLimit width (fun _ : Resource.Event kind => 1) = 28 * width + 23 := by
  simp only [rawDepthLimit, initializationEvents, activeEvents, coefficientUpdateEvents,
    rawOutputEvents, Euclid.gcdFuel, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
