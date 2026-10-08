/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Trace
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Depth

/-!
# Exact raw XGCD cost from the original number of active steps

The actual instruction sequence is serial, so each path's duration is the
sum over that same path's events. The certified original unpadded trace then
gives six initialization operations, fourteen per actual active step and
three output copies. Public fuel remains an upper bound rather than a count
of executed arithmetic steps.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

private theorem guarded_duration_trace (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (guardedActive (model := model) cells zero).Path) :
    (guardedActive (model := model) cells zero).depth duration path =
      (((guardedActive (model := model) cells zero).eventTrace path).map duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact (xgcdNativeScopedActive_durationDepth cells zero duration path).trans
          (congrArg (fun events => (events.map duration).sum)
            (xgcdNativeScopedActive_eventTrace cells zero path)).symm

private theorem loop_duration_trace (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (count : Nat)
    (duration : Resource.Event model → Nat)
    (path : (Circuit.iterate count (guardedActive (model := model) cells zero)).Path) :
    (Circuit.iterate count (guardedActive (model := model) cells zero)).depth duration path =
      (((Circuit.iterate count (guardedActive (model := model) cells zero)).eventTrace path).map
        duration).sum := by
  change 0 + ∑ index : Fin count, (guardedActive (model := model) cells zero).depth duration
    (path index) =
    (((List.ofFn (fun index : Fin count =>
      (guardedActive (model := model) cells zero).eventTrace (path index))).flatten).map
        duration).sum
  simp only [Nat.zero_add, List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl
    (fun index _ => guarded_duration_trace cells zero duration (path index))

private theorem scheduled_duration_trace (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (duration : Resource.Event model → Nat)
    (path : (scheduledRawBody (model := model) cells input zero outputs).Path) :
    (scheduledRawBody (model := model) cells input zero outputs).depth duration path =
      (((scheduledRawBody (model := model) cells input zero outputs).eventTrace path).map
        duration).sum := by
  rw [scheduled_eventTrace]
  change (initializationBody (model := model) cells input zero).depth duration path.1 +
    ((Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive (model := model) cells zero)).depth duration path.2.1 +
      (copyRawOutputs (model := model) cells outputs).depth duration path.2.2) =
    ((initializationEvents model width ++
      ((Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).eventTrace path.2.1 ++ rawOutputEvents model
          width)).map
          duration).sum
  rw [initialization_duration, loop_duration_trace, copyRawOutputs_duration]
  simp only [List.map_append, List.sum_append]

private theorem with_state_duration_trace
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (duration : Resource.Event model → Nat) (path : (withRawState (model := model) input zero
      outputs).Path) :
    (withRawState (model := model) input zero outputs).depth duration path =
      (((withRawState (model := model) input zero outputs).eventTrace path).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody (model := model) cells
      (transport.liftInput input) (transport.liftInput zero) (outputs.transport transport))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ _ _ selected => scheduled_duration_trace cells _ _ _ duration selected) path

omit [BitWord.Selected model] in
private theorem lexical_duration_trace {inner : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit model (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (duration : Resource.Event model → Nat)
    (same : ∀ selected, body.depth duration selected =
      ((body.eventTrace selected).map duration).sum)
    (path : (Circuit.workspace inner key shape fresh body).Path) :
    (Circuit.workspace inner key shape fresh body).depth duration path =
      (((Circuit.workspace inner key shape fresh body).eventTrace path).map duration).sum :=
  same path

/-- The actual raw instruction dependency graph is serial along every selected path. -/
theorem xgcdNativeRawEngine_duration_eventTrace
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (duration : Resource.Event model → Nat)
    (path : (rawEngine (model := model) input outputs).Path) :
    (rawEngine (model := model) input outputs).depth duration path =
      (((rawEngine (model := model) input outputs).eventTrace path).map duration).sum :=
  lexical_duration_trace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (withRawState (model := model)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero) duration
    (with_state_duration_trace
      (ctx := ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh) (width := width)
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
      (GCD.cellRead (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh)) outputs.underZero duration) path

omit [BitWord.Selected model] in
private theorem repeated_duration {State : Type} (states : List State)
    (events : List (Resource.Event model)) (duration : Resource.Event model → Nat) :
    (((states.flatMap (fun _ => events)).map duration).sum) =
      states.length * (events.map duration).sum := by
  induction states with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, inductionHypothesis,
        List.length_cons, Nat.succ_mul]
      omega

/-- Original active-step count determines the exact duration sum of the raw event list. -/
theorem xgcdNativeRawEvents_duration (input : PureXGCD.Input width)
    (duration : Resource.Event model → Nat) :
    ((rawEvents model input).map duration).sum =
      ((initializationEvents model width).map duration).sum +
        (ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount input *
          ((activeEvents model width).map duration).sum +
          ((rawOutputEvents model width).map duration).sum) := by
  unfold rawEvents
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append, repeated_duration]
  rfl

/-- Unit durations count six setup operations, fourteen per genuine step and three raw copies. -/
theorem xgcdNativeRawEvents_unit_duration (model : ExecutionModel) [BitWord.Selected model]
  (input : PureXGCD.Input width) :
    ((rawEvents model input).map (fun _ => 1)).sum =
      14 * ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount input + 9 := by
  rw [xgcdNativeRawEvents_duration]
  simp only [initializationEvents, activeEvents, coefficientUpdateEvents, rawOutputEvents,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  omega

/-- The exact active-count duration satisfies the unchanged original width-derived ceiling. -/
theorem xgcdNativeRawEvents_unit_duration_le (model : ExecutionModel) [BitWord.Selected model]
    (input : PureXGCD.Input width) :
    ((rawEvents model input).map (fun _ => 1)).sum ≤ 28 * width + 23 := by
  rw [xgcdNativeRawEvents_unit_duration]
  have steps := ClassicalAlgorithms.NumberTheory.XGCD.xgcdTraceStepCount_le_gcdFuel input
  simp only [ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel] at steps
  omega

omit [BitWord.Selected model] in
private theorem repeated_pool {State : Type} (states : List State)
    (events : List (Resource.Event model)) :
    ResourcePool.ofList (states.flatMap (fun _ => events)) =
      ResourcePool.scale states.length (ResourcePool.ofList events) := by
  induction states with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons, ResourcePool.ofList_append, inductionHypothesis,
        List.length_cons, ResourcePool.scale_succ]

/-- Each native resource coordinate uses exactly the original number of actual active updates. -/
theorem xgcdNativeRawEvents_resourcePool (input : PureXGCD.Input width) :
    ResourcePool.ofList (rawEvents model input) =
      ResourcePool.ofList (initializationEvents model width) +
        (ResourcePool.scale (ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount input)
          (ResourcePool.ofList (activeEvents model width)) +
          ResourcePool.ofList (rawOutputEvents model width)) := by
  unfold rawEvents
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, repeated_pool]
  rfl

/-- The same actual full record has the exact original active-count duration at any native costs. -/
theorem xgcdNativeRawEngine_record_duration
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (distinct : outputs.Distinct)
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (rawEngine (model
      := model) input outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (rawEngine (model := model) input outputs).execute Reference state = state.mapClassical
        (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (store : Store ctx × model.HiddenState) (duration : Resource.Event model → Nat) :
    (rawEngine (model := model) input outputs).depth duration (record store).2 =
      ((initializationEvents model width).map duration).sum +
        (ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount
          (GCD.decodeOperands (store.1.read input)) * ((activeEvents model width).map
            duration).sum +
          ((rawOutputEvents model width).map duration).sum) := by
  rw [xgcdNativeRawEngine_duration_eventTrace,
    xgcdNativeRawEngine_record_eventTrace input outputs distinct record equation store,
    xgcdNativeRawEvents_duration]

/-- Actual unit-duration depth counts only the original active steps from the actual input. -/
theorem xgcdNativeRawEngine_record_unitDepth
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (distinct : outputs.Distinct)
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (rawEngine (model
      := model) input outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (rawEngine (model := model) input outputs).execute Reference state = state.mapClassical
        (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2))))) (store : Store ctx ×
          model.HiddenState) :
    (rawEngine (model := model) input outputs).depth (fun _ => 1) (record store).2 =
      14 * ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount
        (GCD.decodeOperands (store.1.read input)) + 9 := by
  rw [xgcdNativeRawEngine_duration_eventTrace,
    xgcdNativeRawEngine_record_eventTrace input outputs distinct record equation store,
    xgcdNativeRawEvents_unit_duration]

/-- The actual full record has the exact active-count resource pool at every native coordinate. -/
theorem xgcdNativeRawEngine_record_active_resourcePool
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (distinct : outputs.Distinct)
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (rawEngine (model
      := model) input outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (rawEngine (model := model) input outputs).execute Reference state = state.mapClassical
        (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2))))) (store : Store ctx ×
          model.HiddenState) :
    (rawEngine (model := model) input outputs).resourcePool (record store).2 =
      ResourcePool.ofList (initializationEvents model width) +
        (ResourcePool.scale (ClassicalAlgorithms.NumberTheory.XGCD.traceStepCount
          (GCD.decodeOperands (store.1.read input))) (ResourcePool.ofList (activeEvents model
            width)) +
          ResourcePool.ofList (rawOutputEvents model width)) := by
  rw [xgcdNativeRawEngine_record_resourcePool input outputs distinct record equation store,
    xgcdNativeRawEvents_resourcePool]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
