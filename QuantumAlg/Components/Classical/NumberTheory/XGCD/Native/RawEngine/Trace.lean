/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Loop.Trace
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Trace

/-!
# Exact events of the same complete actual raw XGCD record

Six original initialization events precede the original unpadded active path
and three final output copies. Seven actual state scopes and the independent
fresh zero scope preserve this exact event list. The statement applies to any
record already certifying the complete actual interpreter.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original initialization, unpadded active steps and the three raw result copies. -/
def rawEvents (model : ExecutionModel) [BitWord.Selected model] {width : Nat} (input :
  PureXGCD.Input width) :
    List (Resource.Event model) :=
  initializationEvents model width ++
    ((PureXGCD.trace input).flatMap (fun _ => activeEvents model width) ++
      rawOutputEvents model width)

private theorem scheduled_eventTrace (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (path : (scheduledRawBody (model := model) cells input zero outputs).Path) :
    (scheduledRawBody (model := model) cells input zero outputs).eventTrace path =
      initializationEvents model width ++
        ((Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
          (guardedActive (model := model) cells zero)).eventTrace path.2.1 ++
          rawOutputEvents model width) := by
  change (initializationBody (model := model) cells input zero).eventTrace path.1 ++
    ((Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive (model := model) cells zero)).eventTrace path.2.1 ++
      (copyRawOutputs (model := model) cells outputs).eventTrace path.2.2) = _
  rw [xgcdNativeInitialization_eventTrace, xgcdNativeCopyRawOutputs_eventTrace]

private theorem scheduled_record_execute (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).execute Reference state = state.mapClassical
          (fun entry =>
          let result := record (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scheduledRawBody (model := model) cells input zero outputs).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scheduledRawRecord (model := model) cells input zero outputs record
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord (initializationBody (model := model) cells input zero)
    (.seq (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive (model := model) cells zero)) (copyRawOutputs (model := model) cells outputs))
    (fun before =>
      let result := initializationStep (model := model) cells input zero before.1
      ((result.1, before.2), result.2))
    (Circuit.sequenceRecord
      (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)) (copyRawOutputs (model := model) cells
          outputs) record
      (fun before =>
        let result := copyRawOutputsStep (model := model) cells outputs before.1
        ((result.1, before.2), result.2)))
  · intro reference history historyFinite initial
    refine (xgcdNativeInitialization_execute cells input zero reference initial).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  · intro reference history historyFinite initial
    exact Circuit.execute_sequenceRecord
      (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)) (copyRawOutputs (model := model) cells
          outputs) record
      (fun before =>
        let result := copyRawOutputsStep (model := model) cells outputs before.1
        ((result.1, before.2), result.2)) equation
      (fun finalReference {_} _ finalState => by
        refine (xgcdNativeCopyRawOutputs_execute cells outputs finalReference finalState).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl) reference initial

/-- A certified record of the initialized schedule emits exactly the original represented trace. -/
theorem xgcdNativeScheduledRaw_record_eventTrace {outer : RuntimeCtx model.kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) (outputs : RawOutputs outer width)
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (scheduledRawBody (model := model) cells (transport.liftInput input) (transport.liftInput
        zero)
        (outputs.transport transport)).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (scheduledRawBody (model := model) cells (transport.liftInput input) (transport.liftInput
        zero)
        (outputs.transport transport)).execute Reference state = state.mapClassical (fun entry =>
          let result := record (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (store : Store ctx × model.HiddenState) (initialized : cells.Initialized store.1)
    (zeroValue : (store.1.read (transport.liftInput zero)).toNat = 0) :
    (scheduledRawBody (model := model) cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport)).eventTrace (record store).2 =
        rawEvents model (GCD.decodeOperands (store.1.read (transport.liftInput input))) := by
  obtain ⟨loopRecord, loopEquation, _⟩ :=
    xgcdNativeInitializedLoop_actualRecord (model := model) cells distinct transport separated
      input zero
  have same := Circuit.executionRecord_unique
    (scheduledRawBody (model := model) cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport)) record
    (scheduledRawRecord (model := model) cells (transport.liftInput input) (transport.liftInput
      zero)
      (outputs.transport transport) loopRecord) equation
    (scheduled_record_execute cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport) loopRecord loopEquation)
  rw [same, scheduled_eventTrace]
  have loopTrace := xgcdNativeLoop_record_eventTrace cells distinct (transport.liftInput zero)
    (xgcdNativeState_input_separated cells transport separated zero)
    (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width) loopRecord loopEquation
    (initializationStore cells (transport.liftInput input) (transport.liftInput zero) store.1,
      store.2)
    (GCD.decodeOperands (store.1.read (transport.liftInput input)))
    (xgcdNativeInitialization_ready cells distinct transport separated
      input zero store.1 initialized zeroValue)
    (xgcdNativeInitialization_state cells distinct transport separated
      input zero store.1 initialized zeroValue) le_rfl
  change initializationEvents model width ++
    ((Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive (model := model) cells (transport.liftInput zero))).eventTrace
        (loopRecord (initializationStore cells
          (transport.liftInput input) (transport.liftInput zero) store.1, store.2)).2 ++
      rawOutputEvents model width) = _
  rw [loopTrace]
  rfl

private theorem with_raw_state_trace_record
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (distinct : outputs.Distinct) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (withRawState
      (model := model) input zero outputs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withRawState (model := model) input zero outputs).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (before.1.read zero).toNat = 0 →
        (withRawState (model := model) input zero outputs).eventTrace (record before).2 =
          rawEvents model (GCD.decodeOperands (before.1.read input)) := by
  let Trace (before : Store ctx) (events : List (Resource.Event model)) : Prop :=
    (before.read zero).toNat = 0 → events = rawEvents model (GCD.decodeOperands (before.read input))
  refine withCells_actualRecord_initialized_trace ctx (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody (model := model) cells
      (transport.liftInput input) (transport.liftInput zero) (outputs.transport transport)) Trace ?_
  intro inner cells cellsDistinct transport separated
  obtain ⟨record, equation, _⟩ := xgcdNativeScheduledRaw_actualRecord
    (model := model) cells cellsDistinct transport separated input zero outputs distinct
  refine ⟨record, equation, ?_⟩
  intro source before reads initialized zeroValue
  have result := xgcdNativeScheduledRaw_record_eventTrace cells cellsDistinct transport separated
    input zero outputs record equation before initialized (by
      rw [reads zero]
      exact zeroValue)
  rw [reads input] at result
  exact result

/-- The same selected actual state-scope record retains its exact original schedule events. -/
theorem xgcdNativeWithRawState_record_eventTrace
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (distinct : outputs.Distinct)
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (withRawState
      (model := model) input zero outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (withRawState (model := model) input zero outputs).execute Reference state =
        state.mapClassical (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (store : Store ctx × model.HiddenState) (zeroValue : (store.1.read zero).toNat = 0) :
    (withRawState (model := model) input zero outputs).eventTrace (record store).2 =
      rawEvents model (GCD.decodeOperands (store.1.read input)) := by
  obtain ⟨other, otherEquation, trace⟩ := with_raw_state_trace_record input zero outputs distinct
  rw [Circuit.executionRecord_unique (withRawState (model := model) input zero outputs)
    record other equation otherEquation]
  exact trace store zeroValue

omit [BitWord.Selected model] in
private theorem lexical_record_trace {inner : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit model (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (bodyRecord : Store (inner.addWorkspace key shape fresh) × model.HiddenState →
      (Store (inner.addWorkspace key shape fresh) × model.HiddenState) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (inner.addWorkspace key shape fresh) Reference (model.HiddenState × History)),
      body.execute Reference state = state.mapClassical (fun entry =>
        let result := bodyRecord (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (record : Store inner × model.HiddenState → (Store inner × model.HiddenState) ×
      (Circuit.workspace inner key shape fresh body).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      (Circuit.workspace inner key shape fresh body).execute Reference state =
        state.mapClassical (fun entry =>
          let result := record (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2))))) (store : Store inner ×
            model.HiddenState) :
    (Circuit.workspace inner key shape fresh body).eventTrace (record store).2 =
      body.eventTrace (bodyRecord (store.1.pushWorkspace key shape fresh, store.2)).2 := by
  rw [Circuit.executionRecord_unique (Circuit.workspace inner key shape fresh body)
    record (Circuit.workspaceRecord key shape fresh body bodyRecord) equation
    (Circuit.execute_workspaceRecord key shape fresh body bodyRecord bodyEquation)]
  rfl

/-- The same actual raw-engine record emits the original exact trace with no internal premises. -/
theorem xgcdNativeRawEngine_record_eventTrace
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
    (rawEngine (model := model) input outputs).eventTrace (record store).2 =
      rawEvents model (GCD.decodeOperands (store.1.read input)) := by
  let key := ctx.canonicalFreshKey
  let shape := CShape.unsignedWord width
  let fresh := ctx.canonicalFreshKey_fresh
  let liftedInput := input.underWorkspace key shape fresh
  let zero := GCD.cellRead (CWriteRef.workspaceHead ctx key shape fresh)
  let liftedOutputs := outputs.underZero
  let body := withRawState (model := model) liftedInput zero liftedOutputs
  have liftedDistinct : liftedOutputs.Distinct := distinct
  obtain ⟨bodyRecord, bodyEquation, _⟩ :=
    xgcdNativeWithRawState_actualRecord (model := model) liftedInput zero liftedOutputs
      liftedDistinct
  have inherited := lexical_record_trace key shape fresh body bodyRecord bodyEquation
    record equation store
  have traced := xgcdNativeWithRawState_record_eventTrace liftedInput zero liftedOutputs
    liftedDistinct bodyRecord bodyEquation (store.1.pushWorkspace key shape fresh, store.2) (by rfl)
  have inputRead : (store.1.pushWorkspace key shape fresh).read liftedInput = store.1.read input :=
    Store.read_pushWorkspace_underWorkspace store.1 key shape fresh input
  rw [inputRead] at traced
  exact inherited.trans traced

/-- Resource accounting is exactly the pool of events from that same certified actual record. -/
theorem xgcdNativeRawEngine_record_resourcePool
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
      ResourcePool.ofList (rawEvents model (GCD.decodeOperands (store.1.read input))) := by
  exact congrArg ResourcePool.ofList
    (xgcdNativeRawEngine_record_eventTrace input outputs distinct record equation store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
