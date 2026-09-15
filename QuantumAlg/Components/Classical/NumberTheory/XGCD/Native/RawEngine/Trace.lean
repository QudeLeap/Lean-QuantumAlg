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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original initialization, unpadded active steps and the three raw result copies. -/
def rawEvents (kind : ProblemKind) {width : Nat} (input : PureXGCD.Input width) :
    List (Resource.Event kind) :=
  initializationEvents kind width ++
    ((PureXGCD.trace input).flatMap (fun _ => activeEvents kind width) ++
      rawOutputEvents kind width)

private theorem scheduled_record_execute (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (record : Store ctx → Store ctx ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)).execute Reference state = state.mapClassical (fun entry =>
          ((record entry.1).1, (entry.2, (record entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scheduledRawBody cells input zero outputs).execute Reference state =
      state.mapClassical (fun entry =>
        ((scheduledRawRecord cells input zero outputs record entry.1).1,
          (entry.2, (scheduledRawRecord cells input zero outputs record entry.1).2))) := by
  apply Circuit.execute_sequenceRecord (initializationBody cells input zero)
    (.seq (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive cells zero)) (copyRawOutputs cells outputs))
    (fun before => (initializationStore cells input zero before,
      ((), ((), ((), ((), ((), ())))))))
    (Circuit.sequenceRecord
      (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)) (copyRawOutputs cells outputs) record
      (fun before => (copyRawOutputsStore cells outputs before, ((), ((), ())))))
  · intro reference history historyFinite initial
    refine (xgcdNativeInitialization_execute cells input zero reference initial).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · intro reference history historyFinite initial
    exact Circuit.execute_sequenceRecord
      (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)) (copyRawOutputs cells outputs) record
      (fun before => (copyRawOutputsStore cells outputs before, ((), ((), ())))) equation
      (fun finalReference {_} _ finalState => by
        refine (xgcdNativeCopyRawOutputs_execute cells outputs finalReference finalState).trans ?_
        congr 1
        exact Subsingleton.elim _ _) reference initial

/-- A certified record of the initialized schedule emits exactly the original represented trace. -/
theorem xgcdNativeScheduledRaw_record_eventTrace {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) (outputs : RawOutputs outer width)
    (record : Store ctx → Store ctx ×
      (scheduledRawBody cells (transport.liftInput input) (transport.liftInput zero)
        (outputs.transport transport)).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (scheduledRawBody cells (transport.liftInput input) (transport.liftInput zero)
        (outputs.transport transport)).execute Reference state = state.mapClassical (fun entry =>
          ((record entry.1).1, (entry.2, (record entry.1).2))))
    (store : Store ctx) (initialized : cells.Initialized store)
    (zeroValue : (store.read (transport.liftInput zero)).toNat = 0) :
    (scheduledRawBody cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport)).eventTrace (record store).2 =
        rawEvents kind (GCD.decodeOperands (store.read (transport.liftInput input))) := by
  obtain ⟨loopRecord, loopEquation, _⟩ :=
    xgcdNativeInitializedLoop_actualRecord cells distinct transport separated input zero
  have same := Circuit.executionRecord_unique
    (scheduledRawBody cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport)) record
    (scheduledRawRecord cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport) loopRecord) equation
    (scheduled_record_execute cells (transport.liftInput input) (transport.liftInput zero)
      (outputs.transport transport) loopRecord loopEquation)
  rw [same]
  have loopTrace := xgcdNativeLoop_record_eventTrace cells distinct (transport.liftInput zero)
    (xgcdNativeState_input_separated cells transport separated zero)
    (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width) loopRecord loopEquation
    (initializationStore cells (transport.liftInput input) (transport.liftInput zero) store)
    (GCD.decodeOperands (store.read (transport.liftInput input)))
    (xgcdNativeInitialization_ready cells distinct transport separated
      input zero store initialized zeroValue)
    (xgcdNativeInitialization_state cells distinct transport separated
      input zero store initialized zeroValue) le_rfl
  change initializationEvents kind width ++
    ((Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive cells (transport.liftInput zero))).eventTrace
        (loopRecord (initializationStore cells
          (transport.liftInput input) (transport.liftInput zero) store)).2 ++
      rawOutputEvents kind width) = _
  rw [loopTrace]
  rfl

private theorem with_raw_state_trace_record
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (outputs : RawOutputs ctx width)
    (distinct : outputs.Distinct) :
    ∃ record : Store ctx → Store ctx × (withRawState input zero outputs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withRawState input zero outputs).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (before.read zero).toNat = 0 →
        (withRawState input zero outputs).eventTrace (record before).2 =
          rawEvents kind (GCD.decodeOperands (before.read input)) := by
  let Trace (before : Store ctx) (events : List (Resource.Event kind)) : Prop :=
    (before.read zero).toNat = 0 → events = rawEvents kind (GCD.decodeOperands (before.read input))
  refine withCells_actualRecord_initialized_trace ctx (stateShapes width)
    (fun cells _ transport _ => scheduledRawBody cells
      (transport.liftInput input) (transport.liftInput zero) (outputs.transport transport)) Trace ?_
  intro inner cells cellsDistinct transport separated
  obtain ⟨record, equation, _⟩ := xgcdNativeScheduledRaw_actualRecord
    cells cellsDistinct transport separated input zero outputs distinct
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
    (record : Store ctx → Store ctx × (withRawState input zero outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (withRawState input zero outputs).execute Reference state = state.mapClassical (fun entry =>
        ((record entry.1).1, (entry.2, (record entry.1).2))))
    (store : Store ctx) (zeroValue : (store.read zero).toNat = 0) :
    (withRawState input zero outputs).eventTrace (record store).2 =
      rawEvents kind (GCD.decodeOperands (store.read input)) := by
  obtain ⟨other, otherEquation, trace⟩ := with_raw_state_trace_record input zero outputs distinct
  rw [Circuit.executionRecord_unique (withRawState input zero outputs)
    record other equation otherEquation]
  exact trace store zeroValue

private theorem lexical_record_trace {inner : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (bodyRecord : Store (inner.addWorkspace key shape fresh) →
      Store (inner.addWorkspace key shape fresh) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (inner.addWorkspace key shape fresh) Reference History),
      body.execute Reference state = state.mapClassical (fun entry =>
        ((bodyRecord entry.1).1, (entry.2, (bodyRecord entry.1).2))))
    (record : Store inner → Store inner × (Circuit.workspace inner key shape fresh body).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State inner Reference History),
      (Circuit.workspace inner key shape fresh body).execute Reference state =
        state.mapClassical (fun entry =>
          ((record entry.1).1, (entry.2, (record entry.1).2)))) (store : Store inner) :
    (Circuit.workspace inner key shape fresh body).eventTrace (record store).2 =
      body.eventTrace (bodyRecord (store.pushWorkspace key shape fresh)).2 := by
  rw [Circuit.executionRecord_unique (Circuit.workspace inner key shape fresh body)
    record (Circuit.workspaceRecord key shape fresh body bodyRecord) equation
    (Circuit.execute_workspaceRecord key shape fresh body bodyRecord bodyEquation)]
  rfl

/-- The same actual raw-engine record emits the original exact trace with no internal premises. -/
theorem xgcdNativeRawEngine_record_eventTrace
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (distinct : outputs.Distinct)
    (record : Store ctx → Store ctx × (rawEngine input outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (rawEngine input outputs).execute Reference state = state.mapClassical (fun entry =>
        ((record entry.1).1, (entry.2, (record entry.1).2)))) (store : Store ctx) :
    (rawEngine input outputs).eventTrace (record store).2 =
      rawEvents kind (GCD.decodeOperands (store.read input)) := by
  let key := ctx.canonicalFreshKey
  let shape := CShape.unsignedWord width
  let fresh := ctx.canonicalFreshKey_fresh
  let liftedInput := input.underWorkspace key shape fresh
  let zero := GCD.cellRead (CWriteRef.workspaceHead ctx key shape fresh)
  let liftedOutputs := outputs.underZero
  let body := withRawState liftedInput zero liftedOutputs
  have liftedDistinct : liftedOutputs.Distinct := distinct
  obtain ⟨bodyRecord, bodyEquation, _⟩ :=
    xgcdNativeWithRawState_actualRecord liftedInput zero liftedOutputs liftedDistinct
  have inherited := lexical_record_trace key shape fresh body bodyRecord bodyEquation
    record equation store
  have traced := xgcdNativeWithRawState_record_eventTrace liftedInput zero liftedOutputs
    liftedDistinct bodyRecord bodyEquation (store.pushWorkspace key shape fresh) (by rfl)
  have inputRead : (store.pushWorkspace key shape fresh).read liftedInput = store.read input :=
    Store.read_pushWorkspace_underWorkspace store key shape fresh input
  rw [inputRead] at traced
  exact inherited.trans traced

/-- Resource accounting is exactly the pool of events from that same certified actual record. -/
theorem xgcdNativeRawEngine_record_resourcePool
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (distinct : outputs.Distinct)
    (record : Store ctx → Store ctx × (rawEngine input outputs).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (rawEngine input outputs).execute Reference state = state.mapClassical (fun entry =>
        ((record entry.1).1, (entry.2, (record entry.1).2)))) (store : Store ctx) :
    (rawEngine input outputs).resourcePool (record store).2 =
      ResourcePool.ofList (rawEvents kind (GCD.decodeOperands (store.read input))) := by
  exact congrArg ResourcePool.ofList
    (xgcdNativeRawEngine_record_eventTrace input outputs distinct record equation store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
