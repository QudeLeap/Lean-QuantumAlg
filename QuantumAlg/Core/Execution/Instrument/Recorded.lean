/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction

public import QuantumAlg.Core.Execution.Instrument.Scope
import all QuantumAlg.Core.Execution.Instrument.Scope
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Composition.Identity

/-!
# Actual complete classical preparation before an instrument body

The preparation uses its proved full Store and service-state record. The measured
body reads exactly that returned Store and service state. No independence of
the preparation Path or returned service state is required. Both real Paths and
the incoming History remain present in every retained density fiber.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Outcome : Type} [Fintype Outcome]
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- The original strict child's identity embedding keeps its actual operator and complete record. -/
public def Instrument.embedIdentity
    {code : Circuit (.quantum gates oracles operations services) ctx ctx false}
    (actual : Instrument code Outcome environment) :
    Instrument (Circuit.embed (allowAllocation := true)
      (model := .quantum gates oracles operations services)
      (ContextEmbedding.identity ctx) code) Outcome environment where
  record := actual.record
  operator := actual.operator
  blocks := by
    intro Reference History _ state result
    exact (congrArg (fun output : State ctx Reference
      (services.HiddenState × (History × code.Path)) => (output.block result).matrix)
        (Circuit.execute_identity_embed code environment Reference state)).trans
      (actual.blocks Reference state result)

variable {preparation body : Circuit (.quantum gates oracles operations services)
  ctx ctx true}

/-- Full returned service state and the two actual Paths of preparation then measured body. -/
def sourceRecordedPrefixRecord
    (prefixRecord : Store ctx × services.HiddenState →
      (Store ctx × services.HiddenState) × preparation.Path)
    (bodyRecord : Store ctx → Outcome → Store ctx × body.Path)
    {History : Type} (original : Store ctx × (services.HiddenState × History))
    (outcome : Outcome) :
    Store ctx × (services.HiddenState × (History × (preparation.seq body).Path)) :=
  let first := prefixRecord (original.1, original.2.1)
  let last := bodyRecord first.1.1 outcome
  (last.1, (first.1.2, (original.2.2, (first.2, last.2))))

/-- A true classical record composes with the original body without fixing a hidden state. -/
lemma sourceRecordedPrefix_blocks
    (prefixRecord : Store ctx × services.HiddenState →
      (Store ctx × services.HiddenState) × preparation.Path)
    (prefixActual : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      preparation.execute environment Reference state =
        state.mapClassical (fun original =>
          let next := prefixRecord (original.1, original.2.1)
          (next.1.1, (next.1.2, (original.2.2, next.2)))))
    (actual : Instrument body Outcome environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × (preparation.seq body).Path))) :
    (((preparation.seq body).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        if sourceRecordedPrefixRecord prefixRecord actual.record original outcome = result then
          referenceLift Reference
              (actual.operator (prefixRecord (original.1, original.2.1)).1.1 outcome) *
            (state.block original).matrix *
              (referenceLift Reference
                (actual.operator (prefixRecord (original.1, original.2.1)).1.1 outcome)
                ).conjTranspose
        else 0 := by
  let update := fun original : Store ctx × (services.HiddenState × History) =>
    let next := prefixRecord (original.1, original.2.1)
    (next.1.1, (next.1.2, (original.2.2, next.2)))
  let prepared := state.mapClassical update
  let final := body.execute environment Reference prepared
  let wrap := fun entry : Store ctx ×
      (services.HiddenState × ((History × preparation.Path) × body.Path)) =>
    (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2))))
  have execution : (preparation.seq body).execute environment Reference state =
      final.mapClassical wrap := by
    rw [Circuit.execute_seq, prefixActual]
    exact ExecutionState.executionState_mapClassical_congr final rfl
  refine (congrArg (fun output : State ctx Reference
    (services.HiddenState × (History × (preparation.seq body).Path)) =>
      (output.block result).matrix) execution).trans ?_
  have remapped := mapClassical_retained_matrix final
    (retainedRecord (services := services) actual.record)
    (fun original outcome => referenceLift Reference (actual.operator original.1 outcome) *
      (prepared.block original).matrix *
        (referenceLift Reference (actual.operator original.1 outcome)).conjTranspose)
    (by
      intro selected
      exact (actual.blocks Reference prepared selected).trans
        (sum_condition_decisions _ _ _ _)) wrap result
  refine remapped.trans ?_
  refine (retained_blocks_push state update
    (fun original outcome => wrap (retainedRecord (services := services)
      actual.record original outcome))
    (fun original outcome => referenceLift Reference (actual.operator original.1 outcome))
    result).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  have sameRecord : wrap (retainedRecord (services := services) actual.record
      (update original) outcome) =
      sourceRecordedPrefixRecord prefixRecord actual.record original outcome := rfl
  rw [sameRecord]
  by_cases selected : sourceRecordedPrefixRecord prefixRecord actual.record
      original outcome = result
  · rw [if_pos selected, if_pos selected]
  · rw [if_neg selected, if_neg selected]

/-- The component's actual returned service state and real Path retain the incoming History. -/
@[expose] public def sourceFullRetainedRecord {Path : Type}
    (record : Store ctx × services.HiddenState → Outcome →
      (Store ctx × services.HiddenState) × Path)
    {History : Type} (original : Store ctx × (services.HiddenState × History))
    (outcome : Outcome) : Store ctx × (services.HiddenState × (History × Path)) :=
  let next := record (original.1, original.2.1) outcome
  (next.1.1, (next.1.2, (original.2.2, next.2)))

/-- The literal workspace push and pop around a child's full Store and service-state record. -/
def sourceWorkspaceRecord (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {Path : Type}
    (record : Store (ctx.addWorkspace key shape fresh) × services.HiddenState → Outcome →
      (Store (ctx.addWorkspace key shape fresh) × services.HiddenState) × Path)
    (original : Store ctx × services.HiddenState) (outcome : Outcome) :
    (Store ctx × services.HiddenState) × Path :=
  let next := record (original.1.pushWorkspace key shape fresh, original.2) outcome
  ((Store.popWorkspace key shape fresh next.1.1, next.1.2), next.2)

/-- The actual workspace lifts full child blocks without assuming service-state independence. -/
lemma sourceWorkspace_recorded_blocks
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (code : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true)
    (record : Store (ctx.addWorkspace key shape fresh) × services.HiddenState → Outcome →
      (Store (ctx.addWorkspace key shape fresh) × services.HiddenState) × code.Path)
    (operators : Store (ctx.addWorkspace key shape fresh) × services.HiddenState → Outcome →
      HilbertOperator (ctx.addWorkspace key shape fresh).register)
    (actual : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) Reference (services.HiddenState × History))
      result, ((code.execute environment Reference state).block result).matrix =
        ∑ original : Store (ctx.addWorkspace key shape fresh) × (services.HiddenState × History),
          ∑ outcome : Outcome,
            if sourceFullRetainedRecord record original outcome = result then
              referenceLift Reference
                (operators (original.1, original.2.1) outcome) *
                (state.block original).matrix *
                  (referenceLift Reference
                    (operators (original.1, original.2.1) outcome)).conjTranspose else 0)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × code.Path))) :
    (((Circuit.workspace (model := .quantum gates oracles operations services)
      ctx key shape fresh code).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        if sourceFullRetainedRecord (sourceWorkspaceRecord key shape fresh record)
            original outcome = result then
          referenceLift (Local := ctx.register) Reference
              (operators (original.1.pushWorkspace key shape fresh, original.2.1) outcome) *
            (state.block original).matrix *
              (referenceLift (Local := ctx.register) Reference
                (operators (original.1.pushWorkspace key shape fresh,
                  original.2.1) outcome)).conjTranspose else 0 := by
  let pushed := state.pushWorkspace key shape fresh
  let finished := code.execute environment Reference pushed
  let pop := fun entry : Store (ctx.addWorkspace key shape fresh) ×
      (services.HiddenState × (History × code.Path)) =>
    (Store.popWorkspace key shape fresh entry.1, entry.2)
  have execution : (Circuit.workspace
      (model := .quantum gates oracles operations services)
      ctx key shape fresh code).execute environment Reference state =
        finished.mapClassical pop := by
    rw [Circuit.execute_workspace]
    exact (State.state_popWorkspace_as_mapClassical key shape fresh Reference finished).trans
      (ExecutionState.executionState_mapClassical_congr finished rfl)
  refine (congrArg (fun output : State ctx Reference
    (services.HiddenState × (History × code.Path)) => (output.block result).matrix)
      execution).trans ?_
  have remapped := mapClassical_retained_matrix finished (sourceFullRetainedRecord record)
    (fun original outcome =>
      referenceLift Reference
        (operators (original.1, original.2.1) outcome) *
        (pushed.block original).matrix *
          (referenceLift Reference
            (operators (original.1, original.2.1) outcome)).conjTranspose)
    (by
      intro selected
      exact (actual Reference pushed selected).trans
        (sum_condition_decisions _ _ _ _)) pop result
  refine remapped.trans ?_
  have pushedMap : (pushed : ExecutionState
      (Store (ctx.addWorkspace key shape fresh) × (services.HiddenState × History))
      (ctx.register.prod Reference)) =
    state.mapClassical (fun entry => (entry.1.pushWorkspace key shape fresh, entry.2)) :=
    (State.state_pushWorkspace_as_mapClassical key shape fresh Reference state).trans
      (ExecutionState.executionState_mapClassical_congr state rfl)
  rw [pushedMap]
  exact retained_blocks_push state
    (fun entry => (entry.1.pushWorkspace key shape fresh, entry.2))
    (fun entry outcome => pop (sourceFullRetainedRecord record entry outcome))
    (fun entry outcome => referenceLift (Local := ctx.register) Reference
      (operators (entry.1, entry.2.1) outcome)) result

/-- An internal exact block certificate permitting the actual returned service state to change. -/
public structure RecordedInstrument
    (code : Circuit (.quantum gates oracles operations services) ctx ctx true)
    (Outcome : Type) [Fintype Outcome]
    (environment : (ExecutionModel.quantum gates oracles operations
      services).Environment) where
  /-- The actual returned Store, service state and Path for each original complete record. -/
  record : Store ctx × services.HiddenState → Outcome →
    (Store ctx × services.HiddenState) × code.Path
  /-- The local Kraus matrix may read both the original Store and hidden service state. -/
  operator : Store ctx × services.HiddenState → Outcome → HilbertOperator ctx.register
  /-- The complete actual block equation retains every service state and incoming history. -/
  blocks : ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × code.Path))),
    ((code.execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        if sourceFullRetainedRecord record original outcome = result then
          referenceLift Reference (operator (original.1, original.2.1) outcome) *
            (state.block original).matrix *
              (referenceLift Reference (operator (original.1, original.2.1) outcome)).conjTranspose
        else 0

/-- A hidden-state-preserving actual instrument supplies the more general internal certificate. -/
public def Instrument.recorded {code : Circuit
    (.quantum gates oracles operations services) ctx ctx true}
    (actual : Instrument code Outcome environment) :
    RecordedInstrument code Outcome environment where
  record original outcome :=
    let next := actual.record original.1 outcome
    ((next.1, original.2), next.2)
  operator original outcome := actual.operator original.1 outcome
  blocks := by
    intro Reference History _ state result
    exact (actual.blocks Reference state result).trans (sum_condition_decisions _ _ _ _)

/-- The real deterministic preparation feeds its returned Store and service state into the body. -/
public def Instrument.recordedPrefix
    (prefixRecord : Store ctx × services.HiddenState →
      (Store ctx × services.HiddenState) × preparation.Path)
    (prefixActual : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      preparation.execute environment Reference state = state.mapClassical (fun original =>
        let next := prefixRecord (original.1, original.2.1)
        (next.1.1, (next.1.2, (original.2.2, next.2)))))
    (actual : Instrument body Outcome environment) :
    RecordedInstrument (preparation.seq body) Outcome environment where
  record original outcome :=
    let first := prefixRecord original
    let last := actual.record first.1.1 outcome
    ((last.1, first.1.2), (first.2, last.2))
  operator original outcome := actual.operator (prefixRecord original).1.1 outcome
  blocks := by
    intro Reference History _ state result
    exact sourceRecordedPrefix_blocks prefixRecord prefixActual actual Reference state result

/-- The same actual lexical workspace retains the complete child record and every operator. -/
public def RecordedInstrument.workspace (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {code : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true}
    (actual : RecordedInstrument code Outcome environment) :
    RecordedInstrument (Circuit.workspace
      (model := .quantum gates oracles operations services)
      ctx key shape fresh code) Outcome environment where
  record := sourceWorkspaceRecord key shape fresh actual.record
  operator original outcome :=
    actual.operator (original.1.pushWorkspace key shape fresh, original.2) outcome
  blocks := by
    intro Reference History _ state result
    exact sourceWorkspace_recorded_blocks key shape fresh code actual.record actual.operator
      actual.blocks Reference state result

end

end QuantumAlg.Execution
