/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Exact records of the existing sequential instruction

The record uses the actual first store, actual second store and chronological
paths. Its interpreter theorem is proved with abstract component path types,
so a caller can compose a large fixed program without elaborating its full
finite path at every composition site. There is no additional interpreter.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Lift a caller-store record through an execution model whose service state is unchanged. -/
@[expose] public def preserveHiddenRecord {Path : Type}
    (record : Store ctx → Store ctx × Path) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × Path
  | (store, hidden) =>
      let result := record store
      ((result.1, hidden), result.2)

/-- Record two actual component updates on their shared intermediate store and service state. -/
@[expose] public def sequenceRecord (first second : Circuit model ctx ctx)
    (firstStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (secondStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (entry : Store ctx × model.HiddenState) :
    (Store ctx × model.HiddenState) × (Circuit.seq first second).Path :=
  let head := firstStep entry
  let tail := secondStep head.1
  (tail.1, (head.2, tail.2))

/-- The actual sequential record returns the second component's real caller store. -/
theorem sequenceRecord_store (first second : Circuit model ctx ctx)
    (firstStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (secondStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (entry : Store ctx × model.HiddenState) :
    (sequenceRecord first second firstStep secondStep entry).1.1 =
      (secondStep (firstStep entry).1).1.1 := rfl

/-- The second component receives the first component's actual next service state. -/
theorem sequenceRecord_hiddenState (first second : Circuit model ctx ctx)
    (firstStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (secondStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (entry : Store ctx × model.HiddenState) :
    (sequenceRecord first second firstStep secondStep entry).1.2 =
      (secondStep (firstStep entry).1).1.2 := rfl

/-- Two proved component equations give the complete record of their existing real sequence. -/
theorem execute_sequenceRecord (first second : Circuit model ctx ctx)
    (firstStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (secondStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      first.execute Reference state = state.mapClassical (fun entry =>
        let result := firstStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.execute Reference state = state.mapClassical (fun entry =>
        let result := secondStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq first second).execute Reference state = state.mapClassical (fun entry =>
      let result := sequenceRecord first second firstStep secondStep (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  refine (execute_seq_mapClassical first second firstStep secondStep
    ?_ ?_ Reference state).trans ?_
  · intro reference history _ input
    exact (firstEquation reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ input
    exact (secondEquation reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Record a sequence of deterministic caller-store updates that leave service state unchanged. -/
@[expose] public def sequenceStoreRecord (first second : Circuit model ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path) (store : Store ctx) :
    Store ctx × (Circuit.seq first second).Path :=
  let head := firstStep store
  let tail := secondStep head.1
  (tail.1, (head.2, tail.2))

/-- The final store of a store-only sequence is the second step on the first result. -/
theorem sequenceStoreRecord_store (first second : Circuit model ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path) (store : Store ctx) :
    (sequenceStoreRecord first second firstStep secondStep store).1 =
      (secondStep (firstStep store).1).1 := rfl

/-- Two store-only component equations compose while retaining the persistent service state. -/
theorem execute_sequenceStoreRecord (first second : Circuit model ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      first.execute Reference state = state.mapClassical (fun entry =>
        let result := firstStep entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.execute Reference state = state.mapClassical (fun entry =>
        let result := secondStep entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq first second).execute Reference state = state.mapClassical (fun entry =>
      let result := sequenceStoreRecord first second firstStep secondStep entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (execute_sequenceRecord first second
    (preserveHiddenRecord (model := model) firstStep)
    (preserveHiddenRecord (model := model) secondStep) ?_ ?_ Reference state).trans ?_
  · intro reference history _ input
    exact (firstEquation reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ input
    exact (secondEquation reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Record the branch selected by the actual caller-store value. -/
@[expose] public def branchStoreRecord {shape : CShape} (input : CInputRef ctx shape)
    (body : shape.Value → Circuit model ctx ctx)
    (step : (value : shape.Value) → Store ctx → Store ctx × (body value).Path)
    (store : Store ctx) : Store ctx × (Circuit.branch input body).Path :=
  let selected := store.read input
  let result := step selected store
  (result.1, ⟨selected, result.2⟩)

/-- Store-only branch equations retain the persistent service state. -/
theorem execute_branchStoreRecord {shape : CShape} (input : CInputRef ctx shape)
    (body : shape.Value → Circuit model ctx ctx)
    (step : (value : shape.Value) → Store ctx → Store ctx × (body value).Path)
    (bodyEquation : ∀ (value : shape.Value) (Reference : Register)
      {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (body value).execute Reference state = state.mapClassical (fun entry =>
        let result := step value entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.branch input body).execute Reference state = state.mapClassical (fun entry =>
      let result := branchStoreRecord input body step entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (execute_branch_mapClassical input body
    (fun value => preserveHiddenRecord (model := model) (step value)) ?_
    Reference state).trans ?_
  · intro value reference history _ current
    exact (bodyEquation value reference current).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Circuit
