/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Classical block preservation under actual reset

The reset writes only its declared finite result cell. Selecting any structural
read outside that cell therefore commutes with the full actual execution,
including its path and external-reference blocks. This permits the reset state
equations to be applied separately to every earlier stored result, rather than
only after summing those results away [dW19, qcnotes.tex:5381,5409,5420].

The private lemmas distribute the existing block selector through the actual
interpreter operations. They define no execution syntax or state transformer.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

variable {services : ClassicalOracleModel}

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma filter_map {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
    {R : Register} (state : ExecutionState C R) (update : C → D) (predicate : D → Prop) :
    (state.mapClassical update).filterClassical predicate =
      (state.filterClassical (fun entry => predicate (update entry))).mapClassical update := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  simp only [ExecutionState.filterClassical_block, ExecutionState.mapClassical,
    apply_ite DensityOperator.matrix, DensityOperator.zero_matrix]
  by_cases selected : predicate result
  · rw [if_pos selected]
    apply Finset.sum_congr rfl
    intro entry _
    by_cases same : update entry = result <;> simp [same, selected]
  · rw [if_neg selected]
    symm
    apply Finset.sum_eq_zero
    intro entry _
    by_cases same : update entry = result <;> simp [same, selected]

private lemma filter_applyUnitary {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (operator : C → UnitaryOperator R) (predicate : C → Prop) :
    (state.applyUnitary operator).filterClassical predicate =
      (state.filterClassical predicate).applyUnitary operator := by
  apply ExecutionState.ext
  intro entry
  apply DensityOperator.ext
  by_cases selected : predicate entry <;>
    simp [ExecutionState.filterClassical_block, ExecutionState.applyUnitary_block,
      selected, DensityOperator.applyUnitary_matrix]

private lemma filter_measureZ {C Outcome : Type} [Fintype C] [Fintype Outcome]
    [DecidableEq Outcome] {R : Register} (state : ExecutionState C R)
    (readout : R.Index → Outcome) (predicate : C → Prop) :
    (state.measureZ readout).filterClassical (fun entry => predicate entry.1) =
      (state.filterClassical predicate).measureZ readout := by
  apply ExecutionState.ext
  intro entry
  rcases entry with ⟨source, outcome⟩
  by_cases selected : predicate source <;> simp [selected]

private lemma filter_select {C D : Type} [Fintype C] [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (predicate : C → Prop) (readout : C → D) (value : D) :
    (state.filterClassical predicate).selectClassical readout value =
      (state.selectClassical readout value).filterClassical predicate := by
  apply ExecutionState.ext
  intro entry
  by_cases selected : predicate entry <;> by_cases same : readout entry = value <;>
    simp [ExecutionState.filterClassical_block, ExecutionState.selectClassical_block,
      selected, same]

private lemma filter_mapHistory {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History Later : Type} [Fintype History] [Fintype Later]
    (state : State ctx Reference History) (update : History → Later)
    (predicate : Store ctx → Prop) :
    (state.mapHistory update).filterClassical (fun entry => predicate entry.1) =
      State.mapHistory (state.filterClassical (fun entry => predicate entry.1)) update := by
  simp only [State.mapHistory, filter_map]

private lemma filter_unitary {allowAllocation : Bool} {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}
    {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (predicate : Store ctx → Prop) :
    ((Circuit.unitary (allowAllocation := allowAllocation)
      (classicalOracles := services) program).execute environment Reference
      state).filterClassical
        (fun entry => predicate entry.1) =
      (Circuit.unitary (allowAllocation := allowAllocation)
        (classicalOracles := services) program).execute environment Reference
        (state.filterClassical (fun entry => predicate entry.1)) := by
  simp only [Circuit.execute_unitary, filter_map, filter_applyUnitary]
  exact ExecutionState.executionState_mapClassical_congr_decision
    _ _ _ (fun _ => rfl) _ _

private lemma filter_seq {allowAllocation : Bool}
    {model : ExecutionModel} {environment : model.Environment}
    {ctx : RuntimeCtx model.kind}
    (first second : Circuit model ctx ctx allowAllocation) (predicate : Store ctx → Prop)
    (firstFrame : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (first.execute environment Reference state).filterClassical (fun entry => predicate entry.1) =
        first.execute
      environment Reference (state.filterClassical (fun entry => predicate entry.1)))
    (secondFrame : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (second.execute
      environment Reference state).filterClassical (fun entry => predicate entry.1) =
        second.execute
      environment Reference (state.filterClassical (fun entry => predicate entry.1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ((Circuit.seq first second).execute environment Reference state).filterClassical
        (fun entry => predicate entry.1) =
      (Circuit.seq first second).execute environment Reference
        (state.filterClassical (fun entry => predicate entry.1)) := by
  rw [Circuit.execute_seq]
  refine (filter_mapHistory (ctx := ctx) (Reference := Reference)
    (History := model.HiddenState × ((History × first.Path) × second.Path))
    (Later := model.HiddenState × (History × (first.Path × second.Path)))
    (second.execute environment Reference (first.execute environment Reference state))
    (fun history =>
      (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) predicate).trans ?_
  rw [secondFrame, firstFrame, Circuit.execute_seq]

private lemma filter_branch {allowAllocation : Bool}
    {model : ExecutionModel} {environment : model.Environment}
    {ctx : RuntimeCtx model.kind}
    {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit model ctx ctx allowAllocation)
    (predicate : Store ctx → Prop)
    (bodyFrame : ∀ value (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      ((body value).execute
      environment Reference state).filterClassical (fun entry => predicate entry.1) =
        (body value).execute
      environment Reference (state.filterClassical (fun entry => predicate entry.1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ((Circuit.branch input body).execute environment Reference state).filterClassical
        (fun entry => predicate entry.1) =
      (Circuit.branch input body).execute environment Reference
        (state.filterClassical (fun entry => predicate entry.1)) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  simp only [ExecutionState.filterClassical_block, apply_ite DensityOperator.matrix,
    DensityOperator.zero_matrix, Circuit.execute_branch_block_matrix]
  have part (value : shape.Value) :
      (((body value).execute environment Reference
        ((state.filterClassical (fun entry => predicate entry.1)).selectClassical
          (fun entry => entry.1.read input) value)).mapHistory
            (fun history =>
              (history.1, (history.2.1,
                (⟨value, history.2.2⟩ : (Circuit.branch input body).Path))))).block result =
      if predicate result.1 then
        ((((body value).execute environment Reference
          (state.selectClassical (fun entry => entry.1.read input) value)).mapHistory
            (fun history =>
              (history.1, (history.2.1,
                (⟨value, history.2.2⟩ : (Circuit.branch input body).Path))))).block result)
      else DensityOperator.zero (Register.prod ctx.register Reference) := by
    rw [filter_select, ← bodyFrame, ← filter_mapHistory, ExecutionState.filterClassical_block]
  simp_rw [part]
  by_cases selected : predicate result.1 <;> simp [selected]

/-- Selecting an untouched structural read commutes with the actual write-bearing measurement. -/
private lemma filter_measurement_read {allowAllocation : Bool}
    {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}
    {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : output.key ∉ observed.storageKeys) (value : shape.Value)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History)) :
    ((Circuit.measureZ (allowAllocation := allowAllocation) (classicalOracles := services)
      (gates := gates) (oracles := oracles) wire
      output).execute environment Reference state).filterClassical
        (fun entry => entry.1.read observed = value) =
      (Circuit.measureZ (allowAllocation := allowAllocation) (classicalOracles := services)
        (gates := gates) (oracles := oracles) wire
        output).execute
      environment Reference
        (state.filterClassical (fun entry => entry.1.read observed = value)) := by
  simp only [Circuit.execute_measureZ, filter_map]
  simp only [Store.read_write_of_not_mem_storageKeys _ output _ observed separate]
  congr 1
  exact filter_measureZ (C := Store ctx ×
      ((ExecutionModel.quantum gates oracles .empty services).HiddenState × History))
    (Outcome := Fin (ctx.quantumLayout.wire wire).dimension)
    (R := Register.prod ctx.register Reference) state
    (fun basis => basis.1 wire) (fun entry => entry.1.read observed = value)

/-- Actual reset preserves every complete block selected by a structural read it does not write. -/
lemma zReset_execute_filter_read {allowAllocation : Bool}
    {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}
    {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : output.key ∉ observed.storageKeys) (value : shape.Value)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History)) :
    ((circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations).execute environment Reference
      state).filterClassical
        (fun entry => entry.1.read observed = value) =
      (circuit (allowAllocation := allowAllocation) (services := services) wire output
          realizations).execute environment Reference
        (state.filterClassical (fun entry => entry.1.read observed = value)) := by
  let body : (CShape.finite (ctx.quantumLayout.wire wire).dimension).Value →
      Circuit (.quantum gates oracles .empty services) ctx ctx allowAllocation :=
    fun result => .unitary (realizations (-result.toFin)).circuit
  have selectedFrame := filter_branch (environment := environment)
    (allowAllocation := allowAllocation) (.storage
      output.toCStorageRef) body
    (fun store => store.read observed = value)
    (fun _selected _reference {_history} _historyFinite part =>
      filter_unitary (allowAllocation := allowAllocation) part _ (fun store => store.read observed =
          value))
  exact filter_seq (allowAllocation := allowAllocation)
    (Circuit.measureZ (allowAllocation := allowAllocation)
      (classicalOracles := services) (gates := gates) (oracles := oracles) wire output)
    (.branch (.storage output.toCStorageRef) body)
    (fun store => store.read observed = value)
    (fun reference {_history} _historyFinite initial =>
      filter_measurement_read (allowAllocation := allowAllocation) wire output observed separate
          value reference initial)
    selectedFrame Reference state

end

end QuantumAlg.ZReset
