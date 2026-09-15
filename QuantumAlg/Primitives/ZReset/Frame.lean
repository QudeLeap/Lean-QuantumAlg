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

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem filter_map {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
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

private theorem filter_applyUnitary {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (operator : C → UnitaryOperator R) (predicate : C → Prop) :
    (state.applyUnitary operator).filterClassical predicate =
      (state.filterClassical predicate).applyUnitary operator := by
  apply ExecutionState.ext
  intro entry
  apply DensityOperator.ext
  by_cases selected : predicate entry <;>
    simp [ExecutionState.filterClassical_block, ExecutionState.applyUnitary_block,
      selected, DensityOperator.applyUnitary_matrix]

private theorem filter_measureZ {C Outcome : Type} [Fintype C] [Fintype Outcome]
    [DecidableEq Outcome] {R : Register} (state : ExecutionState C R)
    (readout : R.Index → Outcome) (predicate : C → Prop) :
    (state.measureZ readout).filterClassical (fun entry => predicate entry.1) =
      (state.filterClassical predicate).measureZ readout := by
  apply ExecutionState.ext
  intro entry
  rcases entry with ⟨source, outcome⟩
  by_cases selected : predicate source <;> simp [selected]

private theorem filter_select {C D : Type} [Fintype C] [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (predicate : C → Prop) (readout : C → D) (value : D) :
    (state.filterClassical predicate).selectClassical readout value =
      (state.selectClassical readout value).filterClassical predicate := by
  apply ExecutionState.ext
  intro entry
  by_cases selected : predicate entry <;> by_cases same : readout entry = value <;>
    simp [ExecutionState.filterClassical_block, ExecutionState.selectClassical_block,
      selected, same]

private theorem filter_mapHistory {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History Later : Type} [Fintype History] [Fintype Later]
    (state : State ctx Reference History) (update : History → Later)
    (predicate : Store ctx → Prop) :
    (state.mapHistory update).filterClassical (fun entry => predicate entry.1) =
      State.mapHistory (state.filterClassical (fun entry => predicate entry.1)) update := by
  simp only [State.mapHistory, filter_map]

private theorem filter_unitary {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (program : UnitaryCircuit ctx.register) (placed : program.physical_idx = ctx.physicalIdx)
    (predicate : Store ctx → Prop) :
    ((Circuit.unitary program placed).execute Reference state).filterClassical
        (fun entry => predicate entry.1) =
      (Circuit.unitary program placed).execute Reference
        (state.filterClassical (fun entry => predicate entry.1)) := by
  simp only [Circuit.execute_unitary, State.unitary, filter_map, filter_applyUnitary]

private theorem filter_seq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (first second : Circuit ctx ctx) (predicate : Store ctx → Prop)
    (firstFrame : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (first.execute Reference state).filterClassical (fun entry => predicate entry.1) =
        first.execute Reference (state.filterClassical (fun entry => predicate entry.1)))
    (secondFrame : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (second.execute Reference state).filterClassical (fun entry => predicate entry.1) =
        second.execute Reference (state.filterClassical (fun entry => predicate entry.1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ((Circuit.seq first second).execute Reference state).filterClassical
        (fun entry => predicate entry.1) =
      (Circuit.seq first second).execute Reference
        (state.filterClassical (fun entry => predicate entry.1)) := by
  rw [Circuit.execute_seq]
  refine (filter_mapHistory (ctx := ctx) (Reference := Reference)
    (History := (History × first.Path) × second.Path)
    (Later := History × (first.Path × second.Path))
    (second.execute Reference (first.execute Reference state))
    (fun history => (history.1.1, (history.1.2, history.2))) predicate).trans ?_
  rw [secondFrame, firstFrame, Circuit.execute_seq]

private theorem filter_branch {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit ctx ctx)
    (predicate : Store ctx → Prop)
    (bodyFrame : ∀ value (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      ((body value).execute Reference state).filterClassical (fun entry => predicate entry.1) =
        (body value).execute Reference (state.filterClassical (fun entry => predicate entry.1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ((Circuit.branch input body).execute Reference state).filterClassical
        (fun entry => predicate entry.1) =
      (Circuit.branch input body).execute Reference
        (state.filterClassical (fun entry => predicate entry.1)) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  simp only [ExecutionState.filterClassical_block, apply_ite DensityOperator.matrix,
    DensityOperator.zero_matrix, Circuit.execute_branch_block_matrix]
  have part (value : shape.Value) :
      (((body value).execute Reference
        ((state.filterClassical (fun entry => predicate entry.1)).selectClassical
          (fun entry => entry.1.read input) value)).mapHistory
            (fun history =>
              (history.1, (⟨value, history.2⟩ : (Circuit.branch input body).Path)))).block result =
      if predicate result.1 then
        ((((body value).execute Reference
          (state.selectClassical (fun entry => entry.1.read input) value)).mapHistory
            (fun history =>
              (history.1, (⟨value, history.2⟩ : (Circuit.branch input body).Path)))).block result)
      else DensityOperator.zero (Register.prod ctx.register Reference) := by
    rw [filter_select, ← bodyFrame, ← filter_mapHistory, ExecutionState.filterClassical_block]
  simp_rw [part]
  by_cases selected : predicate result.1 <;> simp [selected]

/-- Selecting an untouched structural read commutes with the actual write-bearing measurement. -/
private theorem filter_measurement_read {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : output.key ∉ observed.storageKeys) (value : shape.Value)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (State.measureZ state wire output).filterClassical
        (fun entry => entry.1.read observed = value) =
      State.measureZ (state.filterClassical (fun entry => entry.1.read observed = value))
        wire output := by
  simp only [State.measureZ, filter_map]
  simp only [Store.read_write_of_not_mem_storageKeys _ output _ observed separate]
  congr 1
  exact filter_measureZ (C := Store ctx × History)
    (Outcome := Fin (ctx.quantumLayout.wire wire).dimension)
    (R := Register.prod ctx.register Reference) state
    (fun basis => basis.1 wire) (fun entry => entry.1.read observed = value)

/-- Actual reset preserves every complete block selected by a structural read it does not write. -/
theorem zReset_execute_filter_read {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : output.key ∉ observed.storageKeys) (value : shape.Value)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ((circuit wire output).execute Reference state).filterClassical
        (fun entry => entry.1.read observed = value) =
      (circuit wire output).execute Reference
        (state.filterClassical (fun entry => entry.1.read observed = value)) := by
  let body : (CShape.finite (ctx.quantumLayout.wire wire).dimension).Value → Circuit ctx ctx :=
    fun result => .unitary (QuditShift.program ctx.quantumLayout wire (-result.toFin))
      ((QuditShift.quditShift_program_physical_idx ctx.quantumLayout wire (-result.toFin)).trans
        (RuntimeCtx.runtimeCtx_quantumLayout_identities ctx))
  have selectedFrame := filter_branch (.storage output.toCStorageRef) body
    (fun store => store.read observed = value)
    (fun _selected _reference {_history} _historyFinite part =>
      filter_unitary part _ _ (fun store => store.read observed = value))
  exact filter_seq (.measureZ wire output) (.branch (.storage output.toCStorageRef) body)
    (fun store => store.read observed = value)
    (fun reference {_history} _historyFinite initial =>
      filter_measurement_read wire output observed separate value reference initial)
    selectedFrame Reference state

end

end QuantumAlg.ZReset
