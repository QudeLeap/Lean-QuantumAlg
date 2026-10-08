/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Scope
import all QuantumAlg.Primitives.ZReset.Frame
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Preserve the complete parent store during scoped bank reset

Every measurement writes the actual lexical head. Popping that head therefore
recovers the same complete parent store before and after each write. Selecting
any parent-store block commutes with the actual reset sequence, including its
real histories and the arbitrary quantum-reference extension. The selector in
this proof is a mathematical block projection, not a circuit operand or a
new execution instruction.
-/

namespace QuantumAlg.ZReset.BankScope

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem measurement_filter_selector {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {α : Type} (selector : Store ctx → α)
    (preserved : ∀ store value, selector (store.write output value) = selector store)
    (value : α) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History)) :
    ((Circuit.measureZ (gates := gates) (oracles := oracles) wire output).execute
      Reference state).filterClassical
        (fun entry => selector entry.1 = value) =
      (Circuit.measureZ (gates := gates) (oracles := oracles) wire output).execute
        Reference (state.filterClassical (fun entry => selector entry.1 = value)) := by
  simp only [Circuit.execute_measureZ, filter_map, preserved]
  congr 1
  exact filter_measureZ (C := Store ctx ×
      ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (Outcome := Fin (ctx.quantumLayout.wire wire).dimension)
    (R := Register.prod ctx.register Reference) state
    (fun basis => basis.1 wire) (fun entry => selector entry.1 = value)

private theorem reset_filter_selector {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    {α : Type} (selector : Store ctx → α)
    (preserved : ∀ store value, selector (store.write output value) = selector store)
    (value : α) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History)) :
    ((ZReset.circuit wire output realizations).execute Reference state).filterClassical
        (fun entry => selector entry.1 = value) =
      (ZReset.circuit wire output realizations).execute Reference
        (state.filterClassical (fun entry => selector entry.1 = value)) := by
  let body : (CShape.finite (ctx.quantumLayout.wire wire).dimension).Value →
      Circuit (.quantum gates oracles) ctx ctx := fun result =>
    .unitary (realizations (-result.toFin)).circuit
  have selected := filter_branch (.storage output.toCStorageRef) body
    (fun store => selector store = value)
    (fun _selected _reference {_history} _historyFinite part =>
      filter_unitary part _ (fun store => selector store = value))
  exact filter_seq (Circuit.measureZ (gates := gates) (oracles := oracles) wire output)
    (.branch (.storage output.toCStorageRef) body)
    (fun store => selector store = value)
    (fun reference {_history} _historyFinite initial =>
      measurement_filter_selector wire output selector preserved value reference initial)
    selected Reference state

private theorem sequence_filter_selector {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum}
    (implementations : ∀ wire,
      QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (readouts : List (ZReadout ctx)) {α : Type} (selector : Store ctx → α)
    (preserved : ∀ item ∈ readouts, ∀ store value,
      selector (store.write item.output value) = selector store)
    (value : α) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History)) :
    ((sequence implementations readouts).execute Reference state).filterClassical
        (fun entry => selector entry.1 = value) =
      (sequence implementations readouts).execute Reference
        (state.filterClassical (fun entry => selector entry.1 = value)) := by
  induction readouts generalizing Reference History with
  | nil =>
      change ((Circuit.id (model := .quantum gates oracles) ctx).execute
          Reference state).filterClassical (fun entry => selector entry.1 = value) =
        (Circuit.id (model := .quantum gates oracles) ctx).execute Reference
          (state.filterClassical (fun entry => selector entry.1 = value))
      rw [Circuit.execute_id, Circuit.execute_id]
      simp only [filter_map]
  | cons head tail ih =>
      exact filter_seq
        (ZReset.circuit head.wire head.output (implementations head.wire))
        (sequence implementations tail)
        (fun store => selector store = value)
        (reset_filter_selector head.wire head.output
          (implementations head.wire) selector (preserved head (.head tail)) value)
        (fun reference {_history} _historyFinite initial =>
          ih (fun item present => preserved item (.tail head present)) reference initial)
        Reference state

/-- Writing the actual scratch key changes no cell of the complete parent store. -/
theorem zResetBankScope_parent_write {ctx : RuntimeCtx .quantum}
    {shape : CShape} (output : CWriteRef (workContext ctx) shape)
    (headKey : output.key = (scratch ctx).key)
    (store : Store (workContext ctx)) (value : shape.Value) :
    Store.popWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh
        (store.write output value) =
      Store.popWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh store := by
  apply Store.store_eq_of_storage_reads
  intro observedShape observed
  exact (Store.read_popWorkspace_underWorkspace _ _ _ _ (.storage observed)).trans
    ((Store.read_write_other store output
      (observed.underWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh)
      value (by
        change output.key ≠ observed.key
        rw [headKey]
        change ctx.canonicalFreshKey ≠ observed.key
        intro same
        exact ctx.canonicalFreshKey_fresh
          (same.symm ▸ List.mem_map_of_mem observed.present))).trans
      (Store.read_popWorkspace_underWorkspace _ _ _ store (.storage observed)).symm)

/-- Every complete parent-store block is preserved by the actual scratch-bearing bank body. -/
theorem zResetBankScope_body_filter_parent {ctx : RuntimeCtx .quantum}
    {oracles : OracleModel}
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (original : Store ctx) (Reference : Register) {History : Type} [Fintype History]
    (state : State (workContext ctx) Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState × History)) :
    ExecutionState.filterClassical
        ((Bank.code (oracles := oracles) (zResetBankScope_work_qubits qubits)
          (scratch ctx)).execute Reference state)
        (fun entry =>
          Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
            ctx.canonicalFreshKey_fresh entry.1 = original) =
      (Bank.code (oracles := oracles) (zResetBankScope_work_qubits qubits)
        (scratch ctx)).execute Reference
        (state.filterClassical (fun entry =>
          Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
            ctx.canonicalFreshKey_fresh entry.1 = original)) :=
  sequence_filter_selector
    (Bank.implementations (oracles := oracles) (zResetBankScope_work_qubits qubits))
    (Bank.readouts (zResetBankScope_work_qubits qubits) (scratch ctx))
    (Store.popWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh)
    (fun item present => zResetBankScope_parent_write item.output
      (Bank.zResetBank_readouts_key _ _ item present)) original Reference state

end

end QuantumAlg.ZReset.BankScope
