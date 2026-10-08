/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Scope.Frame
import all QuantumAlg.Primitives.ZReset.Bank.Semantics
import all QuantumAlg.Primitives.ZReset.Bank.Scope.OperationModel

/-!
# Complete parent-store and reference blocks after scoped reset

The actual lexical entry and exit are the existing store maps. Their matrix
laws compose with the actual measurement, stored selection and correction
sequence. The final register is zero separately for every complete original
store, with that store's entire reference matrix unchanged. No incoming zero
state or independence assumption is introduced.

This internal component resets every physical wire in its context. A caller
that must preserve borrowed quantum systems must place it only around its
actual owned bank; the result is not a borrowed-quantum restoration claim.
-/

namespace QuantumAlg.ZReset.BankScope

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem mapped_filter_marginal {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register} (state : ExecutionState C R) (update : C → D)
    (predicate : D → Prop) :
    ((state.mapClassical update).filterClassical predicate).quantumMarginal =
      (state.filterClassical (fun entry => predicate (update entry))).quantumMarginal :=
  (congrArg ExecutionState.quantumMarginal (filter_map state update predicate)).trans
    (ExecutionState.mapClassical_quantumMarginal _ update)

private theorem pop_filtered_marginal {ctx : RuntimeCtx .quantum}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (workContext ctx) Reference History) (original : Store ctx) :
    (ExecutionState.filterClassical
      (State.popWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh state)
      (fun entry => entry.1 = original)).quantumMarginal =
        (state.filterClassical (fun entry =>
          Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
            ctx.canonicalFreshKey_fresh entry.1 = original)).quantumMarginal := by
  have actual := congrArg (fun result : State ctx Reference History =>
    (result.filterClassical (fun entry => entry.1 = original)).quantumMarginal)
      (State.state_popWorkspace_as_mapClassical ctx.canonicalFreshKey (.finite 2)
        ctx.canonicalFreshKey_fresh Reference state)
  exact actual.trans (mapped_filter_marginal state
    (fun entry => (Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh entry.1, entry.2)) (fun entry => entry.1 = original))

private theorem push_filtered_marginal {ctx : RuntimeCtx .quantum}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx) :
    (ExecutionState.filterClassical
      (state.pushWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh)
      (fun entry =>
        Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
          ctx.canonicalFreshKey_fresh entry.1 = original)).quantumMarginal =
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal := by
  have actual := congrArg
    (fun result : ExecutionState (Store (workContext ctx) × History)
        (Register.prod ctx.register Reference) =>
      (result.filterClassical (fun entry =>
        Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
          ctx.canonicalFreshKey_fresh entry.1 = original)).quantumMarginal)
    (State.state_pushWorkspace_as_mapClassical ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh Reference state)
  exact actual.trans (mapped_filter_marginal state
    (fun entry => (entry.1.pushWorkspace ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh, entry.2))
    (fun entry => Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh entry.1 = original))

/-- Scoped reset produces zero while preserving each complete incoming store-reference block. -/
theorem zResetBankScope_complete_store_entry {ctx : RuntimeCtx .quantum}
    {oracles : OracleModel}
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState × History))
    (original : Store ctx)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    (((code (oracles := oracles) qubits).execute Reference state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 := by
  let allocated : State (workContext ctx) Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState × History) :=
    state.pushWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh
  let body := Bank.code (oracles := oracles) (zResetBankScope_work_qubits qubits)
    (scratch ctx)
  have actual := congrArg
    (fun result : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState ×
        (History × (code (oracles := oracles) qubits).Path)) =>
      (result.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef))
    (Circuit.execute_workspace ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh body Reference state)
  have popped := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef))
    (pop_filtered_marginal Reference (body.execute Reference allocated) original)
  have filtered := congrArg
    (fun result : State (workContext ctx) Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState ×
        (History × body.Path)) =>
      result.quantumMarginal.matrix (left, leftRef) (right, rightRef))
    (zResetBankScope_body_filter_parent (oracles := oracles)
      qubits original Reference allocated)
  refine actual.trans (popped.trans (filtered.trans
    ((Bank.zResetBank_complete_entry (oracles := oracles)
      (zResetBankScope_work_qubits qubits) (scratch ctx)
      (allocated.filterClassical (fun entry =>
        Store.popWorkspace ctx.canonicalFreshKey (.finite 2)
          ctx.canonicalFreshKey_fresh entry.1 = original))
      left right leftRef rightRef).trans ?_)))
  split <;> split
  · exact congrArg (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      ∑ basis : ctx.register.Index, density.matrix (basis, leftRef) (basis, rightRef))
      (push_filtered_marginal Reference state original)
  · rename_i workZero parentNotZero
    exact False.elim (parentNotZero workZero)
  · rename_i workNotZero parentZero
    exact False.elim (workNotZero parentZero)
  · rfl

/-- The complete store-reference reset equation holds under any classical operation grant. -/
theorem zResetBankScope_complete_store_entry_operationModel {ctx : RuntimeCtx .quantum}
    {oracles : OracleModel}
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (operations : ClassicalOpModel)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles operations).HiddenState × History))
    (original : Store ctx)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    (((code (oracles := oracles) qubits operations).execute Reference state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 := by
  have erased := congrArg
    (fun output : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState × History) =>
        (output.filterClassical (fun entry => entry.1 = original)).quantumMarginal)
    (code_execute_operationModel (oracles := oracles) qubits operations state)
  have sameBlocks :
      (((code (oracles := oracles) qubits operations).execute Reference state).filterClassical
        (fun entry => entry.1 = original)).quantumMarginal =
      (((code (oracles := oracles) qubits).execute Reference state).filterClassical
        (fun entry => entry.1 = original)).quantumMarginal := by
    simpa only [State.mapHistory, mapped_filter_marginal] using erased
  exact (congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) sameBlocks).trans
    (zResetBankScope_complete_store_entry (oracles := oracles)
      qubits state original left right leftRef rightRef)

end

end QuantumAlg.ZReset.BankScope
