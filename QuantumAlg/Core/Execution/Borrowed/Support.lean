/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Supported borrowed values of the actual complete execution

A positive classical block remains positive in the finite fiber containing
its borrowed value. Joint borrowed restoration therefore supplies an actual
positive initial block with that same value, including arbitrary histories
and external references. No independently supplied support witness is used.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- A mapped block is positive exactly when one of its actual input blocks is positive. -/
theorem mapClassical_block_mass_pos_iff {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (update : C → D) (value : D) :
    0 < ((state.mapClassical update).block value).mass ↔
      ∃ original, update original = value ∧ 0 < (state.block original).mass := by
  rw [mapClassical_block_mass]
  have nonnegative : ∀ original ∈ (Finset.univ : Finset C),
      0 ≤ if update original = value then (state.block original).mass else 0 := by
    intro original _
    split
    · exact (state.block original).mass_nonneg
    · exact le_rfl
  rw [Finset.sum_pos_iff_of_nonneg nonnegative]
  constructor
  · rintro ⟨original, _member, positive⟩
    by_cases same : update original = value
    · exact ⟨original, same, by simpa only [same, if_true] using positive⟩
    · simp only [same, if_false, lt_self_iff_false] at positive
  · rintro ⟨original, same, positive⟩
    exact ⟨original, Finset.mem_univ _, by simpa only [same, if_true] using positive⟩

end ExecutionState

namespace Execution

/-- Recording a deterministic unit path keeps the exact positive classical
block; no enumeration of a concrete runtime store is needed by callers. -/
theorem State.skip_block_mass_pos_iff {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference H) (store : Store ctx) (history : H) :
    0 < ((State.skip state).block (store, (history, ()))).mass ↔
      0 < (state.block (store, history)).mass := by
  have sameState : State.skip state =
      state.mapClassical (fun record => (record.1, (record.2, ()))) := by
    unfold State.skip State.mapHistory
    exact ExecutionState.executionState_mapClassical_congr_decision state
      (fun record => (record.1, (fun previous => (previous, ())) record.2))
      (fun record => (record.1, (record.2, ()))) (by intro; rfl) _ _
  rw [sameState]
  rw [ExecutionState.mapClassical_block_mass_pos_iff]
  constructor
  · rintro ⟨prior, same, positive⟩
    have storeEq : prior.1 = store := congrArg Prod.fst same
    have historyEq : prior.2 = history := congrArg (fun record => record.2.1) same
    cases prior with
    | mk priorStore priorHistory =>
        dsimp only at storeEq historyEq
        subst priorStore
        subst priorHistory
        exact positive
  · intro positive
    exact ⟨(store, history), rfl, positive⟩

/-- The unit history used by a fresh circuit execution is the same state as
`State.skip`, independently of the equality decision used by the caller. -/
theorem OracleInput.enteredState_eq_skip {oracles : ClassicalOracleModel}
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    (input : OracleInput oracles ctx Reference) :
    input.state.mapClassical (fun entry => (entry.1, (entry.2, ()))) =
      State.skip input.state := by
  unfold State.skip State.mapHistory
  exact ExecutionState.executionState_mapClassical_congr_decision input.state
    (fun entry => (entry.1, (entry.2, ())))
    (fun entry => (entry.1, (fun history => (history, ())) entry.2))
    (by intro; rfl) _ _

/-- A positive joint caller/service block gives a positive local caller block
at the very same live store, for any reference extension. -/
theorem OracleInput.caller_local_mass_pos_of_joint {oracles : ClassicalOracleModel}
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    (input : OracleInput oracles ctx Reference)
    (record : Store ctx × oracles.HiddenState)
    (positive : 0 < (input.state.block record).mass) :
    0 < (input.caller.localState.block record.1).mass := by
  rw [Input.localState_block_mass]
  change 0 < ((input.state.mapClassical Prod.fst).block record.1).mass
  exact (ExecutionState.mapClassical_block_mass_pos_iff input.state Prod.fst record.1).mpr
    ⟨record, rfl, positive⟩

/-- An observed borrowed value is supported precisely by positive actual store-history blocks. -/
theorem observeBorrowed_block_mass_pos_iff {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (Reference : Register) {History : Type} [Fintype History]
    (state : ExecutionState (Store ctx × History) (Register.prod ctx.register Reference))
    (value : ctx.borrowedClassicalShape.Value) :
    0 < ((observeBorrowed Reference state).block value).mass ↔
      ∃ original, original.1.readBorrowedClassical = value ∧
        0 < (state.block original).mass := by
  rw [observeBorrowed_block, RuntimeCtx.observeBorrowedWithReference_mass]
  exact ExecutionState.mapClassical_block_mass_pos_iff state _ value

/-- Exact shape and register transport preserves the mass at the corresponding borrowed value. -/
theorem transportBorrowed_block_mass {sourceShape targetShape : CShape}
    {sourceRegister targetRegister : Register} (Reference : Register)
    (sameShape : sourceShape = targetShape) (sameRegister : sourceRegister = targetRegister)
    (state : ExecutionState sourceShape.Value (Register.prod sourceRegister Reference))
    (value : sourceShape.Value) :
    ((transportBorrowed Reference sameShape sameRegister state).block
      ((Equiv.cast (congrArg CShape.Value sameShape)) value)).mass = (state.block value).mass := by
  cases sameShape
  cases sameRegister
  rfl

end Execution

namespace Circuit

/-- Each supported final record has a supported initial record with the same full borrowed value. -/
theorem borrowedRestored_supported_initial {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (Reference : Register)
    {H K : Type} [Fintype H] [Fintype K]
    (initial : ExecutionState (Execution.Store pre × H) (Register.prod pre.register Reference))
    (final : ExecutionState (Execution.Store post × K) (Register.prod post.register Reference))
    (restored : code.BorrowedRestored Reference initial final)
    (record : Execution.Store post × K) (supported : 0 < (final.block record).mass) :
    ∃ original : Execution.Store pre × H,
      0 < (initial.block original).mass ∧
        original.1.readBorrowedClassical =
          code.borrowedClassicalValueTransport record.1.readBorrowedClassical := by
  have observed : 0 < ((Execution.observeBorrowed Reference final).block
      record.1.readBorrowedClassical).mass :=
    (Execution.observeBorrowed_block_mass_pos_iff Reference final _).2
      ⟨record, rfl, supported⟩
  have transport := Execution.transportBorrowed_block_mass Reference
    code.borrowedClassicalShape_preserved code.borrowedRegister_preserved
    (Execution.observeBorrowed Reference final) record.1.readBorrowedClassical
  have prior : 0 < ((Execution.observeBorrowed Reference initial).block
      (code.borrowedClassicalValueTransport record.1.readBorrowedClassical)).mass := by
    rw [← restored]
    exact transport.symm ▸ observed
  obtain ⟨original, same, positive⟩ :=
    (Execution.observeBorrowed_block_mass_pos_iff Reference initial _).1 prior
  exact ⟨original, positive, same⟩

end Circuit

end

end QuantumAlg
