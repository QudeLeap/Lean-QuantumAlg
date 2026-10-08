/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Local admission and actual continuation states for native cycles

The internal seed domain observes only the caller's local classical/quantum
state. Positivity lifts that support to every external reference extension and
every hidden service record. Retaining mathematical history does not change it.
The continuation obtains admission from the actual prefix output, with its real
hidden service state; no fresh state or independence premise is substituted.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Locally observable seed support in every complete caller store block. -/
def SeedDomain {kind : ProblemKind} {ctx : RuntimeCtx kind} (seed : ctx.register.Index)
    (state : ExecutionState (Store ctx) ctx.register) : Prop :=
  ∀ (original : Store ctx) (basis : ctx.register.Index), basis ≠ seed →
    (state.block original).matrix basis basis = 0

/-- Every reference extension of the local domain has the same complete store seed support. -/
theorem seeded_input {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (seed : ctx.register.Index) {Reference : Register}
    (input : OracleInput model.classicalOracles ctx Reference)
    (admitted : SeedDomain seed input.caller.localState) :
    BasisSeeded.Holds seed input.state := by
  intro original left right leftRef rightRef
  have blocks : (input.state.filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix =
        (input.caller.state.block original).matrix :=
    (BasisSeeded.store_matrix input.state original).symm
  rw [blocks]
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · rw [if_neg supported]
    by_cases leftSeed : left = seed
    · exact DensityOperator.joint_column_zero_of_marginal_diagonal_zero
        (input.caller.state.block original) right
        (admitted original right (fun same => supported ⟨leftSeed, same⟩))
        rightRef (left, leftRef)
    · exact DensityOperator.joint_row_zero_of_marginal_diagonal_zero
        (input.caller.state.block original) left (admitted original left leftSeed)
        leftRef (right, rightRef)

/-- Relabeling histories while preserving the complete store preserves its seed support. -/
theorem seeded_mapRecord {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (seed : ctx.register.Index) {Reference : Register} {History Later : Type}
    [Fintype History] [Fintype Later]
    (state : State ctx Reference History) (seeded : BasisSeeded.Holds seed state)
    (record : Store ctx × History → Later) :
    BasisSeeded.Holds seed (state.mapClassical (fun entry => (entry.1, record entry))) := by
  let updated := state.mapClassical (fun entry => (entry.1, record entry))
  have same : updated.mapClassical (fun entry => entry.1) =
      state.mapClassical (fun entry => entry.1) := by
    exact ExecutionState.executionState_mapClassical_comp state
      (fun entry => (entry.1, record entry)) (fun entry => entry.1)
  have blocks (original : Store ctx) :
      (updated.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix =
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix :=
    (BasisSeeded.store_matrix updated original).symm.trans
      ((congrArg (fun grouped : ExecutionState (Store ctx)
        (Register.prod ctx.register Reference) => (grouped.block original).matrix) same).trans
          (BasisSeeded.store_matrix state original))
  intro original left right leftRef rightRef
  change (updated.filterClassical _).quantumMarginal.matrix _ _ = _
  rw [blocks]
  exact seeded original left right leftRef rightRef

/-- The actual full-state seed invariant implies the locally observable admission predicate. -/
theorem seedDomain_of_seeded {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (seed : ctx.register.Index) {Reference : Register}
    (input : OracleInput model.classicalOracles ctx Reference)
    (seeded : BasisSeeded.Holds seed input.state) :
    SeedDomain seed input.caller.localState := by
  intro original basis different
  rw [Input.localState_block_entry]
  apply Finset.sum_eq_zero
  intro reference _
  have grouped := congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      matrix (basis, reference) (basis, reference))
    (BasisSeeded.store_matrix input.state original)
  exact grouped.trans ((seeded original basis basis reference reference).trans
    (if_neg (fun same => different same.1)))

/-- Actual prefix outputs satisfy the next seed domain without altering hidden service state. -/
theorem nextInput_seedDomain {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post)
    (seed : post.register.Index) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference)
    (seeded : BasisSeeded.Holds seed (code.execute Reference
      (input.state.mapClassical (fun entry => (entry.1, (entry.2, ())))))) :
    SeedDomain seed (code.nextInput input).caller.localState :=
  seedDomain_of_seeded seed (code.nextInput input)
    (seeded_mapRecord seed _ seeded (fun entry => entry.2.1))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles
