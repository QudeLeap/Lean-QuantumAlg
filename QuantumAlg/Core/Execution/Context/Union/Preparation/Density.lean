/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Preparation.State

/-!
# Complete density transport for actual framed loading

The physical program allocates zero and executes the supplied loading gates.
Its established local density equation transports beside an arbitrary resident
frame by the full state naturality theorem. The preparation value occurs only
in that mathematical density equation. No new instruction or independence
premise is introduced, and all frame/reference coherences remain present.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

private lemma mapped_marginal {C D : Type} [Fintype C] [Fintype D]
    {R : Register} {decision : DecidableEq D} (state : ExecutionState C R) (f : C → D) :
    (@ExecutionState.mapClassical C D _ _ R decision state f).quantumMarginal =
      state.quantumMarginal :=
  @ExecutionState.mapClassical_quantumMarginal C D _ _ R decision state f

private lemma reindexed_marginal {C : Type} [Fintype C] {R S : Register}
    (state : ExecutionState C R) (basis : R.Index ≃ S.Index) :
    (state.reindex basis).quantumMarginal = state.quantumMarginal.reindex basis := by
  apply DensityOperator.ext
  ext row column
  simp only [ExecutionState.quantumMarginal, Matrix.sum_apply,
    ExecutionState.reindex_block_entry, DensityOperator.reindex_entry]

private lemma reindex_cancel {R S : Register} (basis : R.Index ≃ S.Index)
    (left right : DensityOperator R) (same : left.reindex basis = right.reindex basis) :
    left = right := by
  apply DensityOperator.ext
  ext row column
  have entry := congrArg
    (fun density : DensityOperator S => density.matrix (basis row) (basis column)) same
  simpa only [DensityOperator.reindex_entry, Equiv.symm_apply_apply] using entry

/-- Splitting preserves the entire joint density under its complete reference basis equivalence. -/
lemma contextUnion_splitServiceState_quantumMarginal (ctx frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint ctx frame) {Reference : Register}
    {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State (ctx.disjointUnion frame separate) Reference (Hidden × History)) :
    (splitServiceState ctx frame separate state).quantumMarginal =
      state.quantumMarginal.reindex (referenceBasis ctx frame separate Reference) := by
  rw [splitServiceState, State.mapHistory_quantumMarginal, splitState,
    reindexed_marginal, mapped_marginal]

variable {ctx frame : RuntimeCtx .quantum} {count : Nat}
  (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
  (separate : RuntimeCtx.StorageDisjoint (ctx.addOwnedLayout key layout fresh disjoint) frame)
  {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  (environment : (ExecutionModel.quantum gates oracles operations services).Environment)

/-- A proved local zero-and-gate loading equation holds beside every complete resident frame. -/
lemma prepareFramed_execute_preparedDensity
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    (preparation : BasisPreparation layout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate))
        Reference (services.HiddenState × History))
    (loaded :
      (((Circuit.prepareZero (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) ctx key layout fresh disjoint).seq
          (Circuit.unitary (operations := operations) (classicalOracles := services) load)).execute
            environment (Register.prod frame.register Reference)
            (splitServiceState ctx frame
              (preparation_original_disjoint key layout fresh disjoint separate)
              state)).quantumMarginal =
        preparedDensity key layout fresh disjoint preparation.normalized
          (Register.prod frame.register Reference)
          (splitServiceState ctx frame
            (preparation_original_disjoint key layout fresh disjoint separate)
            state).quantumMarginal) :
    ((prepareFramed key layout fresh disjoint separate
      (operations := operations) (services := services) load).execute
        environment Reference state).quantumMarginal =
      preparedDensity key layout
        (preparation_fresh_union key layout fresh disjoint separate)
        (preparation_wires_union key layout fresh disjoint separate)
        preparation.normalized Reference state.quantumMarginal := by
  let post := ctx.addOwnedLayout key layout fresh disjoint
  let originalSeparate := preparation_original_disjoint key layout fresh disjoint separate
  let localReference := Register.prod frame.register Reference
  let localInput : State ctx localReference
      (services.HiddenState × (Store frame × History)) :=
    splitServiceState ctx frame originalSeparate state
  let localOutput : State post localReference
      (services.HiddenState × ((Store frame × History) × (Unit × Unit))) :=
    (((Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) ctx key layout fresh disjoint).seq
        (Circuit.unitary (operations := operations) (classicalOracles := services) load)).execute
          environment localReference localInput)
  let actualOutput : State (post.disjointUnion frame separate) Reference
      (services.HiddenState × (History × (Unit × Unit))) :=
    (prepareFramed key layout fresh disjoint separate
      (operations := operations) (services := services) load).execute environment Reference state
  let reassociate : (services.HiddenState × ((Store frame × History) × (Unit × Unit))) →
      (services.HiddenState × (Store frame × (History × (Unit × Unit)))) :=
    fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))
  have framed : splitServiceState post frame separate actualOutput =
      localOutput.mapHistory reassociate :=
    prepareFramed_execute key layout fresh disjoint separate load environment state
  have natural : (splitServiceState post frame separate actualOutput).quantumMarginal =
      localOutput.quantumMarginal :=
    (congrArg (fun input : State post localReference
      (services.HiddenState × (Store frame × (History × (Unit × Unit)))) =>
        input.quantumMarginal) framed).trans
      (State.mapHistory_quantumMarginal (ctx := post) (Reference := localReference)
        localOutput reassociate)
  let prepareLocal :=
    preparedDensity key layout fresh disjoint preparation.normalized localReference
  have inputSplit := contextUnion_splitServiceState_quantumMarginal ctx frame
    originalSeparate state
  have outputSplit :=
    contextUnion_splitServiceState_quantumMarginal post frame separate actualOutput
  have transported := congrArg prepareLocal inputSplit
  have specified := prepared_density_naturality key layout fresh disjoint separate
    preparation state.quantumMarginal
  have same := outputSplit.symm.trans
    (natural.trans (loaded.trans (transported.trans specified.symm)))
  exact reindex_cancel (referenceBasis post frame separate Reference)
    actualOutput.quantumMarginal
    (preparedDensity key layout
      (preparation_fresh_union key layout fresh disjoint separate)
      (preparation_wires_union key layout fresh disjoint separate)
      preparation.normalized Reference state.quantumMarginal) same

/-- A fixed local loading equation lifts to every framed quantum-reference density. -/
lemma preparedDensity_frameUnitary_transport
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    (source target : BasisPreparation layout)
    (loaded : ∀ {R : Register}
      (density : DensityOperator (Register.prod ctx.register R)),
      DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (load.matrix environment.quantum) (1 : UnitaryOperator R))
          (preparedDensity key layout fresh disjoint source.normalized R density) =
        preparedDensity key layout fresh disjoint target.normalized R density)
    (Reference : Register)
    (density : DensityOperator (Register.prod
      (ctx.disjointUnion frame
        (preparation_original_disjoint key layout fresh disjoint separate)).register
      Reference)) :
    DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          ((frameUnitary (ctx.addOwnedLayout key layout fresh disjoint) frame separate
            load).matrix environment.quantum) (1 : UnitaryOperator Reference))
        (preparedDensity key layout
          (preparation_fresh_union key layout fresh disjoint separate)
          (preparation_wires_union key layout fresh disjoint separate)
          source.normalized Reference density) =
      preparedDensity key layout
        (preparation_fresh_union key layout fresh disjoint separate)
        (preparation_wires_union key layout fresh disjoint separate)
        target.normalized Reference density := by
  let basis := referenceBasis (ctx.addOwnedLayout key layout fresh disjoint)
    frame separate Reference
  apply reindex_cancel basis
  calc
    _ = DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (load.matrix environment.quantum)
          (1 : UnitaryOperator (Register.prod frame.register Reference)))
        ((preparedDensity key layout
          (preparation_fresh_union key layout fresh disjoint separate)
          (preparation_wires_union key layout fresh disjoint separate)
          source.normalized Reference density).reindex basis) :=
      density_naturality (ctx.addOwnedLayout key layout fresh disjoint)
        frame separate load environment _
    _ = preparedDensity key layout fresh disjoint target.normalized
        (Register.prod frame.register Reference)
        (density.reindex (referenceBasis ctx frame
          (preparation_original_disjoint key layout fresh disjoint separate) Reference)) := by
      rw [prepared_density_naturality key layout fresh disjoint separate source density]
      exact loaded _
    _ = _ := (prepared_density_naturality key layout fresh disjoint separate
      target density).symm

end

end QuantumAlg.Execution.ContextUnion
