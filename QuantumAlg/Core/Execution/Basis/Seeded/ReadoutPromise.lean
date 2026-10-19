/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Pure full-bank readout from a fixed execution seed

A complete executed state whose every store-reference block is supported on
one fixed bank basis label has a pure local bank at every classical readout.
The proof traces the arbitrary external reference only at the specified local
observation, and keeps zero-mass outcomes without conditional normalization.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History Outcome : Type} [Fintype History] [Fintype Outcome]

/-- A fixed seed in the actual complete state gives the same pure bank after
any finite classical readout and full owned-wire selection. -/
lemma readout_pure_fullSelection (state : State ctx Reference History)
    (seed : ctx.register.Index) (seeded : Holds seed state)
    (read : Store ctx → Outcome) (outcome : Outcome) :
    (StatePromise.pure (NormalizedVector.ket
      (ctx.quantumLayout.restrictSelectedBasis Finset.univ seed))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
        ((state.mapClassical (fun entry => read entry.1)).block outcome)) := by
  let joint := (state.mapClassical (fun entry => read entry.1)).block outcome
  let selection : ctx.register.Index ≃
      (ctx.quantumLayout.selectedRegister Finset.univ).Index := by
    change ctx.quantumLayout.Basis ≃ ctx.quantumLayout.SelectedBasis Finset.univ
    exact ctx.quantumLayout.allSelectedBasisEquiv
  let localState : DensityOperator ctx.quantumLayout.register := joint.marginalLeft
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  have originalDifferent : selection.symm row ≠ seed := by
    intro same
    apply different
    exact (selection.apply_symm_apply row).symm.trans
      (congrArg selection same)
  calc
    (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
        joint).matrix row column =
      (localState.reindex selection).matrix row column :=
        congrArg (fun density : DensityOperator (ctx.quantumLayout.selectedRegister Finset.univ) =>
          density.matrix row column)
          (DensityOperator.observeSelection_all ctx.quantumLayout Reference joint)
    _ = localState.matrix (selection.symm row) (selection.symm column) :=
      DensityOperator.reindex_entry localState selection row column
    _ = ∑ reference : Reference.Index,
          joint.matrix (selection.symm row, reference)
            (selection.symm column, reference) :=
      DensityOperator.marginalLeft_matrix joint _ _
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro reference _
      rw [BasisSeeded.readout_entry seed state seeded read outcome
        (selection.symm row) (selection.symm column) reference reference]
      simp only [originalDifferent, false_and, if_false]

end

end QuantumAlg.Execution.BasisSeeded

namespace QuantumAlg.AlgorithmRun

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A history-polymorphic pure-bank proof for the actual code transfers to
the same run's final stored readout without exposing its path type. -/
lemma pure_fullSelection_of_executionReadout
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape)
    (environment : model.Environment) (seed : post.register.Index)
    (pureExecution : ∀ {Reference : Register} {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History))
      (value : shape.Value),
      (StatePromise.pure (NormalizedVector.ket
        (post.quantumLayout.restrictSelectedBasis Finset.univ seed))).Holds
        (DensityOperator.observeSelection post.quantumLayout Finset.univ Reference
          (((program.code.execute environment Reference state).mapClassical
            (fun entry => program.output.eval entry.1)).block value)))
    {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference)
    (value : shape.Value) :
    (StatePromise.pure (NormalizedVector.ket
      (post.quantumLayout.restrictSelectedBasis Finset.univ seed))).Holds
      (DensityOperator.observeSelection post.quantumLayout Finset.univ Reference
        (((program.finalState environment Reference original.state).mapClassical
          program.output.eval).block value)) := by
  let entered := original.state.mapClassical
    (fun entry => (entry.1, (entry.2, entry.1)))
  have direct := pureExecution entered value
  rw [AlgorithmRun.finalState_readout]
  exact direct

end

end QuantumAlg.AlgorithmRun
