/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Layout

/-!
# One actual Gram-entry refresh

The original separation contract derives each dot-product placement and all
basis and other-entry frames. The output overwrites arbitrary prior contents.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Five selected native instructions compute the Gram entry in place. -/
def entryInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (entry : Entry) : Circuit model ctx ctx :=
  LatticeDotRefresh.refreshInto (model := model) (rowRefs basis (leftRow entry))
    (rowRefs basis (rightRow entry)) (entryRefs refs entry)

/-- The five actual chronological writes of the selected entry. -/
def entryStore (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (entry : Entry) (store : Store ctx) : Store ctx :=
  LatticeDotRefresh.refreshStore (rowRefs basis (leftRow entry))
    (rowRefs basis (rightRow entry)) (entryRefs refs entry) store

/-- The selected instruction path for one actual Gram entry update. -/
def entryStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (entry : Entry) (store : Store ctx) :
    Store ctx × (entryInto (model := model) basis refs entry).Path :=
  LatticeDotRefresh.refreshStep (model := model)
    (rowRefs basis (leftRow entry)) (rowRefs basis (rightRow entry))
    (entryRefs refs entry) store

lemma entryStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (entry : Entry) (store : Store ctx) :
    (entryStep (model := model) basis refs entry store).1 =
      entryStore basis refs entry store :=
  LatticeDotRefresh.refreshStep_store _ _ _ store

/-- The selected Gram entry update keeps service state and external references. -/
lemma entryInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (entry : Entry) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (entryInto (model := model) basis refs entry).execute environment Reference state =
      state.mapClassical (fun record =>
        let actual := entryStep (model := model) basis refs entry record.1
        (actual.1, (record.2.1, (record.2.2, actual.2)))) :=
  LatticeDotRefresh.refreshInto_execute _ _ _ Reference state

private lemma row_avoids (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (separation : Separation basis refs) (row : Row) (cell : MetricCell) :
    metricCellKey refs cell ∉ (writeInput (rowRefs basis row).first).storageKeys ∧
      metricCellKey refs cell ∉ (writeInput (rowRefs basis row).second).storageKeys ∧
      metricCellKey refs cell ∉ (writeInput (rowRefs basis row).third).storageKeys := by
  cases row with
  | first => exact ⟨separation.basisAvoids .firstFirst cell,
      separation.basisAvoids .firstSecond cell, separation.basisAvoids .firstThird cell⟩
  | second => exact ⟨separation.basisAvoids .secondFirst cell,
      separation.basisAvoids .secondSecond cell, separation.basisAvoids .secondThird cell⟩
  | third => exact ⟨separation.basisAvoids .thirdFirst cell,
      separation.basisAvoids .thirdSecond cell, separation.basisAvoids .thirdThird cell⟩

private lemma entry_separation (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (separation : Separation basis refs) (entry : Entry) :
    LatticeDotRefresh.Separation (rowRefs basis (leftRow entry))
      (rowRefs basis (rightRow entry)) (entryRefs refs entry) := by
  have distinct : metricCellKey refs .product ≠ metricCellKey refs (entryCell entry) := by
    intro equal
    have cells := separation.keyInjective equal
    cases entry <;> cases cells
  have accumulatorAvoids : refs.product.key ∉
      (writeInput (metricCellRef refs (entryCell entry))).storageKeys := by
    change metricCellKey refs .product ∉ [metricCellKey refs (entryCell entry)]
    simpa only [List.mem_singleton] using distinct
  have productAvoids : (metricCellRef refs (entryCell entry)).key ∉
      (writeInput refs.product).storageKeys := by
    change metricCellKey refs (entryCell entry) ∉ [metricCellKey refs .product]
    simpa only [List.mem_singleton] using distinct.symm
  have leftProduct := row_avoids basis refs separation (leftRow entry) .product
  have rightProduct := row_avoids basis refs separation (rightRow entry) .product
  have leftOutput := row_avoids basis refs separation (leftRow entry) (entryCell entry)
  have rightOutput := row_avoids basis refs separation (rightRow entry) (entryCell entry)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact ⟨leftProduct.1, rightProduct.1, accumulatorAvoids,
      leftOutput.1, rightOutput.1, productAvoids⟩
  · exact ⟨leftProduct.2.1, rightProduct.2.1, accumulatorAvoids,
      leftOutput.2.1, rightOutput.2.1, productAvoids⟩
  · exact ⟨leftProduct.2.2, rightProduct.2.2, accumulatorAvoids,
      leftOutput.2.2, rightOutput.2.2, productAvoids⟩

/-- One actual Gram refresh preserves all caller reads outside its two written cells. -/
lemma entryInto_callerFrame (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (entry : Entry) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (output : metricCellKey refs (entryCell entry) ∉ other.storageKeys)
    (product : refs.product.key ∉ other.storageKeys) :
    (entryStore basis refs entry store).read other = store.read other :=
  LatticeDotRefresh.refreshInto_callerFrame _ _ _ _ other output product

/-- Every original basis row survives each actual Gram-entry refresh. -/
lemma entryInto_preserves_basis (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (separation : Separation basis refs) (entry : Entry)
    (store : Store ctx) (value : NumberTheory.IntegerBasis3)
    (rep : BasisRawRepresents store basis value) :
    BasisRawRepresents (entryStore basis refs entry store) basis value := by
  intro row
  have output := row_avoids basis refs separation row (entryCell entry)
  have product := row_avoids basis refs separation row .product
  refine ⟨?_, ?_, ?_⟩
  · rw [entryInto_callerFrame _ _ _ _ _ output.1 product.1]
    exact (rep row).1
  · rw [entryInto_callerFrame _ _ _ _ _ output.2.1 product.2.1]
    exact (rep row).2.1
  · rw [entryInto_callerFrame _ _ _ _ _ output.2.2 product.2.2]
    exact (rep row).2.2

/-- The actual selected output represents the original integer Gram entry. -/
lemma entryInto_correct (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (separation : Separation basis refs) (entry : Entry) (store : Store ctx)
    (value : NumberTheory.IntegerBasis3) (rep : BasisRawRepresents store basis value) :
    RawSignedRepresents ((entryStore basis refs entry store).read
      (writeInput (metricCellRef refs (entryCell entry)))) (entryValue value entry) :=
  (LatticeDotRefresh.refreshInto_correct _ _ _ (entry_separation basis refs separation entry)
    store _ _ (rep (leftRow entry)) (rep (rightRow entry))).1

/-- Refreshing one entry preserves every distinct earlier Gram output. -/
lemma entryInto_preserves_entry (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (separation : Separation basis refs) (entry saved : Entry)
    (different : entry ≠ saved) (store : Store ctx) :
    (entryStore basis refs entry store).read (writeInput (metricCellRef refs (entryCell saved))) =
      store.read (writeInput (metricCellRef refs (entryCell saved))) := by
  apply entryInto_callerFrame
  · change metricCellKey refs (entryCell entry) ∉ [metricCellKey refs (entryCell saved)]
    simp only [List.mem_singleton]
    intro equal
    have cells := separation.keyInjective equal
    apply different
    cases entry <;> cases saved <;> cases cells <;> rfl
  · change metricCellKey refs .product ∉ [metricCellKey refs (entryCell saved)]
    simp only [List.mem_singleton]
    intro equal
    have cells := separation.keyInjective equal
    cases saved <;> cases cells

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine
