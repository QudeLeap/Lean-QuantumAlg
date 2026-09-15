/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Measure.Instrument

/-!
# Selected systems under complementary Z measurements

An actual Z measurement outside a selected set preserves the selected
systems jointly with the external reference. Summing its real outcomes
removes the complementary projector, including for off-diagonal selected
and reference entries [dW19, qcnotes.tex:5381,5409,5420]. The interpreter's
Store write and finite path remain part of that same execution.

The borrowed-restoration specialization admits a uniquely valued borrowed
classical interface and arbitrary borrowed quantum systems. It requires
each measured wire to lie outside the actual borrowed selection; neither
separability nor a prescribed result distribution is assumed.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- A complementary Z measurement preserves every selected-reference matrix entry. -/
theorem measureZ_observeSelectionWithReference {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (wire : Fin count) (untouched : wire ∉ selection)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod layout.register Reference)) :
    DensityOperator.observeSelectionWithReference layout selection Reference
      (state.measureZ (fun value => value.1 wire)).quantumMarginal =
    DensityOperator.observeSelectionWithReference layout selection Reference
      state.quantumMarginal := by
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [DensityOperator.observeSelectionWithReference_entry,
    DensityOperator.observeSelectionWithReference_entry]
  apply Finset.sum_congr rfl
  intro complement _
  have leftRead : layout.joinSelectedBasis selection left complement wire =
      complement ⟨wire, Finset.mem_compl.mpr untouched⟩ :=
    layout.joinSelectedBasis_complement_value selection left complement
      ⟨wire, Finset.mem_compl.mpr untouched⟩
  have rightRead : layout.joinSelectedBasis selection right complement wire =
      complement ⟨wire, Finset.mem_compl.mpr untouched⟩ :=
    layout.joinSelectedBasis_complement_value selection right complement
      ⟨wire, Finset.mem_compl.mpr untouched⟩
  change (∑ result : C × Fin (layout.wire wire).dimension,
    (ZMeasurement.branch (R := Register.prod layout.register Reference)
      (fun value => value.1 wire) result.2 (state.block result.1)).matrix)
        (layout.joinSelectedBasis selection left complement, refLeft)
        (layout.joinSelectedBasis selection right complement, refRight) =
    (∑ value : C, (state.block value).matrix)
      (layout.joinSelectedBasis selection left complement, refLeft)
      (layout.joinSelectedBasis selection right complement, refRight)
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, ZMeasurement.branch_matrix,
    leftRead, rightRead, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end ExecutionState

namespace Execution

/-- A uniquely valued borrowed classical observation collects the actual quantum marginal. -/
theorem observeBorrowed_block_of_subsingleton {kind : ProblemKind} {ctx : RuntimeCtx kind}
    [Subsingleton ctx.borrowedClassicalShape.Value] {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference H)
    (value : ctx.borrowedClassicalShape.Value) :
    (observeBorrowed Reference state).block value =
      ctx.observeBorrowedWithReference Reference state.quantumMarginal := by
  rw [observeBorrowed_block]
  apply congrArg (ctx.observeBorrowedWithReference Reference)
  apply DensityOperator.ext
  change (∑ label : Store ctx × H,
    if label.1.readBorrowedClassical = value then (state.block label).matrix else 0) =
      ∑ label : Store ctx × H, (state.block label).matrix
  have sameRead (label : Store ctx × H) : label.1.readBorrowedClassical = value :=
    Subsingleton.elim _ _
  simp only [sameRead, if_true]

end Execution

namespace Circuit

open Execution

/-- The actual classical write and path retain the same selected-reference observation. -/
theorem measurementStep_observeSelectionWithReference {ctx : RuntimeCtx .quantum}
    (selection : Finset (Fin ctx.systemCount)) (item : ZReadout ctx)
    (untouched : item.wire ∉ selection) {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference H) :
    DensityOperator.observeSelectionWithReference ctx.quantumLayout selection Reference
      ((Circuit.measureZ item.wire item.output).execute Reference state).quantumMarginal =
    DensityOperator.observeSelectionWithReference ctx.quantumLayout selection Reference
      state.quantumMarginal := by
  rw [execute_measureZ]
  simp only [State.measureZ, ExecutionState.mapClassical_quantumMarginal]
  exact ExecutionState.measureZ_observeSelectionWithReference ctx.quantumLayout
    selection item.wire untouched state

/-- A finite sequence of complementary measurements preserves the same joint observation. -/
theorem measurementSequence_observeSelectionWithReference {ctx : RuntimeCtx .quantum}
    (selection : Finset (Fin ctx.systemCount)) (readouts : List (ZReadout ctx))
    (untouched : ∀ item ∈ readouts, item.wire ∉ selection)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    DensityOperator.observeSelectionWithReference ctx.quantumLayout selection Reference
      ((measurementSequence readouts).execute Reference state).quantumMarginal =
    DensityOperator.observeSelectionWithReference ctx.quantumLayout selection Reference
      state.quantumMarginal := by
  induction readouts generalizing H with
  | nil =>
      rw [measurementSequence, execute_id, State.skip_quantumMarginal]
  | cons head tail ih =>
      rw [measurementSequence, execute_seq, State.mapHistory_quantumMarginal]
      exact (ih (fun item present => untouched item (.tail head present))
        ((Circuit.measureZ head.wire head.output).execute Reference state)).trans
          (measurementStep_observeSelectionWithReference selection head
            (untouched head (.head tail)) state)

/-- Measuring only complementary wires restores the full borrowed quantum-reference state. -/
theorem borrowedRestored_measurementSequence_complement {ctx : RuntimeCtx .quantum}
    [Subsingleton ctx.borrowedClassicalShape.Value] (readouts : List (ZReadout ctx))
    (untouched : ∀ item ∈ readouts, item.wire ∉ ctx.borrowedSelection)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    (measurementSequence readouts).BorrowedRestored Reference state
      ((measurementSequence readouts).execute Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext]
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block_of_subsingleton, observeBorrowed_block_of_subsingleton]
  exact congrArg
    (fun observed : DensityOperator
        (Register.prod (ctx.quantumLayout.selectedRegister ctx.borrowedSelection) Reference) =>
      observed.reindex (S := Register.prod ctx.borrowedQuantumLayout.register Reference)
        (ctx.borrowedBasisEquiv.prodCongr (Equiv.refl Reference.Index)))
    (measurementSequence_observeSelectionWithReference ctx.borrowedSelection readouts
      untouched state)

end Circuit

end

end QuantumAlg
