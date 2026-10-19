/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Selected-state observation through finite classical grouping

Grouping complete records by a classical readout commutes with observing a
fixed physical subsystem. The proof keeps the complete finite sum and its
probability mass, so an unobserved path cannot be treated as a new pure branch.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {count : Nat} (layout : QuantumLayout count)
  (selection : Finset (Fin count)) (Reference : Register)
  {C D : Type} [Fintype C] [Fintype D]

/-- Observe the same selected physical systems separately in every complete
classical block, preserving each block's trace and the total probability. -/
def observeSelected
    (state : ExecutionState C (Register.prod layout.register Reference)) :
    ExecutionState C (layout.selectedRegister selection) where
  block := fun value => DensityOperator.observeSelection layout selection Reference
    (state.block value)
  total_le_one := by
    simpa only [DensityOperator.observeSelection_mass] using state.total_le_one

/-- Finite classical grouping and subsystem observation give the same density
block, including every hidden outcome and arbitrary external reference. -/
lemma observeSelected_mapClassical
    (state : ExecutionState C (Register.prod layout.register Reference))
    (read : C → D) (result : D) :
    DensityOperator.observeSelection layout selection Reference
      ((state.mapClassical read).block result) =
        ((observeSelected layout selection Reference state).mapClassical read).block
          result := by
  apply DensityOperator.ext
  ext row column
  let f : Reference.Index → layout.ComplementBasis selection → C → ℂ :=
    fun reference complement value =>
      if read value = result then
        (state.block value).matrix
          (layout.joinSelectedBasis selection row complement, reference)
          (layout.joinSelectedBasis selection column complement, reference)
      else 0
  calc
    (DensityOperator.observeSelection layout selection Reference
        ((state.mapClassical read).block result)).matrix row column =
      ∑ reference : Reference.Index, ∑ complement : layout.ComplementBasis selection,
        ∑ value : C, f reference complement value := by
      rw [DensityOperator.observeSelection_entry]
      simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
        Matrix.ite_apply, Matrix.zero_apply, f]
    _ = ∑ value : C, ∑ reference : Reference.Index,
        ∑ complement : layout.ComplementBasis selection,
          f reference complement value := by
      calc
        _ = ∑ reference : Reference.Index, ∑ value : C,
            ∑ complement : layout.ComplementBasis selection,
              f reference complement value := by
          apply Finset.sum_congr rfl
          intro reference _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ value : C, if read value = result then
          (DensityOperator.observeSelection layout selection Reference
            (state.block value)).matrix row column else 0 := by
      apply Finset.sum_congr rfl
      intro value _
      by_cases selected : read value = result
      · simp only [selected, if_true, f,
          DensityOperator.observeSelection_entry]
      · simp only [selected, if_false, f, Finset.sum_const_zero]
    _ = (((observeSelected layout selection Reference state).mapClassical read).block
          result).matrix row column := by
      simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
        Matrix.ite_apply, Matrix.zero_apply, observeSelected]

/-- A single physical pure target survives arbitrary finite grouping of full
classical records, including hidden paths and records of zero probability. -/
lemma mapClassical_pure {R : Register} (state : ExecutionState C R)
    (read : C → D) (target : NormalizedVector R)
    (holds : ∀ entry, (StatePromise.pure target).Holds (state.block entry))
    (result : D) :
    (StatePromise.pure target).Holds ((state.mapClassical read).block result) :=
  state.mapClassical_mixed read (DensityOperator.ofPure target)
    (DensityOperator.ofPure_normalized target) holds result

/-- A branchwise selected pure state is still the same weighted state after
the actual complete records are aggregated by any classical observation. -/
lemma observeSelected_mapClassical_pure
    (state : ExecutionState C (Register.prod layout.register Reference))
    (read : C → D) (target : NormalizedVector (layout.selectedRegister selection))
    (holds : ∀ entry, (StatePromise.pure target).Holds
      (DensityOperator.observeSelection layout selection Reference (state.block entry)))
    (result : D) :
    (StatePromise.pure target).Holds
      (DensityOperator.observeSelection layout selection Reference
        ((state.mapClassical read).block result)) := by
  rw [observeSelected_mapClassical layout selection Reference state read result]
  exact (observeSelected layout selection Reference state).mapClassical_pure read target
    holds result

end

end QuantumAlg.ExecutionState
