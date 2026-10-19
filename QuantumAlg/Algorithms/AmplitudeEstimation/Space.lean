/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Specification
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Complete actual amplitude-estimation space

The t phase systems, any actual work position, and n source systems remain live after every phase
measurement. The t finite binary cells and the separately packed t-bit
result remain live as well. All visited contexts fit the independently
specified dimension-indexed capacity without releasing any workspace.

-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

private lemma pre_residentSpace : pre.residentSpace = 0 := by
  ext axis
  cases axis <;> rfl

private lemma pre_auxiliarySpace : pre.auxiliarySpace = 0 := rfl

private lemma prepared_residentSpace (t n : Nat) :
    (preparedContext t n).residentSpace = SpacePool.ofQuantumLayout (runtimeLayout t n) := by
  rw [preparedContext, RuntimeCtx.residentSpace_addOwnedLayout, pre_residentSpace, add_zero]

private lemma prepared_auxiliarySpace (t n : Nat) :
    (preparedContext t n).auxiliarySpace = SpacePool.ofQuantumLayout (runtimeLayout t n) := by
  rw [preparedContext, RuntimeCtx.auxiliarySpace_addOwnedLayout, pre_auxiliarySpace, add_zero]

private lemma finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

/-- The complete final resident frame has exactly the independently stated native capacities. -/
lemma post_residentSpace (t n : Nat) : (post t n).residentSpace = spaceBudget t n := by
  rw [post, MeasurementCells.context_residentSpace, resultContext,
    RuntimeCtx.residentSpace_addRetained, prepared_residentSpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + 0) = 2 * t
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + (runtimeLayout t n).dimensionCount dimension) = _
      rw [smul_zero, zero_add, zero_add]
      exact (qpeLayout t (Elementary.helperWidth t n + n)).toQuantumLayout_dimensionCount dimension

/-- All newly created entries have owned or retained roles and count toward auxiliary capacity. -/
lemma post_auxiliarySpace (t n : Nat) : (post t n).auxiliarySpace = spaceBudget t n := by
  rw [post, MeasurementCells.context_auxiliarySpace, resultContext,
    RuntimeCtx.auxiliarySpace_addRetained, prepared_auxiliarySpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + 0) = 2 * t
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + (runtimeLayout t n).dimensionCount dimension) = _
      rw [smul_zero, zero_add, zero_add]
      exact (qpeLayout t (Elementary.helperWidth t n + n)).toQuantumLayout_dimensionCount dimension

private lemma pre_spaces (t n : Nat) :
    pre.residentSpace ≤ spaceBudget t n ∧ pre.auxiliarySpace ≤ spaceBudget t n := by
  rw [pre_residentSpace, pre_auxiliarySpace]
  exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

private lemma prepared_spaces (t n : Nat) :
    (preparedContext t n).residentSpace ≤ spaceBudget t n ∧
      (preparedContext t n).auxiliarySpace ≤ spaceBudget t n := by
  rw [prepared_residentSpace, prepared_auxiliarySpace]
  have bounded : SpacePool.ofQuantumLayout (runtimeLayout t n) ≤ spaceBudget t n := by
    intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension =>
        exact le_of_eq
          ((qpeLayout t (Elementary.helperWidth t n + n)).toQuantumLayout_dimensionCount dimension)
  exact ⟨bounded, bounded⟩

private lemma allocated_spaces (t n used : Nat) (bounded : used ≤ t) :
    (MeasurementCells.context (resultContext t n) 2 used).residentSpace ≤ spaceBudget t n ∧
      (MeasurementCells.context (resultContext t n) 2 used).auxiliarySpace ≤ spaceBudget t n := by
  constructor
  · exact (MeasurementCells.context_residentSpace_mono (resultContext t n) 2 bounded).trans_eq
      (post_residentSpace t n)
  · exact (MeasurementCells.context_auxiliarySpace_mono (resultContext t n) 2 bounded).trans_eq
      (post_auxiliarySpace t n)

private lemma visited_spaces (n : Nat) (t : Nat)
    (path : (code n t).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code n t).visitedContexts path) :
    frame.residentSpace ≤ spaceBudget t n ∧ frame.auxiliarySpace ≤ spaceBudget t n := by
  change frame ∈
    ([pre, preparedContext t n] ++
      ([preparedContext t n] ++ ([preparedContext t n, resultContext t n] ++
        (show List (RuntimeCtx .quantum) from
          (MeasurementCells.allocate (model := model n)
            (resultContext t n) 2 t).visitedContexts path.1.2.2.2)))) ++
      ((show List (RuntimeCtx .quantum) from
        (Circuit.measurementSequence (gates := AlgorithmGate.model)
          (oracles := Elementary.oracles n)
          (operations := BitWord.model) (classicalOracles := .empty)
          (readouts t n)).visitedContexts path.2.1) ++ [post t n]) at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at present
  rcases present with ((same | same) | (same | ((same | same) | allocated))) |
    (measured | same)
  · subst frame
    exact pre_spaces t n
  · subst frame
    exact prepared_spaces t n
  · subst frame
    exact prepared_spaces t n
  · subst frame
    exact prepared_spaces t n
  · subst frame
    exact allocated_spaces t n 0 (Nat.zero_le t)
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts (model := model n)
      (resultContext t n) 2 t path.1.2.2.2 frame allocated
    exact allocated_spaces t n used bounded
  · rw [Circuit.measurementSequence_visitedContexts] at measured
    have same := (List.mem_replicate.mp measured).2
    subst frame
    exact allocated_spaces t n t le_rfl
  · subst frame
    exact allocated_spaces t n t le_rfl

/-- Every actual path respects the independent complete resident-space budget. -/
lemma code_residentSpace (n : Nat) (t : Nat)
    (path : (code n t).Path) :
    (code n t).peakResidentSpace path ≤ spaceBudget t n :=
  Circuit.peakResidentSpace_le_of_visited (code n t) path (spaceBudget t n)
    (fun frame present => (visited_spaces n t path frame present).1)

/-- Every actual path respects the independent auxiliary-role budget without releasing storage. -/
lemma code_auxiliarySpace (n : Nat) (t : Nat)
    (path : (code n t).Path) :
    (code n t).peakAuxiliarySpace path ≤ spaceBudget t n :=
  Circuit.peakAuxiliarySpace_le_of_visited (code n t) path (spaceBudget t n)
    (fun frame present => (visited_spaces n t path frame present).2)

end

end QuantumAlg.AmplitudeEstimation
