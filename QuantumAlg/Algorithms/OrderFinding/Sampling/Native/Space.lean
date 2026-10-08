/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Shape

/-!
# Complete source-sample storage

All phase and target qubits stay live after measurement. The packed result
and the individual measured-bit cells are distinct retained classical storage.
Every visited context is bounded by their independent total capacity.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native

noncomputable section

open QuantumAlg.Execution

/-- Independent resident and auxiliary capacity of the empty-input source sample. -/
public def spaceBudget (t width : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then t + width else 0

private theorem pre_residentSpace : pre.residentSpace = 0 := by
  ext axis
  cases axis <;> rfl

private theorem pre_auxiliarySpace : pre.auxiliarySpace = 0 := rfl

private theorem runtime_dimensionCount (t width : Nat) (dimension : ℕ+) :
    (runtimeLayout t width).dimensionCount dimension =
      if (2 : ℕ+) = dimension then t + width else 0 := by
  change (QuantumLayout.uniform (t + width) 2 Fin.val Fin.val_injective).dimensionCount
    dimension = _
  exact QuantumLayout.dimensionCount_uniform (t + width) 2 dimension
    Fin.val Fin.val_injective

private theorem prepared_residentSpace (t width : Nat) :
    (preparedContext t width).residentSpace =
      SpacePool.ofQuantumLayout (runtimeLayout t width) := by
  rw [preparedContext, RuntimeCtx.residentSpace_addOwnedLayout,
    pre_residentSpace, add_zero]

private theorem prepared_auxiliarySpace (t width : Nat) :
    (preparedContext t width).auxiliarySpace =
      SpacePool.ofQuantumLayout (runtimeLayout t width) := by
  rw [preparedContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    pre_auxiliarySpace, add_zero]

private theorem finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

/-- Final resident storage contains the original qubits and both bit representations. -/
public theorem post_residentSpace (t width : Nat) :
    (post t width).residentSpace = spaceBudget t width := by
  rw [post, MeasurementCells.context_residentSpace, resultContext,
    RuntimeCtx.residentSpace_addRetained, prepared_residentSpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + 0) = 2 * t
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + (runtimeLayout t width).dimensionCount dimension) = _
      rw [smul_zero, zero_add, zero_add]
      exact runtime_dimensionCount t width dimension

/-- Every retained cell and every owned source qubit contributes to auxiliary space. -/
public theorem post_auxiliarySpace (t width : Nat) :
    (post t width).auxiliarySpace = spaceBudget t width := by
  rw [post, MeasurementCells.context_auxiliarySpace, resultContext,
    RuntimeCtx.auxiliarySpace_addRetained, prepared_auxiliarySpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + 0) = 2 * t
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + (runtimeLayout t width).dimensionCount dimension) = _
      rw [smul_zero, zero_add, zero_add]
      exact runtime_dimensionCount t width dimension

private theorem pre_spaces (t width : Nat) :
    pre.residentSpace ≤ spaceBudget t width ∧
      pre.auxiliarySpace ≤ spaceBudget t width := by
  rw [pre_residentSpace, pre_auxiliarySpace]
  exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

private theorem prepared_spaces (t width : Nat) :
    (preparedContext t width).residentSpace ≤ spaceBudget t width ∧
      (preparedContext t width).auxiliarySpace ≤ spaceBudget t width := by
  rw [prepared_residentSpace, prepared_auxiliarySpace]
  have bounded : SpacePool.ofQuantumLayout (runtimeLayout t width) ≤
      spaceBudget t width := by
    intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension => exact le_of_eq (runtime_dimensionCount t width dimension)
  exact ⟨bounded, bounded⟩

private theorem allocated_spaces (t width used : Nat) (bounded : used ≤ t) :
    (MeasurementCells.context (resultContext t width) 2 used).residentSpace ≤
        spaceBudget t width ∧
      (MeasurementCells.context (resultContext t width) 2 used).auxiliarySpace ≤
        spaceBudget t width := by
  constructor
  · exact (MeasurementCells.context_residentSpace_mono
      (resultContext t width) 2 bounded).trans_eq (post_residentSpace t width)
  · exact (MeasurementCells.context_auxiliarySpace_mono
      (resultContext t width) 2 bounded).trans_eq (post_auxiliarySpace t width)

private theorem visited_spaces {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code access).visitedContexts path) :
    frame.residentSpace ≤ spaceBudget t width ∧
      frame.auxiliarySpace ≤ spaceBudget t width := by
  change frame ∈
    ([pre, preparedContext t width] ++
      ([preparedContext t width] ++ ([preparedContext t width, resultContext t width] ++
        (show List (RuntimeCtx .quantum) from
          (MeasurementCells.allocate (model := model access)
            (resultContext t width) 2 t).visitedContexts path.1.2.2.2)))) ++
      ((show List (RuntimeCtx .quantum) from
        (Circuit.measurementSequence (gates := AlgorithmGate.model)
          (oracles := OrderFinding.Native.sourceModel access)
          (operations := BitWord.model) (classicalOracles := .empty)
          (readouts t width)).visitedContexts path.2.1) ++ [post t width]) at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with ((same | same) | (same | ((same | same) | allocated))) |
    (measured | same)
  · subst frame
    exact pre_spaces t width
  · subst frame
    exact prepared_spaces t width
  · subst frame
    exact prepared_spaces t width
  · subst frame
    exact prepared_spaces t width
  · subst frame
    exact allocated_spaces t width 0 (Nat.zero_le t)
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts
      (model := model access) (resultContext t width) 2 t path.1.2.2.2 frame allocated
    exact allocated_spaces t width used bounded
  · rw [Circuit.measurementSequence_visitedContexts] at measured
    have same := (List.mem_replicate.mp measured).2
    subst frame
    exact allocated_spaces t width t le_rfl
  · subst frame
    exact allocated_spaces t width t le_rfl

/-- Every complete path respects the independent resident-space budget. -/
public theorem code_residentSpace {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    (code access).peakResidentSpace path ≤ spaceBudget t width :=
  Circuit.peakResidentSpace_le_of_visited (code access) path (spaceBudget t width)
    (fun frame present => (visited_spaces access path frame present).1)

/-- Every complete path respects the same owned auxiliary-space budget. -/
public theorem code_auxiliarySpace {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    (code access).peakAuxiliarySpace path ≤ spaceBudget t width :=
  Circuit.peakAuxiliarySpace_le_of_visited (code access) path (spaceBudget t width)
    (fun frame present => (visited_spaces access path frame present).2)

end

end QuantumAlg.OrderFinding.Sampling.Native
