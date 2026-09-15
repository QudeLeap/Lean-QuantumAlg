/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Actual sample space including an existing classical input

The source sampler adds exactly its original phase and target quantum systems,
the individual measurement cells and their packed bits. Every input cell stays
live throughout. Resident and auxiliary budgets separately add the input
context's corresponding capacities, so borrowed cells are not counted as new
workspace. No path releases a measured quantum system.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private theorem finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

def residentBudget (t n : Nat) : SpacePool .quantum := spaceBudget t n + ctx.residentSpace

def auxiliaryBudget (t n : Nat) : SpacePool .quantum := spaceBudget t n + ctx.auxiliarySpace

private theorem prepared_residentSpace (t n : Nat) :
    (preparedContext ctx noQuantum t n).residentSpace =
      SpacePool.ofQuantumLayout (runtimeLayout t n) + ctx.residentSpace :=
  RuntimeCtx.residentSpace_addOwnedLayout ctx ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)

private theorem prepared_auxiliarySpace (t n : Nat) :
    (preparedContext ctx noQuantum t n).auxiliarySpace =
      SpacePool.ofQuantumLayout (runtimeLayout t n) + ctx.auxiliarySpace :=
  RuntimeCtx.auxiliarySpace_addOwnedLayout ctx ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)

/-- The complete retained output includes exactly the input and both real bit representations. -/
theorem post_residentSpace (t n : Nat) :
    (post ctx noQuantum t n).residentSpace = residentBudget ctx t n := by
  rw [post, MeasurementCells.context_residentSpace, resultContext,
    RuntimeCtx.residentSpace_addRetained, prepared_residentSpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + (0 + ctx.residentSpace .classicalBits)) =
        2 * t + ctx.residentSpace .classicalBits
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + ((runtimeLayout t n).dimensionCount dimension +
        ctx.residentSpace (.quantumSystems dimension))) = _
      rw [smul_zero, zero_add, zero_add]
      exact congrArg (fun count => count + ctx.residentSpace (.quantumSystems dimension))
        ((sourceLayout t n).toQuantumLayout_dimensionCount dimension)

/-- The actual output adds only owned and retained capacities to the original auxiliary ledger. -/
theorem post_auxiliarySpace (t n : Nat) :
    (post ctx noQuantum t n).auxiliarySpace = auxiliaryBudget ctx t n := by
  rw [post, MeasurementCells.context_auxiliarySpace, resultContext,
    RuntimeCtx.auxiliarySpace_addRetained, prepared_auxiliarySpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + (0 + ctx.auxiliarySpace .classicalBits)) =
        2 * t + ctx.auxiliarySpace .classicalBits
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + ((runtimeLayout t n).dimensionCount dimension +
        ctx.auxiliarySpace (.quantumSystems dimension))) = _
      rw [smul_zero, zero_add, zero_add]
      exact congrArg (fun count => count + ctx.auxiliarySpace (.quantumSystems dimension))
        ((sourceLayout t n).toQuantumLayout_dimensionCount dimension)

private theorem pre_spaces (t n : Nat) :
    ctx.residentSpace ≤ residentBudget ctx t n ∧
      ctx.auxiliarySpace ≤ auxiliaryBudget ctx t n := by
  constructor <;> intro axis
  · change ctx.residentSpace axis ≤ spaceBudget t n axis + ctx.residentSpace axis
    omega
  · change ctx.auxiliarySpace axis ≤ spaceBudget t n axis + ctx.auxiliarySpace axis
    omega

private theorem prepared_spaces (t n : Nat) :
    (preparedContext ctx noQuantum t n).residentSpace ≤ residentBudget ctx t n ∧
      (preparedContext ctx noQuantum t n).auxiliarySpace ≤ auxiliaryBudget ctx t n := by
  rw [prepared_residentSpace, prepared_auxiliarySpace]
  have bounded : SpacePool.ofQuantumLayout (runtimeLayout t n) ≤ spaceBudget t n := by
    intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension =>
        exact le_of_eq ((sourceLayout t n).toQuantumLayout_dimensionCount dimension)
  exact ⟨fun axis => Nat.add_le_add_right (bounded axis) _,
    fun axis => Nat.add_le_add_right (bounded axis) _⟩

private theorem allocated_spaces (t n used : Nat) (bounded : used ≤ t) :
    (MeasurementCells.context (resultContext ctx noQuantum t n) 2 used).residentSpace ≤
        residentBudget ctx t n ∧
      (MeasurementCells.context (resultContext ctx noQuantum t n) 2 used).auxiliarySpace ≤
        auxiliaryBudget ctx t n := by
  constructor
  · exact (MeasurementCells.context_residentSpace_mono
      (resultContext ctx noQuantum t n) 2 bounded).trans_eq
        (post_residentSpace ctx noQuantum t n)
  · exact (MeasurementCells.context_auxiliarySpace_mono
      (resultContext ctx noQuantum t n) 2 bounded).trans_eq
        (post_auxiliarySpace ctx noQuantum t n)

private theorem visited_spaces {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code ctx noQuantum A).visitedContexts path) :
    frame.residentSpace ≤ residentBudget ctx t n ∧
      frame.auxiliarySpace ≤ auxiliaryBudget ctx t n := by
  change frame ∈
    ([ctx, preparedContext ctx noQuantum t n] ++
      ([preparedContext ctx noQuantum t n] ++
        ([preparedContext ctx noQuantum t n, resultContext ctx noQuantum t n] ++
          (MeasurementCells.allocate
            (resultContext ctx noQuantum t n) 2 t).visitedContexts path.1.2.2.2))) ++
      ((Circuit.measurementSequence (readouts ctx noQuantum t n)).visitedContexts path.2.1 ++
        [post ctx noQuantum t n]) at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with ((same | same) | (same | ((same | same) | allocated))) |
    (measured | same)
  · subst frame
    exact pre_spaces ctx t n
  · subst frame
    exact prepared_spaces ctx noQuantum t n
  · subst frame
    exact prepared_spaces ctx noQuantum t n
  · subst frame
    exact prepared_spaces ctx noQuantum t n
  · subst frame
    exact allocated_spaces ctx noQuantum t n 0 (Nat.zero_le t)
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts
      (resultContext ctx noQuantum t n) 2 t path.1.2.2.2 frame allocated
    exact allocated_spaces ctx noQuantum t n used bounded
  · rw [Circuit.measurementSequence_visitedContexts] at measured
    have same := (List.mem_replicate.mp measured).2
    subst frame
    exact allocated_spaces ctx noQuantum t n t le_rfl
  · subst frame
    exact allocated_spaces ctx noQuantum t n t le_rfl

/-- Every actual path includes the original resident input and all live sampling resources. -/
theorem code_residentSpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) :
    (code ctx noQuantum A).peakResidentSpace path ≤ residentBudget ctx t n :=
  Circuit.peakResidentSpace_le_of_visited (code ctx noQuantum A) path (residentBudget ctx t n)
    (fun frame present => (visited_spaces ctx noQuantum A path frame present).1)

/-- Borrowed input capacity stays separate from the actual added auxiliary capacity. -/
theorem code_auxiliarySpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) :
    (code ctx noQuantum A).peakAuxiliarySpace path ≤ auxiliaryBudget ctx t n :=
  Circuit.peakAuxiliarySpace_le_of_visited (code ctx noQuantum A) path (auxiliaryBudget ctx t n)
    (fun frame present => (visited_spaces ctx noQuantum A path frame present).2)

end

end QuantumAlg.OrderFinding.Sampling.Framed
