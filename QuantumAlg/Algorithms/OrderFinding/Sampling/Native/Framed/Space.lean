/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Space
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Space
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Shape

/-!
# Source-sample storage with an existing classical input

The original classical cells remain live. The framed sample adds exactly its
fresh phase and target qubits, individual measured bits, and packed word.
Resident and auxiliary capacities use separate independent input ledgers.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private theorem runtime_dimensionCount (t n : Nat) (dimension : ℕ+) :
    (Sampling.Native.runtimeLayout t n).dimensionCount dimension =
      if (2 : ℕ+) = dimension then t + n else 0 := by
  change (QuantumLayout.uniform (t + n) 2 Fin.val Fin.val_injective).dimensionCount
    dimension = _
  exact QuantumLayout.dimensionCount_uniform (t + n) 2 dimension
    Fin.val Fin.val_injective

private theorem finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

/-- Independent resident capacity for fresh sample storage and the original input. -/
public def residentBudget (t n : Nat) : SpacePool .quantum :=
  Sampling.Native.spaceBudget t n + ctx.residentSpace

/-- Independent auxiliary capacity keeps borrowed input storage in its original role. -/
public def auxiliaryBudget (t n : Nat) : SpacePool .quantum :=
  Sampling.Native.spaceBudget t n + ctx.auxiliarySpace

private theorem prepared_residentSpace (t n : Nat) :
    (preparedContext ctx noQuantum t n).residentSpace =
      SpacePool.ofQuantumLayout (Sampling.Native.runtimeLayout t n) + ctx.residentSpace :=
  RuntimeCtx.residentSpace_addOwnedLayout ctx ctx.canonicalFreshKey
    (Sampling.Native.runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)

private theorem prepared_auxiliarySpace (t n : Nat) :
    (preparedContext ctx noQuantum t n).auxiliarySpace =
      SpacePool.ofQuantumLayout (Sampling.Native.runtimeLayout t n) + ctx.auxiliarySpace :=
  RuntimeCtx.auxiliarySpace_addOwnedLayout ctx ctx.canonicalFreshKey
    (Sampling.Native.runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)

/-- The complete retained output includes exactly the input and both real bit representations. -/
public theorem post_residentSpace (t n : Nat) :
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
      change t • 0 + (0 + ((Sampling.Native.runtimeLayout t n).dimensionCount dimension +
        ctx.residentSpace (.quantumSystems dimension))) = _
      rw [smul_zero, zero_add, zero_add]
      exact congrArg (fun count => count + ctx.residentSpace (.quantumSystems dimension))
        (runtime_dimensionCount t n dimension)

/-- The actual output adds only owned and retained capacities to the original auxiliary ledger. -/
public theorem post_auxiliarySpace (t n : Nat) :
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
      change t • 0 + (0 + ((Sampling.Native.runtimeLayout t n).dimensionCount dimension +
        ctx.auxiliarySpace (.quantumSystems dimension))) = _
      rw [smul_zero, zero_add, zero_add]
      exact congrArg (fun count => count + ctx.auxiliarySpace (.quantumSystems dimension))
        (runtime_dimensionCount t n dimension)

private theorem pre_spaces (t n : Nat) :
    ctx.residentSpace ≤ residentBudget ctx t n ∧
      ctx.auxiliarySpace ≤ auxiliaryBudget ctx t n := by
  constructor <;> intro axis
  · change ctx.residentSpace axis ≤ Sampling.Native.spaceBudget t n axis + ctx.residentSpace axis
    omega
  · change ctx.auxiliarySpace axis ≤ Sampling.Native.spaceBudget t n axis + ctx.auxiliarySpace axis
    omega

private theorem prepared_spaces (t n : Nat) :
    (preparedContext ctx noQuantum t n).residentSpace ≤ residentBudget ctx t n ∧
      (preparedContext ctx noQuantum t n).auxiliarySpace ≤ auxiliaryBudget ctx t n := by
  rw [prepared_residentSpace, prepared_auxiliarySpace]
  have bounded : SpacePool.ofQuantumLayout (Sampling.Native.runtimeLayout t n) ≤
      Sampling.Native.spaceBudget t n := by
    intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension =>
        exact le_of_eq (runtime_dimensionCount t n dimension)
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
          (show List (RuntimeCtx .quantum) from
            (MeasurementCells.allocate (model := model A)
              (resultContext ctx noQuantum t n) 2 t).visitedContexts path.1.2.2.2)))) ++
      ((show List (RuntimeCtx .quantum) from
        (Circuit.measurementSequence (gates := AlgorithmGate.model)
          (oracles := OrderFinding.Native.sourceModel A) (operations := BitWord.model)
          (classicalOracles := .empty)
          (readouts ctx noQuantum t n)).visitedContexts path.2.1) ++
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
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts (model := model A)
      (resultContext ctx noQuantum t n) 2 t path.1.2.2.2 frame allocated
    exact allocated_spaces ctx noQuantum t n used bounded
  · rw [Circuit.measurementSequence_visitedContexts] at measured
    have same := (List.mem_replicate.mp measured).2
    subst frame
    exact allocated_spaces ctx noQuantum t n t le_rfl
  · subst frame
    exact allocated_spaces ctx noQuantum t n t le_rfl

/-- Every actual path includes the original resident input and all live sampling resources. -/
public theorem code_residentSpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) :
    (code ctx noQuantum A).peakResidentSpace path ≤ residentBudget ctx t n :=
  Circuit.peakResidentSpace_le_of_visited (code ctx noQuantum A) path (residentBudget ctx t n)
    (fun frame present => (visited_spaces ctx noQuantum A path frame present).1)

/-- Borrowed input capacity stays separate from the actual added auxiliary capacity. -/
public theorem code_auxiliarySpace {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) :
    (code ctx noQuantum A).peakAuxiliarySpace path ≤ auxiliaryBudget ctx t n :=
  Circuit.peakAuxiliarySpace_le_of_visited (code ctx noQuantum A) path (auxiliaryBudget ctx t n)
    (fun frame present => (visited_spaces ctx noQuantum A path frame present).2)

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
