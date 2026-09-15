/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Grover's actual complete live space

The n search systems and any selected work suffix survive every Z measurement.
The n finite binary cells and retained n-bit result also remain live. Actual
visited contexts fit totalQubits n k dimension-two systems and 2n classical bits,
with no systems of any other dimension. No workspace is silently released.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

open QuantumAlg.Execution

/-- Closed native capacity formula, independent of every circuit and execution. -/
private def spaceFormula (n k : Nat) : SpacePool .quantum
  | .classicalBits => 2 * n
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then totalQubits n k else 0

private theorem pre_residentSpace : pre.residentSpace = 0 := by
  ext axis
  cases axis <;> rfl

private theorem pre_auxiliarySpace : pre.auxiliarySpace = 0 := rfl

private theorem prepared_residentSpace (n : Nat) :
    (preparedContext n).residentSpace = SpacePool.ofQuantumLayout (runtimeLayout n) := by
  rw [preparedContext, RuntimeCtx.residentSpace_addOwnedLayout, pre_residentSpace, add_zero]

private theorem prepared_auxiliarySpace (n : Nat) :
    (preparedContext n).auxiliarySpace = SpacePool.ofQuantumLayout (runtimeLayout n) := by
  rw [preparedContext, RuntimeCtx.auxiliarySpace_addOwnedLayout, pre_auxiliarySpace, add_zero]

private theorem finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

/-- The complete final resident frame has exactly the independently stated native capacities. -/
theorem post_residentSpace (n k : Nat) : (post n k).residentSpace = spaceFormula n k := by
  rw [post, MeasurementCells.context_residentSpace, resultContext,
    RuntimeCtx.residentSpace_addRetained, prepared_residentSpace]
  ext axis
  cases axis with
  | classicalBits =>
      change n • CShape.bitWidth (.finite 2) + (n + 0) = 2 * n
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change n • 0 + (0 + (runtimeLayout (totalQubits n k)).dimensionCount dimension) = _
      rw [smul_zero, zero_add, zero_add]
      exact (layout (totalQubits n k)).toQuantumLayout_dimensionCount dimension

/-- All newly created entries have owned or retained roles and count toward auxiliary capacity. -/
theorem post_auxiliarySpace (n k : Nat) : (post n k).auxiliarySpace = spaceFormula n k := by
  rw [post, MeasurementCells.context_auxiliarySpace, resultContext,
    RuntimeCtx.auxiliarySpace_addRetained, prepared_auxiliarySpace]
  ext axis
  cases axis with
  | classicalBits =>
      change n • CShape.bitWidth (.finite 2) + (n + 0) = 2 * n
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change n • 0 + (0 + (runtimeLayout (totalQubits n k)).dimensionCount dimension) = _
      rw [smul_zero, zero_add, zero_add]
      exact (layout (totalQubits n k)).toQuantumLayout_dimensionCount dimension

private theorem pre_spaces (n k : Nat) :
    pre.residentSpace ≤ spaceFormula n k ∧ pre.auxiliarySpace ≤ spaceFormula n k := by
  rw [pre_residentSpace, pre_auxiliarySpace]
  exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

private theorem prepared_spaces (n k : Nat) :
    (preparedContext (totalQubits n k)).residentSpace ≤ spaceFormula n k ∧
      (preparedContext (totalQubits n k)).auxiliarySpace ≤ spaceFormula n k := by
  rw [prepared_residentSpace, prepared_auxiliarySpace]
  have bounded : SpacePool.ofQuantumLayout (runtimeLayout (totalQubits n k)) ≤
      spaceFormula n k := by
    intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension =>
        exact le_of_eq
          ((layout (totalQubits n k)).toQuantumLayout_dimensionCount dimension)
  exact ⟨bounded, bounded⟩

private theorem allocated_spaces (n k used : Nat) (bounded : used ≤ n) :
    (MeasurementCells.context (resultContext n k) 2 used).residentSpace ≤ spaceFormula n k ∧
      (MeasurementCells.context (resultContext n k) 2 used).auxiliarySpace ≤ spaceFormula n k := by
  constructor
  · exact (MeasurementCells.context_residentSpace_mono (resultContext n k) 2 bounded).trans_eq
      (post_residentSpace n k)
  · exact (MeasurementCells.context_auxiliarySpace_mono (resultContext n k) 2 bounded).trans_eq
      (post_auxiliarySpace n k)

private theorem visited_spaces {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code marked k).visitedContexts path) :
    frame.residentSpace ≤ spaceFormula n k ∧ frame.auxiliarySpace ≤ spaceFormula n k := by
  change frame ∈
    ([pre, preparedContext (totalQubits n k)] ++
      ([preparedContext (totalQubits n k)] ++
        ([preparedContext (totalQubits n k), resultContext n k] ++
        (MeasurementCells.allocate (resultContext n k) 2 n).visitedContexts path.1.2.2.2))) ++
      ((Circuit.measurementSequence (readouts n k)).visitedContexts path.2.1 ++
        [post n k]) at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at present
  rcases present with ((same | same) | (same | ((same | same) | allocated))) |
    (measured | same)
  · subst frame
    exact pre_spaces n k
  · subst frame
    exact prepared_spaces n k
  · subst frame
    exact prepared_spaces n k
  · subst frame
    exact prepared_spaces n k
  · subst frame
    exact allocated_spaces n k 0 (Nat.zero_le n)
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts
      (resultContext n k) 2 n path.1.2.2.2 frame allocated
    exact allocated_spaces n k used bounded
  · rw [Circuit.measurementSequence_visitedContexts] at measured
    have same := (List.mem_replicate.mp measured).2
    subst frame
    exact allocated_spaces n k n le_rfl
  · subst frame
    exact allocated_spaces n k n le_rfl

/-- Every actual path respects the independent complete resident-space budget. -/
theorem code_residentSpace {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    (code marked k).peakResidentSpace path ≤ spaceFormula n k :=
  Circuit.peakResidentSpace_le_of_visited (code marked k) path (spaceFormula n k)
    (fun frame present => (visited_spaces marked k path frame present).1)

/-- Every actual path respects the independent auxiliary-role budget without releasing storage. -/
theorem code_auxiliarySpace {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    (code marked k).peakAuxiliarySpace path ≤ spaceFormula n k :=
  Circuit.peakAuxiliarySpace_le_of_visited (code marked k) path (spaceFormula n k)
    (fun frame present => (visited_spaces marked k path frame present).2)

end

end QuantumAlg.GroverSearch
