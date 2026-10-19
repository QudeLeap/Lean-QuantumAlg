/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Complete actual phase-estimation space

The t phase systems and n source systems remain live after every phase
measurement. The t finite binary cells and the separately packed t-bit
result remain live as well. All visited contexts fit the independently
specified dimension-indexed capacity without releasing any workspace.

-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

private lemma pre_residentSpace (t n : Nat) :
    (pre t n).residentSpace = OwnedBorrowedQubits.space n := by
  simp only [pre, OwnedBorrowedQubits.borrowedContext,
    RuntimeCtx.residentSpace_addBorrowedLayout, RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (OwnedBorrowedQubits.borrowedLayout t n).toQuantumLayout_dimensionCount dimension

private lemma pre_auxiliarySpace (t n : Nat) : (pre t n).auxiliarySpace = 0 := by
  simp only [pre, OwnedBorrowedQubits.borrowedContext,
    RuntimeCtx.auxiliarySpace_addBorrowedLayout, RuntimeCtx.auxiliarySpace_empty]

private lemma prepared_residentSpace (t n : Nat) :
    (preparedContext t n).residentSpace = OwnedBorrowedQubits.space (t + n) :=
  OwnedBorrowedQubits.context_resident t n

private lemma prepared_auxiliarySpace (t n : Nat) :
    (preparedContext t n).auxiliarySpace = OwnedBorrowedQubits.space t :=
  OwnedBorrowedQubits.context_auxiliary t n

private lemma finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

/-- The complete final resident frame has exactly the independently stated native capacities. -/
lemma post_residentSpace (t n : Nat) : (post t n).residentSpace = residentBudget t n := by
  rw [post, MeasurementCells.context_residentSpace, resultContext,
    RuntimeCtx.residentSpace_addRetained, prepared_residentSpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + 0) = 2 * t
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + (OwnedBorrowedQubits.space (t + n)) (.quantumSystems dimension)) = _
      rw [smul_zero, zero_add, zero_add]
      rfl

/-- Only the phase systems and retained classical cells contribute to auxiliary capacity. -/
lemma post_auxiliarySpace (t n : Nat) : (post t n).auxiliarySpace = auxiliaryBudget t := by
  rw [post, MeasurementCells.context_auxiliarySpace, resultContext,
    RuntimeCtx.auxiliarySpace_addRetained, prepared_auxiliarySpace]
  ext axis
  cases axis with
  | classicalBits =>
      change t • CShape.bitWidth (.finite 2) + (t + 0) = 2 * t
      rw [finiteTwo_bits, Nat.nsmul_eq_mul]
      omega
  | quantumSystems dimension =>
      change t • 0 + (0 + (OwnedBorrowedQubits.space t) (.quantumSystems dimension)) = _
      rw [smul_zero, zero_add, zero_add]
      rfl

private lemma pre_spaces (t n : Nat) :
    (pre t n).residentSpace ≤ residentBudget t n ∧
      (pre t n).auxiliarySpace ≤ auxiliaryBudget t := by
  rw [pre_residentSpace, pre_auxiliarySpace]
  constructor
  · intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension =>
        change (if (2 : ℕ+) = dimension then n else 0) ≤
          if (2 : ℕ+) = dimension then t + n else 0
        split <;> omega
  · exact fun _ => Nat.zero_le _

private lemma prepared_spaces (t n : Nat) :
    (preparedContext t n).residentSpace ≤ residentBudget t n ∧
      (preparedContext t n).auxiliarySpace ≤ auxiliaryBudget t := by
  rw [prepared_residentSpace, prepared_auxiliarySpace]
  constructor
  · intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension => exact le_rfl
  · intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems dimension => exact le_rfl

private lemma allocated_spaces (t n used : Nat) (bounded : used ≤ t) :
    (MeasurementCells.context (resultContext t n) 2 used).residentSpace ≤ residentBudget t n ∧
      (MeasurementCells.context (resultContext t n) 2 used).auxiliarySpace ≤ auxiliaryBudget t := by
  constructor
  · exact (MeasurementCells.context_residentSpace_mono (resultContext t n) 2 bounded).trans_eq
      (post_residentSpace t n)
  · exact (MeasurementCells.context_auxiliarySpace_mono (resultContext t n) 2 bounded).trans_eq
      (post_auxiliarySpace t n)

private lemma visited_spaces (n : Nat) (t : Nat)
    (path : (code n t).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code n t).visitedContexts path) :
    frame.residentSpace ≤ residentBudget t n ∧ frame.auxiliarySpace ≤ auxiliaryBudget t := by
  change frame ∈
    ([pre t n, preparedContext t n] ++
      ([preparedContext t n] ++ ([preparedContext t n, resultContext t n] ++
        (show List (RuntimeCtx .quantum) from
          (MeasurementCells.allocate (model := model n)
            (resultContext t n) 2 t).visitedContexts path.1.2.2.2)))) ++
      ((show List (RuntimeCtx .quantum) from
        (Circuit.measurementSequence (gates := AlgorithmGate.model)
          (oracles := UnitarySource.model n true) (operations := BitWord.model)
          (classicalOracles := .empty) (readouts t n)).visitedContexts path.2.1) ++ [post t n])
      at present
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
    (code n t).peakResidentSpace path ≤ residentBudget t n :=
  Circuit.peakResidentSpace_le_of_visited (code n t) path (residentBudget t n)
    (fun frame present => (visited_spaces n t path frame present).1)

/-- Every actual path respects the independent auxiliary-role budget without releasing storage. -/
lemma code_auxiliarySpace (n : Nat) (t : Nat)
    (path : (code n t).Path) :
    (code n t).peakAuxiliarySpace path ≤ auxiliaryBudget t :=
  Circuit.peakAuxiliarySpace_le_of_visited (code n t) path (auxiliaryBudget t)
    (fun frame present => (visited_spaces n t path frame present).2)

end

end QuantumAlg.QuantumPhaseEstimation
