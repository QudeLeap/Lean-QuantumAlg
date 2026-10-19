/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Algorithms.SuperdenseCoding.Geometry
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Components.Gates.Construction

/-!
# Native resources of the actual parallel superdense-coding run

Each source block executes at most three single-qubit gates and one CNOT.
The disjoint words run in parallel, so their quantum time is at most four,
including the actual measurement sequence whose canonical quantum duration
is zero. Each of the 2n measurements still occurs in the event ledger.
Original borrowed input and owned result bits both remain live throughout
[dW19, qcnotes.tex:879-890].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution Gate

/-- A source block's independent native upper bound. -/
@[expose] public def blockBudget : ResourcePool model :=
  3 • ResourcePool.singleton (model := model) (.gate .singleQubit) +
    ResourcePool.singleton (model := model) (.gate .cnot)

/-- Independent native upper bound for all real encoding, decoding and measurement events. -/
@[expose] public def eventBudget (count : Nat) : ResourcePool model :=
  count • blockBudget +
    (2 * count) • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+))

/-- All source Bell systems, original message cells and actual measurement cells remain resident. -/
@[expose] public def residentBudget (count : Nat) : SpacePool .quantum
  | .classicalBits => 4 * count
  | .quantumSystems dimension => if dimension = 2 then 2 * count else 0

/-- Only the actual result cells have owned auxiliary roles. -/
@[expose] public def auxiliaryBudget (count : Nat) : SpacePool .quantum
  | .classicalBits => 2 * count
  | .quantumSystems _ => 0

/-- The empty protocol has no quantum work; every nonempty parallel bank takes at most four. -/
@[expose] public def timeBudget (count : Nat) : Nat := if count = 0 then 0 else 4

private lemma selectedGate_cost_le (bit : Bool) (operator : UnitaryOperator (Qubits 1)) :
    (selectedGate bit operator).eventCost ≤
      ResourcePool.singleton (model := model) (.gate .singleQubit) := by
  cases bit with
  | false => exact zero_le
  | true => exact le_refl _

private lemma cnot_cost :
    cnot.eventCost = ResourcePool.singleton (model := model) (.gate .cnot) := by
  rfl

private lemma blockWord_cost_le (first second : Bool) :
    (blockWord first second).eventCost ≤ blockBudget := by
  have encoded := add_le_add (selectedGate_cost_le first XOp) (selectedGate_cost_le second ZOp)
  have whole := add_le_add_right encoded
    (ResourcePool.singleton (model := model) (.gate .cnot) +
      ResourcePool.singleton (model := model) (.gate .singleQubit))
  change _ ≤ _ at whole
  convert whole using 1 <;>
    simp only [blockWord, encodingWord, decodingWord, UnitaryCircuit.seq_eventCost,
      Gate.singleQubitAt_eventCost, cnot_cost, blockBudget, succ_nsmul, zero_nsmul, zero_add] <;>
      ac_rfl

/-- Native events add across actual disjoint words even though time uses maximum. -/
lemma word_cost_le (count : Nat) (bits : SuperdenseMessage count) :
    (word count bits).eventCost ≤ count • blockBudget := by
  induction count with
  | zero => exact le_refl _
  | succ count ih =>
      change ((word count (fun index => bits index.castSucc)).parallelBinary
        (blockWord (bits (Fin.last count)).1 (bits (Fin.last count)).2)).eventCost ≤
        (count + 1) • blockBudget
      rw [UnitaryCircuit.parallelBinary_eventCost, succ_nsmul]
      exact add_le_add (ih _) (blockWord_cost_le _ _)

private lemma blockWord_time_le (first second : Bool) :
    (blockWord first second).evaluatedEventDepth Resource.Event.quantumDuration ≤ 4 := by
  cases first <;> cases second <;> decide

/-- The same native parallel dependency tree establishes the source time limit. -/
lemma word_time_le (count : Nat) (bits : SuperdenseMessage count) :
    (word count bits).evaluatedEventDepth Resource.Event.quantumDuration ≤ timeBudget count := by
  induction count with
  | zero => exact le_refl _
  | succ count ih =>
      change ((word count (fun index => bits index.castSucc)).parallelBinary
        (blockWord (bits (Fin.last count)).1 (bits (Fin.last count)).2)).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 4
      rw [UnitaryCircuit.parallelBinary_evaluatedEventDepth]
      apply max_le
      · exact (ih _).trans (by unfold timeBudget; split <;> omega)
      · exact blockWord_time_le _ _

/-- Every actual path counts all measured wires and its selected native word. -/
public lemma superdense_code_events (count : Nat) (path : (code count).Path) :
    (code count).resourcePool path ≤ eventBudget count := by
  rcases path with ⟨⟨value, _selectedPath⟩, measurementPath⟩
  change ResourcePool.ofList ((selectedWord count value).eventTrace ++
    (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count)).eventTrace measurementPath) ≤ _
  rw [ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change (selectedWord count value).eventCost +
    (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count)).resourcePool measurementPath ≤ _
  have measured :
      (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
          (readouts count)).resourcePool measurementPath =
        width count • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) :=
    QubitReadouts.measurement_resources (allowAllocation := false)
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (services := .empty)
      (position count) (position_dimension count) (resultCell count) measurementPath
  rw [measured]
  change (word count (storedBits value)).eventCost +
    width count • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) ≤ _
  calc
    _ ≤ count • blockBudget +
        width count • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) :=
      add_le_add (word_cost_le count (storedBits value)) (le_refl _)
    _ = eventBudget count := by
      rw [width_eq, Nat.mul_comm count 2]
      rfl

/-- Quantum time follows the actual branch and every subsequent measurement instruction. -/
public lemma superdense_code_time (count : Nat) (path : (code count).Path) :
    (code count).quantumTime path ≤ timeBudget count := by
  change (selectedWord count path.1.1).evaluatedEventDepth Resource.Event.quantumDuration +
    (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count)).quantumTime path.2 ≤ _
  have measured :
      (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
          (readouts count)).quantumTime path.2 = 0 := by
    rw [Circuit.quantumTime, Circuit.measurementSequence_depth]
    simp [Circuit.zEvent]
  rw [measured, Nat.add_zero]
  exact word_time_le count _

private lemma finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

/-- The same live context has exactly 4n classical bits and 2n physical qubits. -/
public lemma superdense_context_resident (count : Nat) :
    (context count).residentSpace = residentBudget count := by
  rw [context, MeasurementCells.context_residentSpace, inputContext,
    RuntimeCtx.residentSpace_addBorrowedInput, quantumContext,
    RuntimeCtx.residentSpace_addSuppliedLayout, RuntimeCtx.residentSpace_empty, add_zero]
  ext axis
  cases axis with
  | classicalBits =>
      change width count * CShape.bitWidth (.finite 2) +
        (count * (CShape.bitWidth (.finite 2) + CShape.bitWidth (.finite 2)) + 0) = 4 * count
      rw [finiteTwo_bits, width_eq]
      omega
  | quantumSystems dimension =>
      change 0 + (0 + (layout count).dimensionCount dimension) = _
      simp only [zero_add]
      have counted := QuantumLayout.dimensionCount_uniform (width count) 2 dimension
        Fin.val Fin.val_injective
      change (layout count).dimensionCount dimension = _ at counted
      rw [counted, width_eq]
      by_cases equal : dimension = 2 <;> simp [residentBudget, equal, eq_comm, Nat.mul_comm]

/-- The original borrowed input and supplied quantum systems add no auxiliary storage. -/
public lemma superdense_context_auxiliary (count : Nat) :
    (context count).auxiliarySpace = auxiliaryBudget count := by
  rw [context, MeasurementCells.context_auxiliarySpace, inputContext,
    RuntimeCtx.auxiliarySpace_addBorrowedInput, quantumContext,
    RuntimeCtx.auxiliarySpace_addSuppliedLayout, RuntimeCtx.auxiliarySpace_empty, add_zero]
  ext axis
  cases axis with
  | classicalBits =>
      change width count * CShape.bitWidth (.finite 2) = 2 * count
      rw [finiteTwo_bits, width_eq]
      omega
  | quantumSystems dimension => rfl

/-- Actual execution keeps precisely the declared complete frame live on every path. -/
public lemma superdense_code_space (count : Nat) (path : (code count).Path) :
    (code count).peakResidentSpace path = residentBudget count ∧
      (code count).peakAuxiliarySpace path = auxiliaryBudget count := by
  constructor
  · exact (Circuit.fixed_peakResidentSpace (code count) path).trans
      (superdense_context_resident count)
  · exact (Circuit.fixed_peakAuxiliarySpace (code count) path).trans
      (superdense_context_auxiliary count)

end
end QuantumAlg.SuperdenseCoding.Execution
