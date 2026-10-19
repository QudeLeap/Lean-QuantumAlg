/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Construction

import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Algorithms.Teleportation.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Components.Gates.Construction

/-!
# Resource bounds for the complete parallel teleportation execution

All triples retain their supplied systems and actual measurement cells. Alice's
native word precedes the measured-feedback correction, while disjoint triples
run in parallel [dW19, qcnotes.tex:790,802,804]. The bounds below belong to that
same complete execution, including the empty bank.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.Resources

noncomputable section

open QuantumAlg.Execution Gate

/-- One original Alice block emits one CNOT and one Hadamard gate. -/
@[expose] public def aliceBudget : ResourcePool model :=
  ResourcePool.singleton (model := model) (.gate .cnot) +
    ResourcePool.singleton (model := model) (.gate .singleQubit)

/-- The actual stored pair selects at most two native one-qubit corrections. -/
@[expose] public def correctionBudget : ResourcePool model :=
  2 • ResourcePool.singleton (model := model) (.gate .singleQubit)

/-- Independent limit: n CNOTs, at most 3n one-qubit gates, and 2n actual measurements. -/
@[expose] public def eventBudget (count : Nat) : ResourcePool model :=
  count • aliceBudget + (count * 2) • ResourcePool.singleton (model := model) (.gate .singleQubit) +
    (count * 2) • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+))

/-- All supplied quantum systems and actual result cells stay live. -/
@[expose] public def residentBudget (count : Nat) : SpacePool .quantum
  | .classicalBits => 2 * count
  | .quantumSystems dimension => if dimension = 2 then 3 * count else 0

/-- Supplied quantum systems are excluded; the real retained result cells are auxiliary. -/
@[expose] public def auxiliaryBudget (count : Nat) : SpacePool .quantum
  | .classicalBits => 2 * count
  | .quantumSystems _ => 0

private lemma block_alice_events : Block.aliceWord.eventCost = aliceBudget := by
  let first := UnitaryCircuit.onBinaryPrefix 1 Block.aliceCnot
  let second := Gate.singleQubitAt Block.layout .empty HOp 0 rfl
  calc
    _ = first.eventCost + second.eventCost := UnitaryCircuit.seq_eventCost first second
    _ = Block.aliceCnot.eventCost + second.eventCost :=
      congrArg (fun value => value + second.eventCost)
        (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost 1 Block.aliceCnot)
    _ = aliceBudget := by rfl

private lemma selected_last_events (bit : Bool) (operator : UnitaryOperator (Qubits 1)) :
    (if bit then Gate.singleQubitAt Block.layout .empty operator 2 rfl
      else UnitaryCircuit.identity AlgorithmGate.model .empty Block.layout).eventCost ≤
        ResourcePool.singleton (model := model) (.gate .singleQubit) := by
  cases bit with
  | false => exact zero_le
  | true => exact le_refl _

private lemma block_correction_events (first second : Bool) :
    (Block.correctionWord first second).eventCost ≤ correctionBudget := by
  let firstWord := if second then Gate.singleQubitAt Block.layout .empty XOp 2 rfl
    else UnitaryCircuit.identity AlgorithmGate.model .empty Block.layout
  let secondWord := if first then Gate.singleQubitAt Block.layout .empty ZOp 2 rfl
    else UnitaryCircuit.identity AlgorithmGate.model .empty Block.layout
  calc
    _ = firstWord.eventCost + secondWord.eventCost :=
      UnitaryCircuit.seq_eventCost firstWord secondWord
    _ ≤ ResourcePool.singleton (model := model) (.gate .singleQubit) +
        ResourcePool.singleton (model := model) (.gate .singleQubit) :=
      add_le_add (selected_last_events second XOp) (selected_last_events first ZOp)
    _ = correctionBudget := by simp only [correctionBudget, two_nsmul]

lemma aliceWord_events (count : Nat) :
    (aliceWord count).eventCost = count • aliceBudget := by
  induction count with
  | zero => rfl
  | succ count ih =>
      calc
        _ = Block.aliceWord.eventCost + (aliceWord count).eventCost :=
          UnitaryCircuit.parallelBinary_eventCost Block.aliceWord (aliceWord count)
        _ = aliceBudget + count • aliceBudget := congrArg₂ (· + ·) block_alice_events ih
        _ = (count + 1) • aliceBudget := by rw [succ_nsmul, add_comm]

lemma correctionWord_events (count : Nat) (bits : Fin count → Bool × Bool) :
    (correctionWord count bits).eventCost ≤ count • correctionBudget := by
  induction count with
  | zero => exact le_refl _
  | succ count ih =>
      calc
        _ = (Block.correctionWord (bits 0).1 (bits 0).2).eventCost +
            (correctionWord count (fun index => bits index.succ)).eventCost :=
          UnitaryCircuit.parallelBinary_eventCost (Block.correctionWord (bits 0).1 (bits 0).2)
            (correctionWord count (fun index => bits index.succ))
        _ ≤ correctionBudget + count • correctionBudget :=
          add_le_add (block_correction_events _ _) (ih _)
        _ = (count + 1) • correctionBudget := by rw [succ_nsmul, add_comm]

/-- Both upper-bound summands come from the actual word and the actual measurement path. -/
lemma code_events (count : Nat) (path : (code count).Path) :
    (code count).resourcePool path ≤ eventBudget count := by
  change ResourcePool.ofList ((onContext count (aliceWord count)).eventTrace ++
    ((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts count)).eventTrace path.2.1 ++
        (selectedCorrection count path.2.2.1).eventTrace)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change (aliceWord count).eventCost +
    ((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts count)).resourcePool path.2.1 +
        (correctionWord count (storedBits path.2.2.1)).eventCost) ≤ _
  have measured := QubitReadouts.measurement_resources (allowAllocation := false)
    (gates := AlgorithmGate.model) (oracles := .empty) (operations := .empty) (services := .empty)
    (measuredPosition count) (measuredPosition_dimension count) (resultCell count) path.2.1
  have combined := add_le_add (aliceWord_events count).le
    (add_le_add measured.le (correctionWord_events count (storedBits path.2.2.1)))
  refine combined.trans_eq ?_
  change count • aliceBudget +
    ((count * 2) • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) +
      count • correctionBudget) = _
  rw [eventBudget, correctionBudget, ← mul_nsmul]
  ac_rfl

private lemma finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

lemma context_resident (count : Nat) :
    (context count).residentSpace = residentBudget count := by
  rw [context, MeasurementCells.context_residentSpace, quantumContext,
    RuntimeCtx.residentSpace_addSuppliedLayout, RuntimeCtx.residentSpace_empty, add_zero]
  ext axis
  cases axis with
  | classicalBits =>
      change (count * 2) * CShape.bitWidth (.finite 2) + 0 = 2 * count
      rw [finiteTwo_bits]
      omega
  | quantumSystems dimension =>
      change 0 + (layout count).dimensionCount dimension = _
      rw [zero_add]
      have counted := QuantumLayout.dimensionCount_uniform (width count) 2 dimension
        Fin.val Fin.val_injective
      change (layout count).dimensionCount dimension = _ at counted
      rw [counted, width_eq]
      by_cases same : dimension = 2 <;>
        simp [residentBudget, same, eq_comm, Nat.mul_comm]

lemma context_auxiliary (count : Nat) :
    (context count).auxiliarySpace = auxiliaryBudget count := by
  rw [context, MeasurementCells.context_auxiliarySpace, quantumContext,
    RuntimeCtx.auxiliarySpace_addSuppliedLayout, RuntimeCtx.auxiliarySpace_empty, add_zero]
  ext axis
  cases axis with
  | classicalBits =>
      change (count * 2) * CShape.bitWidth (.finite 2) = 2 * count
      rw [finiteTwo_bits]
      omega
  | quantumSystems dimension => rfl

/-- The actual false allocation index determines both exact peaks on every path. -/
lemma code_space (count : Nat) (path : (code count).Path) :
    (code count).peakResidentSpace path = residentBudget count ∧
      (code count).peakAuxiliarySpace path = auxiliaryBudget count :=
  ⟨((code count).fixed_peakResidentSpace path).trans (context_resident count),
    ((code count).fixed_peakAuxiliarySpace path).trans (context_auxiliary count)⟩

/-- The empty bank has no gates; each nonempty bank has two sequential two-layer stages. -/
@[expose] public def timeBudget (count : Nat) : Nat := if count = 0 then 0 else 4


end

end QuantumAlg.QuantumTeleportation.Parallel.Resources
