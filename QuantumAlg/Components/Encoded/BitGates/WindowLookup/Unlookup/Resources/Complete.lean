/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Resources.Measurement
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Count
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Ledger

/-!
# Complete actual measurement-unlookup resources

The complete existing circuit pays its physical H/MZ/reset, one native
mask-packing instruction, both unary traversals and every retained parity
row and feedback gate. Bounds concern all actual paths of that same circuit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (output : Fin resultWidth → CWriteRef ctx (.finite 2))
  (mask : CWriteRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))

/-- The original physical reset and actual paid-restoration tail retain their complete pools. -/
lemma circuit_resourcePool
    (path : (frame.circuit (services := services)
      physical sameWires output mask parity table).Path) :
    (frame.circuit physical sameWires output mask parity table).resourcePool path =
      (measuredResetWordCircuit physical sameWires frame.result frame.resultDistinct
        output mask).resourcePool path.1 +
      (frame.restorationCircuit physical sameWires (.storage mask.toCStorageRef)
        parity table).resourcePool path.2 := by
  dsimp only [circuit, Circuit.Path] at path
  change ResourcePool.ofList (_ ++ _) = _
  rw [ResourcePool.ofList_append]
  rfl

/-- All actual high-selector and reused-unary Toffolis are included. -/
lemma circuit_toffoli_count_le
    (path : (frame.circuit (services := services)
      physical sameWires output mask parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      ((frame.circuit physical sameWires output mask parity table).resourcePool path) ≤
        2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4) := by
  have first := measuredResetWordCircuit_gate_count_le (oracles := .empty)
    (services := services) physical sameWires frame.result frame.resultDistinct output mask
    .toffoli path.1
  have last := frame.restorationCircuit_toffoli_count_le physical sameWires
    (.storage mask.toCStorageRef) parity table path.2
  rw [frame.circuit_resourcePool physical sameWires output mask parity table,
    ResourcePool.count_add]
  simp only [reduceCtorEq, ↓reduceIte] at first
  omega

/-- Every original unary cleanup and paid phase fan-in/inverse CNOT remains charged. -/
lemma circuit_cnot_count_le
    (path : (frame.circuit (services := services)
      physical sameWires output mask parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((frame.circuit physical sameWires output mask parity table).resourcePool path) ≤
        2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) * 2 ^ lowWidth - 2) := by
  have first := measuredResetWordCircuit_gate_count_le (oracles := .empty)
    (services := services) physical sameWires frame.result frame.resultDistinct output mask
    .cnot path.1
  have last := frame.restorationCircuit_cnot_count_le physical sameWires
    (.storage mask.toCStorageRef) parity table path.2
  rw [frame.circuit_resourcePool physical sameWires output mask parity table,
    ResourcePool.count_add]
  simp only [reduceCtorEq, ↓reduceIte] at first
  omega

/-- Physical H/reset X, real unary seed/inverse and all feedback single-qubit events are paid. -/
lemma circuit_singleQubit_count_le
    (path : (frame.circuit (services := services)
      physical sameWires output mask parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
      ((frame.circuit physical sameWires output mask parity table).resourcePool path) ≤
        2 * resultWidth + 2 + (4 * 2 ^ (highRemaining + 1) - 2) := by
  have first := measuredResetWordCircuit_gate_count_le (oracles := .empty)
    (services := services) physical sameWires frame.result frame.resultDistinct output mask
    .singleQubit path.1
  have last := frame.restorationCircuit_singleQubit_count_le physical sameWires
    (.storage mask.toCStorageRef) parity table path.2
  rw [frame.circuit_resourcePool physical sameWires output mask parity table,
    ResourcePool.count_add]
  simp only [↓reduceIte] at first
  omega

/-- The actual packed-mask operation and every native parity-row operation remain paid. -/
lemma circuit_classical_weight_le
    (path : (frame.circuit (services := services)
      physical sameWires output mask parity table).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.circuit physical sameWires output mask parity table).resourcePool path) ≤
        1 + 2 ^ (highRemaining + 1) * 2 ^ lowWidth * (resultWidth + 1) := by
  have last := frame.restorationCircuit_classical_weight_le physical sameWires
    (.storage mask.toCStorageRef) parity table path.2
  rw [frame.circuit_resourcePool physical sameWires output mask parity table,
    ResourcePool.weightedCount_add, measuredResetWordCircuit_classical_weight]
  omega

/-- Real parallel H/reset X and unary/feedback/inverse depth are retained in the actual circuit. -/
lemma circuit_quantumTime_le
    (path : (frame.circuit (services := services)
      physical sameWires output mask parity table).Path) :
    (frame.circuit physical sameWires output mask parity table).depth
      Resource.Event.quantumDuration path ≤
        2 + 2 * (2 ^ lowWidth + lowWidth) +
          ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8) := by
  have first := measuredResetWordCircuit_quantumTime_le (oracles := .empty)
    (services := services) physical sameWires frame.result frame.resultDistinct output mask path.1
  have last := frame.restorationCircuit_quantumTime_le (services := services) physical sameWires
    (.storage mask.toCStorageRef) parity table path.2
  have addition := Circuit.depth_seq
    (measuredResetWordCircuit (oracles := .empty) (services := services) physical sameWires
      frame.result frame.resultDistinct output mask)
    (frame.restorationCircuit (services := services) physical sameWires
      (.storage mask.toCStorageRef) parity table) Resource.Event.quantumDuration path.1 path.2
  exact addition.trans_le (by omega)

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
