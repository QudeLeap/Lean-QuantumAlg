/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Split.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Resources.Complete

/-!
# Actual same-word load/unlookup resource composition

The physical split lookup and the complete original measurement-unlookup
retain their own native event pools and dependency depths. The measured
mask and every parity row are paid; no operation is replaced by a budget
witness. All unary systems remain supplied positions of the original result.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (lookup : SelectorFrame encoding (highRemaining + lowWidth))
  (outsideAddress : ∀ bit index,
    (frame.result.bit bit).wire ≠ (lookup.address index).wire)
  (outsideStack : ∀ bit index,
    (frame.result.bit bit).wire ≠ (lookup.stack index).wire)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ resultWidth))
  (height : Nat) (output : Fin resultWidth → CWriteRef ctx (.finite 2))
  (mask : CWriteRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)

local notation "native" => splitLookupProgram lookup physical OracleModel.empty
  (frame.cycleTarget lookup outsideAddress outsideStack) table height
local notation "code" => frame.cycleCircuit (services := services) lookup outsideAddress
  outsideStack physical sameWires table height output mask parity
local notation "tailCode" => frame.circuit (services := services) physical sameWires
  output mask parity (splitTable table)

/-- The original same-word lookup and measurement-unlookup keep their complete actual pools. -/
lemma cycleCircuit_resourcePool (path : (code).Path) :
    (code).resourcePool path = (native).eventCost BitWord.model services +
      (tailCode).resourcePool path.2 := by
  dsimp only [cycleCircuit, SelectorFrame.placedCircuit, Circuit.Path] at path
  change ResourcePool.ofList (_ ++ _) = _
  rw [ResourcePool.ofList_append]
  change ResourcePool.ofList
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires native).eventTrace
      BitWord.model services) + _ = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services,
    unitaryOfEqualWires_cost]
  rfl

private lemma cycleCircuit_gate_count (coordinate : AlgorithmGate.Coordinate) (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((code).resourcePool path) =
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
          (native).eventCost + ResourcePool.count
            (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
            ((tailCode).resourcePool path.2) := by
  have arithmetic
      (tailPool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services)) :
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
        ((native).eventCost BitWord.model services + tailPool) =
          ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
            (native).eventCost + ResourcePool.count
              (model := .quantum AlgorithmGate.model .empty BitWord.model services)
              (.gate coordinate) tailPool := by
    rw [ResourcePool.count_add,
      UnitaryCircuit.unitaryCircuit_event_count_classical_context native BitWord.model services
        (.gate coordinate)]
  exact (congrArg (ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate))
    (frame.cycleCircuit_resourcePool lookup outsideAddress outsideStack physical sameWires
      table height output mask parity path)).trans (arithmetic _)

/-- The real same-word lookup plus both real unary traversals pay these native Toffolis. -/
lemma cycleCircuit_toffoli_count_le (covered : resultWidth ≤ 2 ^ height) (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      ((code).resourcePool path) ≤
        (2 * 2 ^ (highRemaining + lowWidth + 1) - 4) +
          (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4)) := by
  refine (frame.cycleCircuit_gate_count lookup outsideAddress outsideStack physical sameWires
    table height output mask parity .toffoli path).trans_le ?_
  exact Nat.add_le_add
    (Nat.le_of_eq (splitLookupProgram_toffoli_count lookup physical .empty
      (frame.cycleTarget lookup outsideAddress outsideStack) table height covered))
    (frame.circuit_toffoli_count_le physical sameWires output mask parity (splitTable table) path.2)

/-- Actual lookup masks, unary cleanup and paid phase fan-in/inverse CNOTs all remain charged. -/
lemma cycleCircuit_cnot_count_le (covered : resultWidth ≤ 2 ^ height) (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((code).resourcePool path) ≤
        (2 * (2 ^ (highRemaining + lowWidth) - 1) +
          2 * 2 ^ (highRemaining + lowWidth) * (2 * resultWidth - 1)) +
          (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) * 2 ^ lowWidth - 2)) := by
  refine (frame.cycleCircuit_gate_count lookup outsideAddress outsideStack physical sameWires
    table height output mask parity .cnot path).trans_le ?_
  exact Nat.add_le_add
    (splitLookupProgram_cnot_count_le lookup physical .empty
      (frame.cycleTarget lookup outsideAddress outsideStack) table height covered)
    (frame.circuit_cnot_count_le physical sameWires output mask parity (splitTable table) path.2)

/-- All selector X, physical result H/reset X and unary/feedback single-qubit gates are paid. -/
lemma cycleCircuit_singleQubit_count_le (covered : resultWidth ≤ 2 ^ height)
    (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
      ((code).resourcePool path) ≤
        (2 * 2 ^ (highRemaining + lowWidth + 1) - 2) +
          (2 * resultWidth + 2 + (4 * 2 ^ (highRemaining + 1) - 2)) := by
  refine (frame.cycleCircuit_gate_count lookup outsideAddress outsideStack physical sameWires
    table height output mask parity .singleQubit path).trans_le ?_
  exact Nat.add_le_add
    (Nat.le_of_eq (splitLookupProgram_singleQubit_count lookup physical .empty
      (frame.cycleTarget lookup outsideAddress outsideStack) table height covered))
    (frame.circuit_singleQubit_count_le physical sameWires output mask parity (splitTable table)
      path.2)

private lemma native_classical_weight :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((native).eventCost BitWord.model services) = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context native
        BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

/-- The paid native pack and every actual measured-mask parity row retain
their own operation count. -/
lemma cycleCircuit_classical_weight_le (path : (code).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((code).resourcePool path) ≤
        1 + 2 ^ (highRemaining + 1) * 2 ^ lowWidth * (resultWidth + 1) := by
  have pools := frame.cycleCircuit_resourcePool lookup outsideAddress outsideStack physical
    sameWires table height output mask parity path
  have arithmetic
      (tailPool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services)) :
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((native).eventCost BitWord.model services + tailPool) =
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight tailPool := by
    rw [ResourcePool.weightedCount_add, native_classical_weight, Nat.zero_add]
  exact ((congrArg (ResourcePool.weightedCount Resource.Event.classicalOperationWeight)
    pools).trans (arithmetic _)).trans_le
      (frame.circuit_classical_weight_le physical sameWires output mask parity (splitTable table)
        path.2)

/-- The original physical result word is measured once and no lookup/feedback
native program adds MZ. -/
lemma cycleCircuit_measurement_count (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+))
      ((code).resourcePool path) = resultWidth := by
  have pools := frame.cycleCircuit_resourcePool lookup outsideAddress outsideStack physical
    sameWires table height output mask parity path
  have arithmetic
      (tailPool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services)) :
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+))
        ((native).eventCost BitWord.model services + tailPool) =
          ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) tailPool := by
    rw [ResourcePool.count_add,
      UnitaryCircuit.unitaryCircuit_event_count_classical_context native BitWord.model services
        (.measurement (2 : ℕ+)), Nat.zero_add]
  exact ((congrArg (ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+)))
    pools).trans (arithmetic _)).trans
      (frame.circuit_measurement_count physical sameWires parity (splitTable table) output mask
        path.2)

/-- Actual lookup mask layers and all original reset/unary/feedback layers keep their depth. -/
lemma cycleCircuit_quantumTime_le (path : (code).Path) :
    (code).depth Resource.Event.quantumDuration path ≤
      (2 + 10 * (2 ^ (highRemaining + lowWidth) - 1) +
        2 * 2 ^ (highRemaining + lowWidth) * (2 * height + 1)) +
        (2 + 2 * (2 ^ lowWidth + lowWidth) +
          ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8)) := by
  dsimp only [cycleCircuit, SelectorFrame.placedCircuit, Circuit.Path] at path
  have first := splitLookupProgram_quantumTime_le lookup physical .empty
    (frame.cycleTarget lookup outsideAddress outsideStack) table height
  have last := frame.circuit_quantumTime_le physical sameWires output mask parity (splitTable table)
    path.2
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires native).eventDepth
      BitWord.model services) + (tailCode).depth Resource.Event.quantumDuration path.2 ≤ _
  rw [unitaryOfEqualWires_depth, UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]
  exact Nat.add_le_add first last

/-- The actual complete load/unlookup pair uses precisely its caller's existing peak context. -/
lemma cycleCircuit_spaces (path : (code).Path) :
    (code).peakResidentSpace path = ctx.residentSpace ∧
    (code).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ _, Circuit.fixed_peakAuxiliarySpace _ _⟩

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
