/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Resources.Phase
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Restoration
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Count
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Actual unary preparation, feedback and inverse resources

Both occurrences of the native unary program are paid. Their original gate
coordinates and parallel dependency depths surround the complete paid phase
feedback, on the caller's existing physically reset result systems.
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
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))

/-- The actual native preparation and inverse retain their exact original gate pools. -/
lemma restorationCircuit_resourcePool
    (path : (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path) :
    (frame.restorationCircuit physical sameWires measured parity table).resourcePool path =
      (frame.low.program physical .empty).eventCost BitWord.model services +
        ((frame.phaseCircuit physical sameWires measured parity table).resourcePool path.2.1 +
          (frame.low.uncomputeProgram physical).eventCost BitWord.model services) := by
  dsimp only [restorationCircuit, SelectorFrame.placedCircuit, Circuit.Path] at path
  change ResourcePool.ofList (_ ++ (_ ++ _)) = _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  change ResourcePool.ofList
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (frame.low.program physical .empty)).eventTrace BitWord.model services) +
    (_ + ResourcePool.ofList
      ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (frame.low.uncomputeProgram physical)).eventTrace BitWord.model services)) = _
  rw [
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services,
    unitaryOfEqualWires_cost, unitaryOfEqualWires_cost]
  rfl

private lemma restorationCircuit_gate_count
    (coordinate : AlgorithmGate.Coordinate)
    (path : (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((frame.restorationCircuit physical sameWires measured parity table).resourcePool path) =
        2 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
          (frame.low.program physical .empty).eventCost +
        ResourcePool.count
          (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
          ((frame.phaseCircuit physical sameWires measured parity table).resourcePool
            path.2.1) := by
  have arithmetic
      (middle : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services)) :
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
        ((frame.low.program physical .empty).eventCost BitWord.model services +
          (middle + (frame.low.uncomputeProgram physical).eventCost BitWord.model services)) =
        2 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
          (frame.low.program physical .empty).eventCost + ResourcePool.count
            (model := .quantum AlgorithmGate.model .empty BitWord.model services)
            (.gate coordinate) middle := by
    rw [ResourcePool.count_add, ResourcePool.count_add,
      UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (frame.low.program physical .empty) BitWord.model services (.gate coordinate),
      UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (frame.low.uncomputeProgram physical) BitWord.model services (.gate coordinate)]
    simp only
    rw [frame.low.uncomputeProgram_event_count]
    omega
  exact (congrArg (ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate))
    (frame.restorationCircuit_resourcePool physical sameWires measured parity table path)).trans
      (arithmetic _)

/-- Both original unary traversals and the actual high selectors pay their full Toffoli counts. -/
lemma restorationCircuit_toffoli_count_le
    (path : (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      ((frame.restorationCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4) := by
  rw [frame.restorationCircuit_gate_count physical sameWires measured parity table,
    frame.low.program_toffoli_count]
  exact Nat.add_le_add_left
    (frame.phaseCircuit_toffoli_count_le physical sameWires measured parity table path.2.1) _

/-- Native unary cleanup, feedback fan-in and both inverse words remain paid CNOTs. -/
lemma restorationCircuit_cnot_count_le
    (path : (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((frame.restorationCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) * 2 ^ lowWidth - 2) := by
  rw [frame.restorationCircuit_gate_count physical sameWires measured parity table,
    frame.low.program_cnot_count]
  exact Nat.add_le_add_left
    (frame.phaseCircuit_cnot_count_le physical sameWires measured parity table path.2.1) _

/-- The original unary seed and inverse are added to every actual feedback single-qubit event. -/
lemma restorationCircuit_singleQubit_count_le
    (path : (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
      ((frame.restorationCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 + (4 * 2 ^ (highRemaining + 1) - 2) := by
  rw [frame.restorationCircuit_gate_count physical sameWires measured parity table,
    frame.low.program_singleQubit_count, Nat.mul_one]
  exact Nat.add_le_add_left
    (frame.phaseCircuit_singleQubit_count_le physical sameWires measured parity table path.2.1) _

private lemma pure_classical_weight
    (program : UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (program.eventCost BitWord.model services) = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        program BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

/-- The complete actual paid classical work is precisely the phase-tail work. -/
lemma restorationCircuit_classical_weight_le
    (path : (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.restorationCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 ^ (highRemaining + 1) * 2 ^ lowWidth * (resultWidth + 1) := by
  rw [frame.restorationCircuit_resourcePool physical sameWires measured parity table]
  simp only [ResourcePool.weightedCount_add, pure_classical_weight,
    Nat.zero_add, Nat.add_zero]
  exact frame.phaseCircuit_classical_weight_le physical sameWires measured parity table path.2.1

private lemma placed_quantumTime
    (program : UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum) (path : Unit) :
    (SelectorFrame.placedCircuit (services := services) (operations := BitWord.model)
      physical sameWires program).depth Resource.Event.quantumDuration path =
      program.evaluatedEventDepth Resource.Event.quantumDuration := by
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires program).eventDepth
      BitWord.model services) = _
  rw [unitaryOfEqualWires_depth, UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]

/-- The native inverse preserves actual unary parallelism and surrounds the real feedback depth. -/
lemma restorationCircuit_quantumTime_le
    (path : (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path) :
    (frame.restorationCircuit physical sameWires measured parity table).depth
      Resource.Event.quantumDuration path ≤
        2 * (2 ^ lowWidth + lowWidth) +
          ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8) := by
  dsimp only [restorationCircuit, SelectorFrame.placedCircuit, Circuit.Path] at path
  have first := frame.low.program_quantumTime_le physical .empty
  have last := frame.low.uncomputeProgram_quantumTime_le physical
  have middle := frame.phaseCircuit_quantumTime_le physical sameWires measured parity table
    path.2.1
  change (SelectorFrame.placedCircuit (services := services) (operations := BitWord.model)
    physical sameWires
    (frame.low.program physical .empty)).depth Resource.Event.quantumDuration path.1 +
    ((frame.phaseCircuit physical sameWires measured parity table).depth
      Resource.Event.quantumDuration path.2.1 +
      (SelectorFrame.placedCircuit (services := services) (operations := BitWord.model)
        physical sameWires
        (frame.low.uncomputeProgram physical)).depth Resource.Event.quantumDuration path.2.2) ≤ _
  rw [placed_quantumTime, placed_quantumTime]
  omega

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
