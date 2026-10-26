/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Resources

/-!
# Native gate coordinates of the actual word reset

The physical parallel H bank pays one single-qubit event per result system.
The stored-mask X layer pays its actual selected subset. Real MZ and native
packing remain separate paid coordinates, and add no Toffoli or CNOT event.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

private lemma placed_gate_count (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (coordinate : AlgorithmGate.Coordinate) (path : Unit) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate coordinate) ((Circuit.unitary (operations := BitWord.model)
        (classicalOracles := services) (allowAllocation := false)
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires program)).resourcePool
          path) =
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
        (.gate coordinate) program.eventCost := by
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
    (ResourcePool.ofList ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      program).eventTrace BitWord.model services)) = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context, unitaryOfEqualWires_cost]

private lemma wordHadamard_gate_count (physical : QubitLayout encoding.width)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate coordinate)
      (wordHadamardProgram physical oracles target distinct).eventCost =
        if AlgorithmGate.Coordinate.singleQubit = coordinate then width else 0 := by
  rw [wordHadamardProgram_eventCost, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]
  cases coordinate <;> simp

private lemma wordX_gate_count_le (physical : QubitLayout encoding.width)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (constant : Fin (2 ^ width)) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate coordinate)
      (wordXProgram physical oracles target distinct constant).eventCost ≤
        if AlgorithmGate.Coordinate.singleQubit = coordinate then width else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    wordXProgram_eventTrace, ResourcePool.ofList_replicate,
    ResourcePool.count_scale, ResourcePool.count_singleton]
  have bounded := Word.constantOneIndices_length_le constant
  cases coordinate <;> simp_all

private lemma resultReadouts_gate_count (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (coordinate : AlgorithmGate.Coordinate)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate coordinate) ((Circuit.measurementSequence (gates := AlgorithmGate.model)
        (oracles := oracles) (operations := BitWord.model) (classicalOracles := services)
        (allowAllocation := false) (resultReadouts physical sameWires target output)).resourcePool
          path) = 0 := by
  rw [Circuit.measurementSequence_qubit_resourcePool _ (by
    intro item member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact resultWire_qubit physical sameWires (target.bit index)), ResourcePool.count_nsmul,
    ResourcePool.count_singleton]
  rfl

/-- The same actual H/MZ/pack/stored-X program has only its original single-qubit gate events. -/
lemma measuredResetWordCircuit_gate_count_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (coordinate : AlgorithmGate.Coordinate)
    (path : (measuredResetWordCircuit (oracles := oracles) (services := services)
      physical sameWires target distinct output mask).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate coordinate) ((measuredResetWordCircuit physical sameWires target distinct
        output mask).resourcePool path) ≤
      if AlgorithmGate.Coordinate.singleQubit = coordinate then 2 * width else 0 := by
  dsimp only [measuredResetWordCircuit, Circuit.Path] at path
  have first := wordHadamard_gate_count (oracles := oracles) physical target distinct coordinate
  have last := wordX_gate_count_le (oracles := oracles) physical target distinct
    (resultConstant path.2.2.2.1) coordinate
  unfold measuredResetWordCircuit
  rw [Circuit.resourcePool_count_seq, Circuit.resourcePool_count_seq,
    Circuit.resourcePool_count_seq, placed_gate_count, resultReadouts_gate_count]
  have packed : ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
      ((MaskParity.instruction (oracles := oracles) (services := services)
        (resultPackOp output mask)).resourcePool path.2.2.1) = 0 := by
    change ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
      (ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packFiniteBits width)))) = 0
    rw [ResourcePool.count_singleton]
    rfl
  rw [packed, first]
  change (if AlgorithmGate.Coordinate.singleQubit = coordinate then width else 0) +
    (0 + (0 + ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
      ((Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
        (allowAllocation := false)
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (wordXProgram physical oracles target distinct
            (resultConstant path.2.2.2.1)))).resourcePool path.2.2.2.2))) ≤ _
  rw [placed_gate_count]
  split_ifs at last ⊢ <;> omega

end

end QuantumAlg.EncodedBit.WindowLookup
