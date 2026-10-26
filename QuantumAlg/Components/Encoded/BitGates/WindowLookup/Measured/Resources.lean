/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Circuit
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Actual result-word measurement/reset resources

The same allocation-free circuit contains one real Z measurement per result
wire and the paid packing instruction. Its two physical gate layers give
quantum depth at most two; all measurement writes and classical feedback
remain in the actual dependency expression and native event accounting.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

private lemma pure_measurement_count
    (program : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout) (path : Unit) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.measurement (2 : ℕ+))
      ((Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
        (allowAllocation := false) program).resourcePool path) = 0 := by
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.measurement (2 : ℕ+))
    (ResourcePool.ofList (program.eventTrace BitWord.model services)) = 0
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost program BitWord.model services]
  exact UnitaryCircuit.unitaryCircuit_event_count_classical_context _ _ _ (.measurement (2 : ℕ+))

/-- The actual original result-word sequence measures precisely one qubit per physical position. -/
lemma resultReadouts_measurement_count (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.measurement (2 : ℕ+))
      ((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)).resourcePool path) = width := by
  rw [Circuit.measurementSequence_qubit_resourcePool _ (by
    intro item member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact resultWire_qubit physical sameWires (target.bit index))]
  simp only [resultReadouts, List.length_ofFn, Circuit.zEvent, ResourcePool.count_nsmul,
    ResourcePool.count_singleton_self, Nat.mul_one]

/-- No H, pack or selected X instruction adds a measurement to the actual result-word circuit. -/
lemma measuredResetWordCircuit_measurement_count (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (path : (measuredResetWordCircuit (oracles := oracles) (services := services)
      physical sameWires target distinct output mask).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.measurement (2 : ℕ+))
      ((measuredResetWordCircuit physical sameWires target distinct output mask).resourcePool
        path) = width := by
  dsimp only [measuredResetWordCircuit, Circuit.Path] at path
  unfold measuredResetWordCircuit
  rw [Circuit.resourcePool_count_seq, Circuit.resourcePool_count_seq,
    Circuit.resourcePool_count_seq, pure_measurement_count, resultReadouts_measurement_count]
  have packed : ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.measurement (2 : ℕ+))
      ((MaskParity.instruction (resultPackOp output mask)).resourcePool path.2.2.1) = 0 := by
    change ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.measurement (2 : ℕ+)) (ResourcePool.singleton
        (.classicalOperation (.nominalEncoding (.packFiniteBits width)))) = 0
    simp only [ResourcePool.count_singleton]
    split
    · contradiction
    · rfl
  rw [packed]
  change 0 + (width + (0 + ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.measurement (2 : ℕ+))
    ((Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
      (allowAllocation := false)
      (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (wordXProgram physical oracles target distinct (resultConstant path.2.2.2.1)))).resourcePool
          path.2.2.2.2))) = width
  rw [pure_measurement_count, Nat.zero_add, Nat.add_zero]

private lemma placed_quantumTime_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (bounded : program.evaluatedEventDepth (fun _ => 1) ≤ 1) (path : Unit) :
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
      (allowAllocation := false)
      (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires program)).depth
        Resource.Event.quantumDuration path ≤ 1 := by
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires program).eventDepth
      BitWord.model services) ≤ 1
  refine (DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one _).trans ?_
  rw [unitaryOfEqualWires_depth, UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  exact bounded

/-- Sequential actual MZ writes retain no quantum-gate duration, without removing their events. -/
lemma resultReadouts_quantumTime (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).depth
        Resource.Event.quantumDuration path = 0 := by
  rw [Circuit.measurementSequence_depth]
  simp only [Circuit.zEvent, Resource.Event.quantumDuration_measurement, List.map_const',
    List.sum_replicate, smul_zero]

/-- Actual parallel H and stored-outcome X contribute at most two quantum dependencies. -/
lemma measuredResetWordCircuit_quantumTime_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (path : (measuredResetWordCircuit (oracles := oracles) (services := services)
      physical sameWires target distinct output mask).Path) :
    (measuredResetWordCircuit physical sameWires target distinct output mask).depth
      Resource.Event.quantumDuration path ≤ 2 := by
  dsimp only [measuredResetWordCircuit, Circuit.Path] at path
  have hBound : (wordHadamardProgram physical oracles target distinct).evaluatedEventDepth
      (fun _ => 1) ≤ 1 := by
    rw [wordHadamardProgram, UnitaryCircuit.placeAt_evaluatedEventDepth,
      Gate.HadamardLayer.hadamardLayer_circuit_unit_depth]
    split <;> omega
  have xBound (constant : Fin (2 ^ width)) :
      (wordXProgram physical oracles target distinct constant).evaluatedEventDepth
        (fun _ => 1) ≤ 1 := by
    rw [wordXProgram, GateSpec.parallelProgramList_unitDepth]
    split <;> omega
  have first := placed_quantumTime_le (services := services) physical sameWires _ hBound path.1
  have last := placed_quantumTime_le (services := services) physical sameWires _
    (xBound (resultConstant path.2.2.2.1)) path.2.2.2.2
  have middle := resultReadouts_quantumTime (oracles := oracles) (services := services)
    physical sameWires target output path.2.1
  change _ + (_ + (0 + _)) ≤ 2
  dsimp only [Circuit.depth, Circuit.eventDepth] at first last middle ⊢
  rw [middle, Nat.zero_add, Nat.zero_add]
  omega

/-- The complete existing caller context is the exact resident and auxiliary peak. -/
lemma measuredResetWordCircuit_spaces (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (path : (measuredResetWordCircuit (oracles := oracles) (services := services)
      physical sameWires target distinct output mask).Path) :
    (measuredResetWordCircuit physical sameWires target distinct output mask).peakResidentSpace
      path = ctx.residentSpace ∧
    (measuredResetWordCircuit physical sameWires target distinct output mask).peakAuxiliarySpace
      path = ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ _, Circuit.fixed_peakAuxiliarySpace _ _⟩

end

end QuantumAlg.EncodedBit.WindowLookup
