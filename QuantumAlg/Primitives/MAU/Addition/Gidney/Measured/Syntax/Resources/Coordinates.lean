/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Native
import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Placement.Resources

/-!
# Actual CNOT, physical measurement and single-qubit coordinates of measured instructions

The same actual H/MZ/write/read/reset path emits one measurement and its
selected reset X. Stored-outcome phase feedback emits its actual Z or
identity. Native words retain their original event trace in the full
surrounding hybrid model [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The exact native CNOT multiplicity of this same emitted instruction. -/
def cnotCount : Instruction encoding records → Nat
  | .native gates => (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum
  | .vent _ _ => 0
  | .phase _ _ => 0

/-- Every actual vent contributes exactly one physical dimension-two measurement. -/
def measurementCount : Instruction encoding records → Nat
  | .native _ => 0
  | .vent _ _ => 1
  | .phase _ _ => 0

/-- The path-uniform native bound charges H, possible reset X and possible stored-result Z. -/
def singleQubitBound : Instruction encoding records → Nat
  | .native gates => (gates.map EncodedBit.GateSpec.xMultiplicity).sum
  | .vent _ _ => 2
  | .phase _ _ => 1

/-- Every actual path has its exact CNOT/MZ coordinates and its charged one-qubit bound. -/
lemma circuit_coordinates (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records)
    (path : (instruction.circuit (oracles := oracles) (operations := operations)
      (services := services) physical sameWires output).Path) :
    let pool := (instruction.circuit physical sameWires output).resourcePool path
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .cnot) pool = instruction.cnotCount ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles operations services)
        (.measurement (2 : ℕ+)) pool = instruction.measurementCount ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.gate .singleQubit) pool ≤ instruction.singleQubitBound := by
  dsimp only
  cases instruction with
  | native gates =>
      let pool : ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
        ResourcePool.ofList ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (EncodedBit.GateSpec.programList physical oracles gates)).eventTrace operations services)
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .cnot) pool = _ ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) pool = _ ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model oracles operations services)
            (.gate .singleQubit) pool ≤ _
      have actual : pool =
          (EncodedBit.GateSpec.programList physical oracles gates).eventCost
            operations services := by
        dsimp only [pool]
        rw [unitaryOfEqualWires_trace,
          UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services]
      rw [actual]
      exact ⟨NativeResources.word_cnot_count physical gates,
        NativeResources.word_measurement_count physical gates 2,
        (NativeResources.word_singleQubit_count physical gates).le⟩
  | vent target record =>
      let code := EncodedBit.MeasuredUncompute.placedCircuit (oracles := oracles)
        target physical ctx sameWires
        (finiteOutput (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
          (output record)) operations services false
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .cnot) (ResourcePool.ofList (code.eventTrace path)) = 0 ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) (ResourcePool.ofList (code.eventTrace path)) = 1 ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model oracles operations services)
            (.gate .singleQubit)
            (ResourcePool.ofList (code.eventTrace path)) ≤ 2
      rcases EncodedBit.MeasuredUncompute.placedCircuit_eventTrace_cases target physical ctx
        sameWires _ path with first | second
      · change code.eventTrace path = _ at first
        rw [first]
        simp [Circuit.zEvent]
      · change code.eventTrace path = _ at second
        rw [second]
        simp [Circuit.zEvent]
  | phase target record =>
      let pool : ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
        ResourcePool.ofList ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (phaseProgram physical target path.1.toFin)).eventTrace operations services)
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .cnot) pool = 0 ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) pool = 0 ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model oracles operations services)
            (.gate .singleQubit) pool ≤ 1
      have traced : (phaseProgram (oracles := oracles) physical target path.1.toFin).eventTrace
          operations services =
        if path.1.toFin = 1 then [.gate .singleQubit] else [] := by
        unfold phaseProgram
        split_ifs <;> first | rfl | contradiction
      dsimp only [pool]
      rw [unitaryOfEqualWires_trace, traced]
      split_ifs <;> simp

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
