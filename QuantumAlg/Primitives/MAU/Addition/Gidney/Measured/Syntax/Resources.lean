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
# Actual path-native Toffoli accounting for the measured instruction word

Native words contribute exactly their literal addressed Toffolis. Physical
H/MZ/reset and stored-result Z instructions contribute none on every actual
path. Chronological composition retains that same count without replacing
the measured instruction word by a unitary inverse or a semantic gate list
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The literal instruction's native Toffoli multiplicity, before any record is selected. -/
def toffoliCount : Instruction encoding records → Nat
  | .native gates => (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum
  | .vent _ _ => 0
  | .phase _ _ => 0

/-- The Toffoli multiplicity of the same complete chronological physical instruction word. -/
def wordToffoliCount (word : List (Instruction encoding records)) : Nat :=
  (word.map toffoliCount).sum

/-- Source-order concatenation retains the exact sum of both literal native multiplicities. -/
lemma wordToffoliCount_append (first second : List (Instruction encoding records)) :
    wordToffoliCount (first ++ second) = wordToffoliCount first + wordToffoliCount second := by
  simp only [wordToffoliCount, List.map_append, List.sum_append]

/-- Every selected actual instruction path has precisely its literal native Toffoli count. -/
lemma circuit_toffoli_count (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records)
    (path : (instruction.circuit (oracles := oracles) (operations := operations)
      (services := services) physical sameWires output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((instruction.circuit physical sameWires output).resourcePool path) =
        instruction.toffoliCount := by
  cases instruction with
  | native gates =>
      change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .toffoli)
        (ResourcePool.ofList ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (EncodedBit.GateSpec.programList physical oracles gates)).eventTrace operations
            services)) = _
      rw [unitaryOfEqualWires_trace,
        UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services]
      exact NativeResources.word_toffoli_count physical gates
  | vent target record =>
      change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .toffoli) (ResourcePool.ofList
        ((EncodedBit.MeasuredUncompute.placedCircuit target physical ctx sameWires
          (finiteOutput
            (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
              (output record)) operations services false).eventTrace path)) = 0
      rcases EncodedBit.MeasuredUncompute.placedCircuit_eventTrace_cases target physical ctx
        sameWires _ path with first | second
      · rw [first, ResourcePool.count_ofList]
        simp [Circuit.zEvent]
      · rw [second, ResourcePool.count_ofList]
        simp [Circuit.zEvent]
  | phase target record =>
      change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .toffoli) (ResourcePool.ofList
        ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (phaseProgram physical target path.1.toFin)).eventTrace operations services)) = 0
      rw [unitaryOfEqualWires_trace]
      have traced : (phaseProgram (oracles := oracles) physical target path.1.toFin).eventTrace
          operations services =
        if path.1.toFin = 1 then [.gate .singleQubit] else [] := by
        unfold phaseProgram
        split_ifs <;> first | rfl | contradiction
      rw [traced]
      split_ifs <;> simp

/-- Every actual chronological word path has the Toffoli count of that same literal source word. -/
lemma wordCircuit_toffoli_count (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    ∀ (word : List (Instruction encoding records))
      (path : (wordCircuit (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output word).Path),
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((wordCircuit physical sameWires output word).resourcePool path) = wordToffoliCount word := by
  intro word
  induction word with
  | nil => intro path; rfl
  | cons instruction rest ih =>
      intro path
      change (instruction.circuit (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output).Path ×
          (wordCircuit (oracles := oracles) (operations := operations) (services := services)
            physical sameWires output rest).Path at path
      change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .toffoli)
        ((instruction.circuit physical sameWires output).resourcePool path.1 +
          (wordCircuit physical sameWires output rest).resourcePool path.2) = _
      rw [ResourcePool.count_add, circuit_toffoli_count, ih]
      rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
