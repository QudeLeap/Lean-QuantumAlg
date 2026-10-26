/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Weight
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Time

/-!
# Actual quantum time bounded by the same paid native coordinates

Physical measurement has zero default quantum duration. Its H and selected
reset X, both selected Z phase passes and all original native gates remain
paid. The general actual dependency-to-pool bound is used only as an upper
bound on this same circuit's time [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Every actual instruction's quantum weight is bounded by its paid native coordinates. -/
lemma circuit_quantumWeight_bound (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records)
    (path : (instruction.circuit (oracles := oracles) (operations := operations)
      (services := services) physical sameWires output).Path) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      ((instruction.circuit physical sameWires output).resourcePool path) ≤
        instruction.toffoliCount + instruction.cnotCount + instruction.singleQubitBound := by
  cases instruction with
  | native gates =>
      change ResourcePool.weightedCount Resource.Event.quantumDuration
        (ResourcePool.ofList ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (EncodedBit.GateSpec.programList physical oracles gates)).eventTrace operations
            services)) ≤ _
      rw [unitaryOfEqualWires_trace,
        UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services,
        NativeResources.word_quantumWeight]
      exact (NativeResources.word_length_coordinates gates).le
  | vent target record =>
      change ResourcePool.weightedCount Resource.Event.quantumDuration
        (ResourcePool.ofList ((EncodedBit.MeasuredUncompute.placedCircuit target physical ctx
          sameWires (finiteOutput
            (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
              (output record)) operations services false).eventTrace path)) ≤ 2
      rcases EncodedBit.MeasuredUncompute.placedCircuit_eventTrace_cases target physical ctx
        sameWires _ path with first | second
      · rw [first]
        simp [Circuit.zEvent]
      · rw [second]
        simp [Circuit.zEvent]
  | phase target record =>
      change ResourcePool.weightedCount Resource.Event.quantumDuration
        (ResourcePool.ofList ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (phaseProgram physical target path.1.toFin)).eventTrace operations services)) ≤ 1
      rw [unitaryOfEqualWires_trace]
      unfold phaseProgram
      split
      · have paid : (target.pauliZ physical oracles).eventTrace operations services =
            [.gate .singleQubit] := rfl
        rw [paid]
        simp
      · exact Nat.zero_le 1

/-- Every actual chronological path retains the sum of its original paid native bounds. -/
lemma wordCircuit_quantumWeight_bound (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    ∀ (word : List (Instruction encoding records))
      (path : (wordCircuit (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output word).Path),
    ResourcePool.weightedCount Resource.Event.quantumDuration
      ((wordCircuit physical sameWires output word).resourcePool path) ≤
        wordToffoliCount word + wordCnotCount word + wordSingleQubitBound word := by
  intro word
  induction word with
  | nil => intro path; exact Nat.le_refl 0
  | cons instruction rest ih =>
      intro path
      change (instruction.circuit (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output).Path ×
          (wordCircuit (oracles := oracles) (operations := operations) (services := services)
            physical sameWires output rest).Path at path
      have head := circuit_quantumWeight_bound physical sameWires output instruction path.1
      have tail := ih path.2
      change ResourcePool.weightedCount Resource.Event.quantumDuration
        ((instruction.circuit physical sameWires output).resourcePool path.1 +
          (wordCircuit physical sameWires output rest).resourcePool path.2) ≤
        (instruction.toffoliCount + wordToffoliCount rest) +
          (instruction.cnotCount + wordCnotCount rest) +
            (instruction.singleQubitBound + wordSingleQubitBound rest)
      rw [ResourcePool.weightedCount_add]
      omega

/-- The actual dependency time is bounded by the same literal chronological word's native costs. -/
lemma wordCircuit_quantumTime_bound (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (word : List (Instruction encoding records))
    (path : (wordCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output word).Path) :
    (wordCircuit physical sameWires output word).quantumTime path ≤
      wordToffoliCount word + wordCnotCount word + wordSingleQubitBound word :=
  ((wordCircuit physical sameWires output word).depth_le_weightedCount_of_pool_le
    Resource.Event.quantumDuration _ path le_rfl).trans
      (wordCircuit_quantumWeight_bound physical sameWires output word path)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
