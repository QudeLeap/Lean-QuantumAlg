/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Coordinates

/-!
# Actual chronological measured-word native coordinates and retained feedback bounds

The recurrences follow the literal sequence in the execution AST. They
retain actual branch-selected reset and phase instructions on every path,
and charge every physical measurement separately from quantum gate time
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Exact original native CNOT occurrences in the actual chronological measured word. -/
def wordCnotCount (word : List (Instruction encoding records)) : Nat :=
  (word.map cnotCount).sum

/-- Exact actual physical qubit measurements in the chronological instruction word. -/
def wordMeasurementCount (word : List (Instruction encoding records)) : Nat :=
  (word.map measurementCount).sum

/-- A uniform actual-path single-qubit bound including paid reset and stored-result phases. -/
def wordSingleQubitBound (word : List (Instruction encoding records)) : Nat :=
  (word.map singleQubitBound).sum

/-- Source concatenation adds the same actual native CNOT occurrences. -/
lemma wordCnotCount_append (first second : List (Instruction encoding records)) :
    wordCnotCount (first ++ second) = wordCnotCount first + wordCnotCount second := by
  simp only [wordCnotCount, List.map_append, List.sum_append]

/-- Source concatenation adds every actual physical measurement occurrence. -/
lemma wordMeasurementCount_append (first second : List (Instruction encoding records)) :
    wordMeasurementCount (first ++ second) =
      wordMeasurementCount first + wordMeasurementCount second := by
  simp only [wordMeasurementCount, List.map_append, List.sum_append]

/-- Source concatenation retains the paid uniform single-qubit bounds of both real subwords. -/
lemma wordSingleQubitBound_append (first second : List (Instruction encoding records)) :
    wordSingleQubitBound (first ++ second) =
      wordSingleQubitBound first + wordSingleQubitBound second := by
  simp only [wordSingleQubitBound, List.map_append, List.sum_append]

/-- Every complete actual chronological path retains these exact CNOT/MZ and charged X/Z bounds. -/
lemma wordCircuit_coordinates (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    ∀ (word : List (Instruction encoding records))
      (path : (wordCircuit (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output word).Path),
    let pool := (wordCircuit physical sameWires output word).resourcePool path
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .cnot) pool = wordCnotCount word ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles operations services)
        (.measurement (2 : ℕ+)) pool = wordMeasurementCount word ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.gate .singleQubit) pool ≤ wordSingleQubitBound word := by
  intro word
  induction word with
  | nil =>
      intro path
      exact ⟨rfl, rfl, Nat.le_refl 0⟩
  | cons instruction rest ih =>
      intro path
      change (instruction.circuit (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output).Path ×
          (wordCircuit (oracles := oracles) (operations := operations) (services := services)
            physical sameWires output rest).Path at path
      have head := circuit_coordinates physical sameWires output instruction path.1
      have tail := ih path.2
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .cnot)
          ((instruction.circuit physical sameWires output).resourcePool path.1 +
            (wordCircuit physical sameWires output rest).resourcePool path.2) =
        instruction.cnotCount + wordCnotCount rest ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+))
          ((instruction.circuit physical sameWires output).resourcePool path.1 +
            (wordCircuit physical sameWires output rest).resourcePool path.2) =
          instruction.measurementCount + wordMeasurementCount rest ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.gate .singleQubit)
          ((instruction.circuit physical sameWires output).resourcePool path.1 +
            (wordCircuit physical sameWires output rest).resourcePool path.2) ≤
          instruction.singleQubitBound + wordSingleQubitBound rest
      rw [ResourcePool.count_add, ResourcePool.count_add, ResourcePool.count_add]
      exact ⟨congrArg₂ (· + ·) head.1 tail.1,
        congrArg₂ (· + ·) head.2.1 tail.2.1, Nat.add_le_add head.2.2 tail.2.2⟩

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
