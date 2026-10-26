/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Word

/-!
# Complete actual native event pool of chronological measured arithmetic

The same instruction word emits only original X/CNOT/Toffoli, paid H/reset/Z
and actual dimension-two measurements. Reading stored results introduces no
arithmetic or service grant. The complete pool below retains all four native
coordinates [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Literal separate native allowances with every physical measurement retained. -/
def coordinatePool (oracles : OracleModel) (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) (toffoli cnot single measured : Nat) :
    ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
  ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli) toffoli +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .cnot) cnot +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .singleQubit) single +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) measured

/-- Increasing each independent native coordinate increases the complete literal pool. -/
lemma coordinatePool_mono {firstToffoli firstCnot firstSingle firstMeasured : Nat}
    {lastToffoli lastCnot lastSingle lastMeasured : Nat}
    (toffoli : firstToffoli ≤ lastToffoli) (cnot : firstCnot ≤ lastCnot)
    (single : firstSingle ≤ lastSingle) (measured : firstMeasured ≤ lastMeasured) :
    coordinatePool oracles operations services firstToffoli firstCnot firstSingle firstMeasured ≤
      coordinatePool oracles operations services lastToffoli lastCnot lastSingle lastMeasured := by
  apply ResourcePool.le_iff_count.mpr
  intro focus
  simp only [coordinatePool, ResourcePool.count_add, ResourcePool.count_singleton]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · split <;> first | exact toffoli | exact Nat.le_refl 0
      · split <;> first | exact cnot | exact Nat.le_refl 0
    · split <;> first | exact single | exact Nat.le_refl 0
  · split <;> first | exact measured | exact Nat.le_refl 0

/-- Every other coordinate is absent from the actual selected instruction path. -/
lemma circuit_count_other (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records)
    (path : (instruction.circuit (oracles := oracles) (operations := operations)
      (services := services) physical sameWires output).Path)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles operations services))
    (notToffoli : focus ≠ .gate .toffoli) (notCnot : focus ≠ .gate .cnot)
    (notSingle : focus ≠ .gate .singleQubit) (notMeasured : focus ≠ .measurement (2 : ℕ+)) :
    ResourcePool.count focus ((instruction.circuit physical sameWires output).resourcePool path) =
      0 := by
  cases instruction with
  | native gates =>
      change ResourcePool.count focus
        (ResourcePool.ofList ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (EncodedBit.GateSpec.programList physical oracles gates)).eventTrace operations
            services)) = 0
      rw [unitaryOfEqualWires_trace,
        UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services,
        NativeResources.word_count]
      apply List.sum_eq_zero
      intro value present
      obtain ⟨gate, _, rfl⟩ := List.mem_map.mp present
      cases gate with
      | x => exact if_neg (Ne.symm notSingle)
      | cnot => exact if_neg (Ne.symm notCnot)
      | toffoli => exact if_neg (Ne.symm notToffoli)
  | vent target record =>
      change ResourcePool.count focus (ResourcePool.ofList
        ((EncodedBit.MeasuredUncompute.placedCircuit target physical ctx sameWires
          (finiteOutput
            (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
              (output record)) operations services false).eventTrace path)) = 0
      rcases EncodedBit.MeasuredUncompute.placedCircuit_eventTrace_cases target physical ctx
        sameWires _ path with first | second
      · rw [first]
        simp [Circuit.zEvent, Ne.symm notSingle, Ne.symm notMeasured]
      · rw [second]
        simp [Circuit.zEvent, Ne.symm notSingle, Ne.symm notMeasured]
  | phase target record =>
      change ResourcePool.count focus (ResourcePool.ofList
        ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (phaseProgram physical target path.1.toFin)).eventTrace operations services)) = 0
      rw [unitaryOfEqualWires_trace]
      unfold phaseProgram
      split
      · have paid : (target.pauliZ physical oracles).eventTrace operations services =
            [.gate .singleQubit] := rfl
        rw [paid]
        simp [Ne.symm notSingle]
      · exact ResourcePool.count_zero focus

/-- Chronological source composition introduces no coordinate outside the actual four kinds. -/
lemma wordCircuit_count_other (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles operations services))
    (notToffoli : focus ≠ .gate .toffoli) (notCnot : focus ≠ .gate .cnot)
    (notSingle : focus ≠ .gate .singleQubit) (notMeasured : focus ≠ .measurement (2 : ℕ+)) :
    ∀ (word : List (Instruction encoding records))
      (path : (wordCircuit (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output word).Path),
      ResourcePool.count focus ((wordCircuit physical sameWires output word).resourcePool path) =
        0 := by
  intro word
  induction word with
  | nil => intro path; exact ResourcePool.count_zero focus
  | cons instruction rest ih =>
      intro path
      change (instruction.circuit (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output).Path ×
          (wordCircuit (oracles := oracles) (operations := operations) (services := services)
            physical sameWires output rest).Path at path
      change ResourcePool.count focus
        ((instruction.circuit physical sameWires output).resourcePool path.1 +
          (wordCircuit physical sameWires output rest).resourcePool path.2) = 0
      rw [ResourcePool.count_add,
        circuit_count_other physical sameWires output instruction path.1 focus
          notToffoli notCnot notSingle notMeasured, ih]

/-- The complete actual word pool retains all its native coordinates, with paid feedback bounds. -/
lemma wordCircuit_pool_bound (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (word : List (Instruction encoding records))
    (path : (wordCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output word).Path) :
    (wordCircuit physical sameWires output word).resourcePool path ≤
      coordinatePool oracles operations services (wordToffoliCount word) (wordCnotCount word)
        (wordSingleQubitBound word) (wordMeasurementCount word) := by
  apply ResourcePool.le_iff_count.mpr
  intro focus
  have actual := wordCircuit_coordinates physical sameWires output word path
  by_cases toffoli : focus = .gate .toffoli
  · subst focus
    simpa [coordinatePool] using (wordCircuit_toffoli_count physical sameWires output word path).le
  by_cases cnot : focus = .gate .cnot
  · subst focus
    simpa [coordinatePool] using actual.1.le
  by_cases single : focus = .gate .singleQubit
  · subst focus
    simpa [coordinatePool] using actual.2.2
  by_cases measured : focus = .measurement (2 : ℕ+)
  · subst focus
    simpa [coordinatePool] using actual.2.1.le
  rw [wordCircuit_count_other physical sameWires output focus toffoli cnot single measured]
  exact Nat.zero_le _

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
