/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Resources.Coordinates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Word

/-!
# Closed CNOT and paid one-qubit bounds of the actual measured multiplier

Each MAC retains every literal static modular-addition row. The separately
emitted negative inverse MAC has the same independently bounded row costs.
Every original controlled exchange pays two native CNOTs and one Toffoli
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution EncodedBit Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Literal chronological MAC prefixes obey both independently stated per-row native bounds. -/
lemma accumulatePrefixWord_coordinate_bounds (layout : Layout encoding width)
    (wide : 2 ≤ width) (large : 3 ≤ width) (modulus : BitVec width)
    (constants : Fin width → BitVec width) (count : Nat) (bounded : count ≤ width) :
    wordCnotCount (layout.accumulatePrefixWord wide modulus constants count bounded) ≤
        count * (54 * width - 90) ∧
      wordSingleQubitBound (layout.accumulatePrefixWord wide modulus constants count bounded) ≤
        count * (12 * width - 16) := by
  induction count with
  | zero => simp [accumulatePrefixWord, wordCnotCount, wordSingleQubitBound]
  | succ count ih =>
      rw [accumulatePrefixWord, wordCnotCount_append, wordSingleQubitBound_append]
      have earlier := ih (by omega)
      have row := Addition.Gidney.Measured.Reduction.Layout.modularWord_coordinate_bounds
        (layout.reductionLayout ⟨count, by omega⟩) wide large modulus (constants ⟨count, by omega⟩)
      constructor
      · exact (Nat.add_le_add earlier.1 row.1).trans (Nat.le_of_eq (Nat.succ_mul _ _).symm)
      · exact (Nat.add_le_add earlier.2 row.2).trans (Nat.le_of_eq (Nat.succ_mul _ _).symm)

/-- The actual original-pair exchange prefix has exactly two CNOTs per pair and no single gate. -/
lemma swapPrefixGates_coordinates (layout : Layout encoding width) (count : Nat)
    (bounded : count ≤ width) :
    ((layout.swapPrefixGates count bounded).map GateSpec.cnotMultiplicity).sum = 2 * count ∧
      ((layout.swapPrefixGates count bounded).map GateSpec.xMultiplicity).sum = 0 := by
  induction count with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
      rw [swapPrefixGates]
      simp only [List.map_append, List.sum_append]
      have earlier := ih (by omega)
      rw [earlier.1, earlier.2]
      have rowCnot : ((layout.swapRowGates ⟨count, by omega⟩).map GateSpec.cnotMultiplicity).sum =
          2 := by rw [swapRowGates]; apply fredkin_cnot_count
      have rowSingle : ((layout.swapRowGates ⟨count, by omega⟩).map GateSpec.xMultiplicity).sum =
          0 := rfl
      rw [rowCnot, rowSingle]
      constructor <;> omega

private lemma multiplication_cnot_formula (large : 3 ≤ width) :
    width * (54 * width - 90) + 2 * width + width * (54 * width - 90) =
      108 * width ^ 2 - 178 * width := by
  have natural : 54 * width - 90 + 90 = 54 * width := by omega
  have scaled := congrArg (fun amount => width * amount) natural
  have total : width * (54 * width - 90) + 2 * width + width * (54 * width - 90) +
      178 * width = 108 * width ^ 2 := by nlinarith [scaled]
  omega

private lemma multiplication_single_formula (large : 3 ≤ width) :
    width * (12 * width - 16) + width * (12 * width - 16) =
      24 * width ^ 2 - 32 * width := by
  have natural : 12 * width - 16 + 16 = 12 * width := by omega
  have scaled := congrArg (fun amount => width * amount) natural
  have total : width * (12 * width - 16) + width * (12 * width - 16) +
      32 * width = 24 * width ^ 2 := by nlinarith [scaled]
  omega

/-- The full literal multiplier charges the CNOTs and feedback gates of all its actual stages. -/
lemma multiplicationWord_coordinate_bounds (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus : BitVec width) (coefficient inverseCoefficient : Nat) :
    wordCnotCount (layout.multiplicationWord wide modulus coefficient inverseCoefficient) ≤
        108 * width ^ 2 - 178 * width ∧
      wordSingleQubitBound
          (layout.multiplicationWord wide modulus coefficient inverseCoefficient) ≤
        24 * width ^ 2 - 32 * width := by
  have forward := accumulatePrefixWord_coordinate_bounds layout wide large modulus
    (forwardConstant modulus coefficient) width le_rfl
  have inverse := accumulatePrefixWord_coordinate_bounds layout wide large modulus
    (inverseConstant modulus inverseCoefficient) width le_rfl
  change wordCnotCount (layout.forwardMACWord wide modulus coefficient) ≤
      width * (54 * width - 90) ∧
    wordSingleQubitBound (layout.forwardMACWord wide modulus coefficient) ≤
      width * (12 * width - 16) at forward
  change wordCnotCount (layout.inverseMACWord wide modulus inverseCoefficient) ≤
      width * (54 * width - 90) ∧
    wordSingleQubitBound (layout.inverseMACWord wide modulus inverseCoefficient) ≤
      width * (12 * width - 16) at inverse
  have swap := swapPrefixGates_coordinates layout width le_rfl
  rw [multiplicationWord, wordCnotCount_append, wordCnotCount_append,
    wordSingleQubitBound_append, wordSingleQubitBound_append]
  change wordCnotCount (layout.forwardMACWord wide modulus coefficient) +
      ((layout.swapWordGates).map GateSpec.cnotMultiplicity).sum +
      wordCnotCount (layout.inverseMACWord wide modulus inverseCoefficient) ≤ _ ∧
    wordSingleQubitBound (layout.forwardMACWord wide modulus coefficient) +
      ((layout.swapWordGates).map GateSpec.xMultiplicity).sum +
      wordSingleQubitBound (layout.inverseMACWord wide modulus inverseCoefficient) ≤ _
  change ((layout.swapWordGates).map GateSpec.cnotMultiplicity).sum = 2 * width ∧
    ((layout.swapWordGates).map GateSpec.xMultiplicity).sum = 0 at swap
  rw [swap.1, swap.2]
  constructor
  · exact (Nat.add_le_add (Nat.add_le_add_right forward.1 (2 * width)) inverse.1).trans
      (multiplication_cnot_formula large).le
  · rw [Nat.add_zero]
    exact (Nat.add_le_add forward.2 inverse.2).trans (multiplication_single_formula large).le

/-- Both every-path actual native coordinates inherit the bounds of this same measured word. -/
lemma multiplicationCircuit_coordinate_bounds (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        physical sameWires output).Path) :
    let pool := (layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
      physical sameWires output).resourcePool path
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .cnot) pool ≤ 108 * width ^ 2 - 178 * width ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .singleQubit) pool ≤ 24 * width ^ 2 - 32 * width := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output
      (layout.multiplicationWord wide modulus coefficient inverseCoefficient)).Path at path
  have actual := wordCircuit_coordinates physical sameWires output
    (layout.multiplicationWord wide modulus coefficient inverseCoefficient) path
  have bounds := multiplicationWord_coordinate_bounds layout wide large modulus
    coefficient inverseCoefficient
  exact ⟨actual.1.le.trans bounds.1, actual.2.2.trans bounds.2⟩

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
