/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Resources.General
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Pool

/-!
# Native multiplier envelope on the full admitted width and parity domain

The same literal forward MAC, native swap and explicit negative-residue
inverse MAC are counted without a modulus-parity assumption. Width two
has its own finite native circuit ledger. These independent upper bounds
coexist with the smaller odd-modulus bound [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Independent all-parity native Toffoli cap, with the separate width-two source circuit. -/
def generalToffoliBound (width : Nat) : Nat :=
  if width = 2 then 54 else 28 * width ^ 2 - 37 * width

/-- Independent native CNOT cap, retaining the actual finite width-two comparator. -/
def generalCnotBound (width : Nat) : Nat :=
  if width = 2 then 124 else 108 * width ^ 2 - 178 * width

/-- Literal MAC prefixes add the native bounds of every original selected modular row. -/
lemma accumulatePrefixWord_bounds_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width)
    (count : Nat) (bounded : count ≤ width) :
    wordToffoliCount (layout.accumulatePrefixWord wide modulus constants count bounded) ≤
        count * (if width = 2 then 13 else 14 * width - 19) ∧
      wordCnotCount (layout.accumulatePrefixWord wide modulus constants count bounded) ≤
        count * (if width = 2 then 30 else 54 * width - 90) ∧
      wordSingleQubitBound (layout.accumulatePrefixWord wide modulus constants count bounded) ≤
        count * (12 * width - 16) := by
  induction count with
  | zero =>
      simp only [accumulatePrefixWord, wordToffoliCount, wordCnotCount, wordSingleQubitBound,
        List.map_nil, List.sum_nil, Nat.zero_mul, le_refl, and_self]
  | succ count ih =>
      have earlier := ih (by omega)
      have rowT := Addition.Gidney.Measured.Reduction.Layout.modularWord_toffoli_bound_general
        (layout.reductionLayout ⟨count, by omega⟩) wide modulus (constants ⟨count, by omega⟩)
      have rowOther :=
        Addition.Gidney.Measured.Reduction.Layout.modularWord_coordinate_bounds_general
          (layout.reductionLayout ⟨count, by omega⟩) wide modulus (constants ⟨count, by omega⟩)
      rw [accumulatePrefixWord, wordToffoliCount_append, wordCnotCount_append,
        wordSingleQubitBound_append]
      exact ⟨(Nat.add_le_add earlier.1 rowT).trans_eq (Nat.succ_mul _ _).symm,
        (Nat.add_le_add earlier.2.1 rowOther.1).trans_eq (Nat.succ_mul _ _).symm,
        (Nat.add_le_add earlier.2.2 rowOther.2).trans_eq (Nat.succ_mul _ _).symm⟩

private lemma general_toffoli_formula (wide : 2 ≤ width) :
    width * (if width = 2 then 13 else 14 * width - 19) + width +
        width * (if width = 2 then 13 else 14 * width - 19) = generalToffoliBound width := by
  by_cases two : width = 2
  · subst width
    rfl
  · rw [if_neg two, generalToffoliBound, if_neg two]
    have natural : 14 * width - 19 + 19 = 14 * width := by omega
    have scaled := congrArg (fun amount => width * amount) natural
    have total : width * (14 * width - 19) + width + width * (14 * width - 19) +
        37 * width = 28 * width ^ 2 := by nlinarith [scaled]
    omega

private lemma general_cnot_formula (wide : 2 ≤ width) :
    width * (if width = 2 then 30 else 54 * width - 90) + 2 * width +
        width * (if width = 2 then 30 else 54 * width - 90) = generalCnotBound width := by
  by_cases two : width = 2
  · subst width
    rfl
  · rw [if_neg two, generalCnotBound, if_neg two]
    exact multiplication_cnot_formula (by omega)

private lemma general_single_formula (wide : 2 ≤ width) :
    width * (12 * width - 16) + width * (12 * width - 16) =
      24 * width ^ 2 - 32 * width := by
  have natural : 12 * width - 16 + 16 = 12 * width := by omega
  have scaled := congrArg (fun amount => width * amount) natural
  have total : width * (12 * width - 16) + width * (12 * width - 16) +
      32 * width = 24 * width ^ 2 := by nlinarith [scaled]
  omega

/-- The complete original source word obeys all three caps on every admitted width and parity. -/
lemma multiplicationWord_bounds_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) :
    wordToffoliCount (layout.multiplicationWord wide modulus coefficient inverseCoefficient) ≤
        generalToffoliBound width ∧
      wordCnotCount (layout.multiplicationWord wide modulus coefficient inverseCoefficient) ≤
        generalCnotBound width ∧
      wordSingleQubitBound
          (layout.multiplicationWord wide modulus coefficient inverseCoefficient) ≤
        24 * width ^ 2 - 32 * width := by
  have forward := accumulatePrefixWord_bounds_general layout wide modulus
    (forwardConstant modulus coefficient) width le_rfl
  have inverse := accumulatePrefixWord_bounds_general layout wide modulus
    (inverseConstant modulus inverseCoefficient) width le_rfl
  change wordToffoliCount (layout.forwardMACWord wide modulus coefficient) ≤ _ ∧
    wordCnotCount (layout.forwardMACWord wide modulus coefficient) ≤ _ ∧
    wordSingleQubitBound (layout.forwardMACWord wide modulus coefficient) ≤ _ at forward
  change wordToffoliCount (layout.inverseMACWord wide modulus inverseCoefficient) ≤ _ ∧
    wordCnotCount (layout.inverseMACWord wide modulus inverseCoefficient) ≤ _ ∧
    wordSingleQubitBound (layout.inverseMACWord wide modulus inverseCoefficient) ≤ _ at inverse
  have swap := swapPrefixGates_coordinates layout width le_rfl
  change ((layout.swapWordGates).map EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * width ∧
    ((layout.swapWordGates).map EncodedBit.GateSpec.xMultiplicity).sum = 0 at swap
  rw [multiplicationWord, wordToffoliCount_append, wordToffoliCount_append,
    wordCnotCount_append, wordCnotCount_append,
    wordSingleQubitBound_append, wordSingleQubitBound_append, swapWordGates_toffoli]
  change _ ≤ _ ∧
    wordCnotCount (layout.forwardMACWord wide modulus coefficient) +
      ((layout.swapWordGates).map EncodedBit.GateSpec.cnotMultiplicity).sum +
      wordCnotCount (layout.inverseMACWord wide modulus inverseCoefficient) ≤ _ ∧
    wordSingleQubitBound (layout.forwardMACWord wide modulus coefficient) +
      ((layout.swapWordGates).map EncodedBit.GateSpec.xMultiplicity).sum +
      wordSingleQubitBound (layout.inverseMACWord wide modulus inverseCoefficient) ≤ _
  rw [swap.1, swap.2, Nat.add_zero]
  exact ⟨(Nat.add_le_add (Nat.add_le_add_right forward.1 width) inverse.1).trans_eq
      (general_toffoli_formula wide),
    (Nat.add_le_add (Nat.add_le_add_right forward.2.1 (2 * width)) inverse.2.1).trans_eq
      (general_cnot_formula wide),
    (Nat.add_le_add forward.2.2 inverse.2.2).trans_eq (general_single_formula wide)⟩

/-- Complete independent native pool on the admitted domain, without an odd-modulus premise. -/
def generalMultiplicationBudget (oracles : OracleModel) (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
  coordinatePool oracles operations services (generalToffoliBound width) (generalCnotBound width)
    (24 * width ^ 2 - 32 * width) (4 * width * (width - 2))

/-- Every path of the same actual measured circuit meets the full parity-independent pool. -/
lemma multiplicationCircuit_pool_bound_general (layout : Layout encoding width)
    (wide : 2 ≤ width) (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        physical sameWires output).Path) :
    (layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
      physical sameWires output).resourcePool path ≤
        generalMultiplicationBudget oracles operations services width := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output
      (layout.multiplicationWord wide modulus coefficient inverseCoefficient)).Path at path
  have actual := wordCircuit_pool_bound physical sameWires output
    (layout.multiplicationWord wide modulus coefficient inverseCoefficient) path
  have bounds := multiplicationWord_bounds_general layout wide modulus coefficient
    inverseCoefficient
  have measured := multiplicationWord_measurement_bound layout wide modulus
    coefficient inverseCoefficient
  exact actual.trans (coordinatePool_mono bounds.1 bounds.2.1 bounds.2.2 measured)

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
