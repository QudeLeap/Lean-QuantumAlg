/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Native Toffoli bound derived from the actual measured multiplier word

The literal forward MAC and explicit inverse MAC each supply their own
proved row recurrence. The intervening native word executes one Toffoli
per original source bit. The derived `28n²-45n` bound is a project formula
for this exact construction, not a quoted paper formula
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution EncodedBit Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Every native source-order swap prefix executes exactly one Toffoli per original pair. -/
lemma swapPrefixGates_toffoli (layout : Layout encoding width) (count : Nat)
    (bounded : count ≤ width) :
    ((layout.swapPrefixGates count bounded).map GateSpec.toffoliMultiplicity).sum = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [swapPrefixGates, List.map_append, List.sum_append, ih (by omega),
        swapRowGates]
      rfl

/-- The actual full controlled native exchange has exactly the original word width Toffolis. -/
lemma swapWordGates_toffoli (layout : Layout encoding width) :
    wordToffoliCount (records := width - 2) [.native layout.swapWordGates] = width := by
  simp only [wordToffoliCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    toffoliCount, Nat.add_zero, swapWordGates]
  exact swapPrefixGates_toffoli layout width le_rfl

private lemma multiplication_count_formula (large : 5 ≤ width) :
    width * (14 * width - 23) + width + width * (14 * width - 23) =
      28 * width ^ 2 - 45 * width := by
  have rowNatural : 14 * width - 23 + 23 = 14 * width := by omega
  have scaled := congrArg (fun value => width * value) rowNatural
  have sumNatural : width * (14 * width - 23) + width + width * (14 * width - 23) +
      45 * width = 28 * width ^ 2 := by nlinarith [scaled]
  omega

/-- The native bound comes from the same literal forward/swap/explicit-inverse measured word. -/
lemma multiplicationWord_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 5 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient inverseCoefficient : Nat) :
    wordToffoliCount (layout.multiplicationWord wide modulus coefficient inverseCoefficient) ≤
      28 * width ^ 2 - 45 * width := by
  rw [multiplicationWord, wordToffoliCount_append, wordToffoliCount_append,
    swapWordGates_toffoli]
  have forward := forwardMACWord_toffoli_bound layout wide (by omega) modulus positive odd
    coefficient
  have inverse := inverseMACWord_toffoli_bound layout wide (by omega) modulus positive odd
    inverseCoefficient
  exact (Nat.add_le_add (Nat.add_le_add_right forward width) inverse).trans
    (Nat.le_of_eq (multiplication_count_formula large))

/-- Every actual multiplier path retains the native bound of that literal measured program. -/
lemma multiplicationCircuit_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 5 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        physical sameWires output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
        physical sameWires output).resourcePool path) ≤ 28 * width ^ 2 - 45 * width := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output
      (layout.multiplicationWord wide modulus coefficient inverseCoefficient)).Path at path
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
    (.gate .toffoli)
    ((wordCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output
        (layout.multiplicationWord wide modulus coefficient inverseCoefficient)).resourcePool
          path) ≤ _
  rw [wordCircuit_toffoli_count]
  exact multiplicationWord_toffoli_bound layout wide large modulus positive odd
    coefficient inverseCoefficient

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
