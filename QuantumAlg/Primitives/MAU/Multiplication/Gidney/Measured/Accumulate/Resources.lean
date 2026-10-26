/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Constants
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Resources.Toffoli
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources

/-!
# Native Toffoli recurrence from the actual source-order measured MAC compiler

Each nonzero canonical static row has its proved actual `14n-23` count;
a literal zero row emits identity. The source prefix appends that same
actual measured row. Both forward and explicit inverse words therefore
satisfy the derived native recurrence [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

private lemma selectedRow_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (selector : Fin width) (modulus constant : BitVec width)
    (odd : modulus.getLsbD 0 = true) (canonical : constant.toNat < modulus.toNat) :
    wordToffoliCount ((layout.reductionLayout selector).modularWord wide modulus constant) ≤
      14 * width - 23 := by
  by_cases zero : constant = 0
  · subst constant
    rw [Addition.Gidney.Measured.Reduction.Layout.modularWord_zero_toffoli]
    omega
  · rw [Addition.Gidney.Measured.Reduction.Layout.modularWord_toffoliCount
      _ wide large modulus constant odd canonical zero]

/-- The actual literal prefix obeys the independent linear native-Toffoli row recurrence. -/
lemma accumulatePrefixWord_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus : BitVec width) (odd : modulus.getLsbD 0 = true)
    (constants : Fin width → BitVec width)
    (canonical : ∀ index, (constants index).toNat < modulus.toNat)
    (count : Nat) (bounded : count ≤ width) :
    wordToffoliCount (layout.accumulatePrefixWord wide modulus constants count bounded) ≤
      count * (14 * width - 23) := by
  induction count with
  | zero => simp [accumulatePrefixWord, wordToffoliCount]
  | succ count ih =>
      rw [accumulatePrefixWord, wordToffoliCount_append, Nat.succ_mul]
      have earlier := ih (by omega)
      have row := selectedRow_toffoli_bound layout wide large ⟨count, by omega⟩ modulus
        (constants ⟨count, by omega⟩) odd (canonical ⟨count, by omega⟩)
      omega

/-- The literal full forward measured MAC retains the actual source recurrence bound. -/
lemma forwardMACWord_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient : Nat) :
    wordToffoliCount (layout.forwardMACWord wide modulus coefficient) ≤
      width * (14 * width - 23) :=
  accumulatePrefixWord_toffoli_bound layout wide large modulus odd
    (forwardConstant modulus coefficient)
    (fun index => forwardConstant_canonical modulus coefficient index positive) width le_rfl

/-- The separately emitted negative-residue measured inverse MAC has its own actual bound. -/
lemma inverseMACWord_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient : Nat) :
    wordToffoliCount (layout.inverseMACWord wide modulus coefficient) ≤
      width * (14 * width - 23) :=
  accumulatePrefixWord_toffoli_bound layout wide large modulus odd
    (inverseConstant modulus coefficient)
    (fun index => inverseConstant_canonical modulus coefficient index positive) width le_rfl

/-- Every actual forward-MAC path has the bound derived from the same literal measured word. -/
lemma forwardMACCircuit_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient : Nat) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.forwardMACCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient physical sameWires output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((layout.forwardMACCircuit wide modulus coefficient physical sameWires output).resourcePool
        path) ≤ width * (14 * width - 23) := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output (layout.forwardMACWord wide modulus coefficient)).Path at path
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
    (.gate .toffoli)
    ((wordCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output (layout.forwardMACWord wide modulus coefficient)).resourcePool
        path) ≤ _
  rw [wordCircuit_toffoli_count]
  exact forwardMACWord_toffoli_bound layout wide large modulus positive odd coefficient

/-- Every path of the actual separate inverse MAC retains its independent native recurrence. -/
lemma inverseMACCircuit_toffoli_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient : Nat) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.inverseMACCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient physical sameWires output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((layout.inverseMACCircuit wide modulus coefficient physical sameWires output).resourcePool
        path) ≤ width * (14 * width - 23) := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output (layout.inverseMACWord wide modulus coefficient)).Path at path
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
    (.gate .toffoli)
    ((wordCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output (layout.inverseMACWord wide modulus coefficient)).resourcePool
        path) ≤ _
  rw [wordCircuit_toffoli_count]
  exact inverseMACWord_toffoli_bound layout wide large modulus positive odd coefficient

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
