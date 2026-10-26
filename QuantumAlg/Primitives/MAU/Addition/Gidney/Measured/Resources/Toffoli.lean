/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Circuit

/-!
# Exact actual native Toffoli count of the measured constant adder

The formula is derived from the same literal chronological physical word:
the vented stream and the native carry repair retain their individual counts,
while both native complements and both paid phase passes contain no Toffoli.
This exact formula is a project derivation from the source construction,
rather than an exact expression stated by the paper [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Execution EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

private lemma complementGates_toffoli (layout : Layout encoding width) :
    (layout.complementGates.map toffoliMultiplicity).sum = 0 := by
  simp only [complementGates, List.map_ofFn, Function.comp_def, toffoliMultiplicity,
    List.sum_ofFn, Finset.sum_const_zero]

private lemma phaseWord_toffoliCount (layout : Layout encoding width) :
    wordToffoliCount layout.phaseWord = 0 := by
  simp only [wordToffoliCount, phaseWord, List.map_ofFn, Function.comp_def, toffoliCount,
    List.sum_ofFn, Finset.sum_const_zero]

private lemma native_singleton_toffoli {records : Nat} (gates : List (GateSpec encoding)) :
    wordToffoliCount (records := records) [.native gates] =
      (gates.map toffoliMultiplicity).sum := by
  simp only [wordToffoliCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    toffoliCount, Nat.add_zero]

/-- The literal paid native repair retains exactly its carry word's source Toffolis. -/
lemma tailWord_toffoliCount (layout : Layout encoding width) (large : 3 ≤ width)
    (constant : BitVec width) :
    wordToffoliCount (layout.tailWord constant) =
      2 * (width - 3) + (constant.getLsbD 0).toNat := by
  simp only [tailWord, wordToffoliCount_append, phaseWord_toffoliCount,
    native_singleton_toffoli, complementGates_toffoli, Nat.zero_add, Nat.add_zero]
  rw [CarryLayout.gates_toffoliMultiplicity, BitVec.getLsbD_setWidth,
    decide_eq_true (by omega : 0 < width - 2), Bool.true_and]
  congr 1

/-- Exact literal adder multiplicity, with the statically simplified low carry retained. -/
lemma adderWord_toffoliCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (constant : BitVec width) :
    wordToffoliCount (layout.adderWord wide constant) =
      3 * width - 8 + 2 * (constant.getLsbD 0).toNat := by
  rw [adderWord_eq_stream_tail, wordToffoliCount_append, streamingWord_toffoliCount,
    tailWord_toffoliCount layout large]
  omega

/-- Every path of the actual compiled measured adder has the exact source native Toffoli count. -/
lemma adderCircuit_toffoli_count (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.adderCircuit wide constant physical sameWires output
      oracles operations services).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((layout.adderCircuit wide constant physical sameWires output
        oracles operations services).resourcePool path) =
      3 * width - 8 + 2 * (constant.getLsbD 0).toNat := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output (layout.adderWord wide constant)).Path at path
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
    (.gate .toffoli)
    ((wordCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output (layout.adderWord wide constant)).resourcePool path) = _
  rw [wordCircuit_toffoli_count, adderWord_toffoliCount layout wide large]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
