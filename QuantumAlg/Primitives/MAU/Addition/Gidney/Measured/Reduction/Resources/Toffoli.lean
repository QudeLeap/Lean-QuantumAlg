/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Parity
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Toffoli

/-!
# Exact actual native Toffoli count of measured clean-flag modular addition

The literal program retains two native comparisons, two chronological
measured additions and the middle flag Toffoli. An odd modulus makes the
two static low-bit contributions complementary. The resulting exact count
is a project derivation from the emitted native instructions; no semantic
reordering or unused identity padding is counted [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Execution EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

private lemma nativeWord_toffoli {records : Nat} (gates : List (GateSpec encoding)) :
    wordToffoliCount (records := records) [.native gates] =
      (gates.map toffoliMultiplicity).sum := by
  simp only [wordToffoliCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    toffoliCount, Nat.add_zero]

private lemma toggleFlag_toffoli (layout : Layout encoding width) :
    (layout.toggleFlagGates.map toffoliMultiplicity).sum = 1 := rfl

/-- The actual zero-offset source program is identity and emits no native Toffoli. -/
lemma modularWord_zero_toffoli (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) :
    wordToffoliCount (layout.modularWord wide modulus 0) = 0 := by
  rw [modularWord, if_pos rfl]
  rfl

/-- Exact source-native multiplicity of a nonzero canonical offset for an odd modulus. -/
lemma modularWord_toffoliCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus constant : BitVec width)
    (odd : modulus.getLsbD 0 = true) (constantBound : constant.toNat < modulus.toNat)
    (nonzero : constant ≠ 0) :
    wordToffoliCount (layout.modularWord wide modulus constant) = 14 * width - 23 := by
  have thresholdNonzero : modulus - constant ≠ 0 := by
    apply sub_ne_zero.mpr
    intro same
    have values := congrArg BitVec.toNat same
    omega
  rw [modularWord, if_neg nonzero]
  simp only [wordToffoliCount_append, nativeWord_toffoli]
  rw [comparisonGates_toffoli layout wide large _ thresholdNonzero,
    Measured.Layout.adderWord_toffoliCount layout.adderLayout wide large,
    toggleFlag_toffoli,
    Measured.Layout.adderWord_toffoliCount layout.adderLayout wide large,
    comparisonGates_toffoli layout wide large constant nonzero]
  have firstOffset : -(modulus - constant) = constant - modulus := by ring
  rw [firstOffset, negative_low_bit]
  have complementary := modular_offsets_low_sum modulus constant (by omega) odd
  omega

/-- Every actual retained path of this same compiled measured program has that native count. -/
lemma modularCircuit_toffoli_count (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus constant : BitVec width)
    (odd : modulus.getLsbD 0 = true) (constantBound : constant.toNat < modulus.toNat)
    (nonzero : constant ≠ 0) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.modularCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus constant physical sameWires output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((layout.modularCircuit wide modulus constant physical sameWires output).resourcePool path) =
        14 * width - 23 := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output (layout.modularWord wide modulus constant)).Path at path
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
    (.gate .toffoli)
    ((wordCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output (layout.modularWord wide modulus constant)).resourcePool path) = _
  rw [wordCircuit_toffoli_count,
    modularWord_toffoliCount layout wide large modulus constant odd constantBound nonzero]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
