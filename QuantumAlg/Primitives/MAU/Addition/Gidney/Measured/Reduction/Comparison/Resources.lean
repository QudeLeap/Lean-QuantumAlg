/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Native

/-!
# Actual native Toffoli count of the literal controlled comparison

Both clean-low words retain their independently counted native instructions.
Their direction does not change the multiplicities. The two conjunction
Toffolis and the flag CNOT remain explicit in the source word. This exact
formula is a project derivation from the source construction
[G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}

private lemma activePair_toffoli (layout : Layout encoding width) :
    (layout.activePairGates.map toffoliMultiplicity).sum = 1 := rfl

/-- The literal zero-threshold comparison is actual identity with zero native Toffolis. -/
lemma comparisonGates_zero_toffoli (layout : Layout encoding width) (wide : 2 ≤ width) :
    ((layout.comparisonGates wide 0).map toffoliMultiplicity).sum = 0 := by
  rw [comparisonGates, if_pos rfl]
  rfl

/-- Exact Toffoli multiplicity of the actual positive-threshold comparison source word. -/
lemma comparisonGates_toffoli (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (threshold : BitVec width) (nonzero : threshold ≠ 0) :
    ((layout.comparisonGates wide threshold).map toffoliMultiplicity).sum =
      4 * width - 6 + 2 * ((-threshold).getLsbD 0).toNat := by
  rw [comparisonGates, if_neg nonzero]
  simp only [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
    activePair_toffoli]
  rw [CarryLayout.cleanLowGates_toffoli_of_large _ (by omega : 2 ≤ width) (-threshold),
    CarryLayout.cleanLowGates_toffoli_of_large _ (by omega : 2 ≤ width - 1)]
  have low : ((-threshold).setWidth (width - 1)).getLsbD 0 = (-threshold).getLsbD 0 := by
    rw [BitVec.getLsbD_setWidth, decide_eq_true (by omega : 0 < width - 1), Bool.true_and]
  rw [low]
  change 1 + (2 * width - 3 + ((-threshold).getLsbD 0).toNat) +
    (2 * (width - 1) - 3 + ((-threshold).getLsbD 0).toNat) + 0 + 1 = _
  omega

/-- The compiled native comparator has that same exact count in every surrounding hybrid model. -/
lemma comparisonProgram_toffoli_count (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (threshold : BitVec width) (nonzero : threshold ≠ 0)
    (physical : QubitLayout encoding.width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.gate .toffoli)
      ((layout.comparisonProgram wide threshold physical oracles).eventCost operations services) =
        4 * width - 6 + 2 * ((-threshold).getLsbD 0).toNat := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
    (.gate .toffoli)
    ((programList physical oracles (layout.comparisonGates wide threshold)).eventCost
      operations services) = _
  rw [NativeResources.word_toffoli_count,
    comparisonGates_toffoli layout wide large threshold nonzero]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
