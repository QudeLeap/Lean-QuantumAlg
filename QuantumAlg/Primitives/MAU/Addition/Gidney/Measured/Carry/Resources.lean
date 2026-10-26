/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Native

/-!
# Toffoli multiplicity of the actual recursive carry word

Every non-low row contains the two literal affine-control Toffolis. The low
row contains a native Toffoli precisely when the static low offset bit is one.
The exact formula is a project derivation from this actual native generator,
rather than an exact formula stated in the paper [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma descendingTop_toffoli {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) :
    ((layout.descendingTop constant positive).map toffoliMultiplicity).sum = 1 := by
  unfold descendingTop
  apply affineToffoliGates_toffoliMultiplicity

private lemma ascendingTop_toffoli {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) :
    ((layout.ascendingTop constant positive).map toffoliMultiplicity).sum = 1 := by
  unfold ascendingTop
  apply affineToffoliGates_toffoliMultiplicity

private lemma topOffsetGates_toffoli {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1)) :
    ((layout.topOffsetGates constant).map toffoliMultiplicity).sum = 0 := by
  unfold topOffsetGates
  split_ifs <;> rfl

private lemma lowGates_toffoli {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (positive : 0 < length) :
    ((layout.lowGates constant).map toffoliMultiplicity).sum =
      (constant.getLsbD 0).toNat := by
  simp only [lowGates, dif_pos positive]
  cases constant.getLsbD 0 <;> rfl

/-- The exact native source-word Toffoli count, including the empty carry prefix. -/
lemma gates_toffoliMultiplicity : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length),
    ((layout.gates constant).map toffoliMultiplicity).sum =
      2 * (length - 1) + (constant.getLsbD 0).toNat := by
  intro length
  induction length with
  | zero =>
      intro layout constant
      simp [gates, BitVec.getLsbD_of_ge]
  | succ length ih =>
      intro layout constant
      by_cases positive : 0 < length
      · rw [gates, dif_pos positive, List.map_append, List.map_append, List.map_append,
          List.sum_append, List.sum_append, List.sum_append,
          descendingTop_toffoli, ih, topOffsetGates_toffoli, ascendingTop_toffoli]
        have low : (constant.setWidth length).getLsbD 0 = constant.getLsbD 0 := by
          simp [positive]
        rw [low]
        omega
      · have zero : length = 0 := by omega
        subst length
        rw [gates, dif_neg (by omega : ¬ 0 < 0), List.map_append, List.sum_append,
          topOffsetGates_toffoli, lowGates_toffoli _ _ (by omega)]

/-- The compiled word retains its exact Toffoli count in every surrounding hybrid model. -/
lemma program_toffoli_count {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .toffoli)
        ((layout.program constant physical oracles).eventCost operations services) =
      2 * (length - 1) + (constant.getLsbD 0).toNat := by
  rw [program, NativeResources.word_toffoli_count, gates_toffoliMultiplicity]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
