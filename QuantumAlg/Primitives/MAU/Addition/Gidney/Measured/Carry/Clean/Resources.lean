/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Gates

/-!
# Exact native Toffoli multiplicity of the clean-low carry generator

This independent structural induction counts the literal native list. The
clean-input semantic omission proof is separate; resource equality is not
inferred from semantic equivalence. The count removes exactly one native
Toffoli when the original carry prefix has at least two outputs
[G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma retainedDescending_toffoli {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) :
    (((if 1 < length then layout.descendingTop constant positive else []).map
      toffoliMultiplicity).sum) = if 1 < length then 1 else 0 := by
  by_cases upper : 1 < length
  · rw [if_pos upper, if_pos upper]
    unfold descendingTop
    apply affineToffoliGates_toffoliMultiplicity
  · rw [if_neg upper, if_neg upper]
    rfl

private lemma retainedAscending_toffoli {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) :
    ((layout.ascendingTop constant positive).map toffoliMultiplicity).sum = 1 := by
  unfold ascendingTop
  apply affineToffoliGates_toffoliMultiplicity

private lemma cleanOffset_toffoli {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1)) :
    ((layout.topOffsetGates constant).map toffoliMultiplicity).sum = 0 := by
  unfold topOffsetGates
  split_ifs <;> rfl

private lemma cleanLow_toffoli {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (positive : 0 < length) :
    ((layout.lowGates constant).map toffoliMultiplicity).sum =
      (constant.getLsbD 0).toNat := by
  rw [lowGates, dif_pos positive]
  cases constant.getLsbD 0 <;> rfl

/-- The clean-low source word has exactly one fewer native Toffoli for length at least two. -/
lemma cleanLowGates_toffoliMultiplicity :
    ∀ {length : Nat} (layout : CarryLayout encoding length) (constant : BitVec length),
    ((layout.cleanLowGates constant).map toffoliMultiplicity).sum =
      2 * (length - 1) - (if 1 < length then 1 else 0) + (constant.getLsbD 0).toNat := by
  intro length
  induction length with
  | zero => intro layout constant; simp [cleanLowGates, BitVec.getLsbD_of_ge]
  | succ length ih =>
      intro layout constant
      by_cases positive : 0 < length
      · rw [cleanLowGates, dif_pos positive, List.map_append, List.map_append, List.map_append,
          List.sum_append, List.sum_append, List.sum_append, retainedDescending_toffoli,
          ih, cleanOffset_toffoli, retainedAscending_toffoli]
        have low : (constant.setWidth length).getLsbD 0 = constant.getLsbD 0 := by
          simp [positive]
        rw [low]
        split_ifs <;> omega
      · have zero : length = 0 := by omega
        subst length
        rw [cleanLowGates, dif_neg (by omega : ¬ 0 < 0), List.map_append, List.sum_append,
          cleanOffset_toffoli, cleanLow_toffoli _ _ (by omega)]
        omega

/-- Exact native count in the nontrivial comparison prefixes, independently of dirty values. -/
lemma cleanLowGates_toffoli_of_large {length : Nat} (layout : CarryLayout encoding length)
    (large : 2 ≤ length) (constant : BitVec length) :
    ((layout.cleanLowGates constant).map toffoliMultiplicity).sum =
      2 * length - 3 + (constant.getLsbD 0).toNat := by
  rw [cleanLowGates_toffoliMultiplicity, if_pos (by omega : 1 < length)]
  congr 1
  omega

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
