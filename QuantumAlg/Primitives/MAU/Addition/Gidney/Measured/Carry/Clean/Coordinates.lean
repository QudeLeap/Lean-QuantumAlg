/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Coordinates

/-!
# Actual coordinates after omitting the inactive clean-low descending row

The omitted row removes its two possible conjugating CNOTs. The remaining
source order and all other original addressed gates are retained
[G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The exact emitted clean-low word has the smaller uniform CNOT bound from length two. -/
lemma cleanLowGates_cnot_bound : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length),
    ((layout.cleanLowGates constant).map cnotMultiplicity).sum ≤
      if length < 2 then 3 * length else 7 * length - 6 := by
  intro length
  induction length with
  | zero => intro layout constant; rfl
  | succ length ih =>
      intro layout constant
      by_cases positive : 0 < length
      · rw [cleanLowGates, dif_pos positive]
        simp only [List.map_append, List.sum_append]
        have lower := ih layout.lower (constant.setWidth length)
        have ascending := (ascendingTop_coordinates layout constant positive).1
        have offset := (topOffsetGates_coordinates layout constant).1
        by_cases upper : 1 < length
        · rw [if_pos upper]
          have descending := (descendingTop_coordinates layout constant positive).1
          rw [if_neg (by omega : ¬ length < 2)] at lower
          rw [if_neg (by omega : ¬ length + 1 < 2)]
          omega
        · rw [if_neg upper]
          have one : length = 1 := by omega
          subst length
          norm_num at lower ⊢
          omega
      · rw [cleanLowGates, dif_neg positive]
        simp only [List.map_append, List.sum_append]
        have offset := (topOffsetGates_coordinates layout constant).1
        have low := (lowGates_coordinates layout constant).1
        have empty : length = 0 := by omega
        subst length
        norm_num
        omega

/-- Omitting the inactive descending row does not introduce a single-qubit native gate. -/
lemma cleanLowGates_x_count : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length),
    ((layout.cleanLowGates constant).map xMultiplicity).sum = 0 := by
  intro length
  induction length with
  | zero => intro layout constant; rfl
  | succ length ih =>
      intro layout constant
      by_cases positive : 0 < length
      · rw [cleanLowGates, dif_pos positive]
        have descending := (descendingTop_coordinates layout constant positive).2
        split <;>
          simp only [List.map_append, List.sum_append, List.map_nil, List.sum_nil,
            ih, descending, (topOffsetGates_coordinates layout constant).2,
            (ascendingTop_coordinates layout constant positive).2, Nat.add_zero]
      · rw [cleanLowGates, dif_neg positive]
        simp only [List.map_append, List.sum_append,
          (topOffsetGates_coordinates layout constant).2,
          (lowGates_coordinates layout constant).2, Nat.add_zero]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
