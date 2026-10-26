/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Gates

/-!
# Native CNOT and X coordinates of the original recursive carry word

Every upper row retains its descending and ascending affine conjugations
and its static offset CNOT. The low row has at most three CNOTs. These
bounds inspect the actual addressed generator [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

lemma descendingTop_coordinates {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) :
    ((layout.descendingTop constant positive).map cnotMultiplicity).sum ≤ 2 ∧
      ((layout.descendingTop constant positive).map xMultiplicity).sum = 0 := by
  unfold descendingTop
  dsimp only
  unfold affineToffoliGates
  split_ifs <;> simp_all [cnotMultiplicity, xMultiplicity]

lemma ascendingTop_coordinates {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) :
    ((layout.ascendingTop constant positive).map cnotMultiplicity).sum ≤ 4 ∧
      ((layout.ascendingTop constant positive).map xMultiplicity).sum = 0 := by
  unfold ascendingTop
  dsimp only
  unfold affineToffoliGates
  split_ifs <;> simp_all [cnotMultiplicity, xMultiplicity]

lemma topOffsetGates_coordinates {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) :
    ((layout.topOffsetGates constant).map cnotMultiplicity).sum ≤ 1 ∧
      ((layout.topOffsetGates constant).map xMultiplicity).sum = 0 := by
  unfold topOffsetGates
  split <;> simp [cnotMultiplicity, xMultiplicity]

lemma lowGates_coordinates {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) :
    ((layout.lowGates constant).map cnotMultiplicity).sum ≤ 2 ∧
      ((layout.lowGates constant).map xMultiplicity).sum = 0 := by
  unfold lowGates
  dsimp only
  split
  · split <;> simp [cnotMultiplicity, xMultiplicity]
  · simp

/-- Every positive-length literal carry word pays at most seven CNOTs per upper row. -/
lemma gates_cnot_bound : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length),
    ((layout.gates constant).map cnotMultiplicity).sum ≤ 7 * length - 4 := by
  intro length
  induction length with
  | zero => intro layout constant; rfl
  | succ length ih =>
      intro layout constant
      by_cases positive : 0 < length
      · rw [gates, dif_pos positive]
        simp only [List.map_append, List.sum_append]
        have lower := ih layout.lower (constant.setWidth length)
        have descending := (descendingTop_coordinates layout constant positive).1
        have ascending := (ascendingTop_coordinates layout constant positive).1
        have offset := (topOffsetGates_coordinates layout constant).1
        omega
      · rw [gates, dif_neg positive]
        simp only [List.map_append, List.sum_append]
        have offset := (topOffsetGates_coordinates layout constant).1
        have low := (lowGates_coordinates layout constant).1
        have empty : length = 0 := by omega
        subst length
        omega

/-- The same carry generator contains no native single-qubit X instruction. -/
lemma gates_x_count : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length), ((layout.gates constant).map xMultiplicity).sum = 0 := by
  intro length
  induction length with
  | zero => intro layout constant; rfl
  | succ length ih =>
      intro layout constant
      by_cases positive : 0 < length
      · rw [gates, dif_pos positive]
        simp only [List.map_append, List.sum_append, ih,
          (descendingTop_coordinates layout constant positive).2,
          (ascendingTop_coordinates layout constant positive).2,
          (topOffsetGates_coordinates layout constant).2, Nat.add_zero]
      · rw [gates, dif_neg positive]
        simp only [List.map_append, List.sum_append,
          (topOffsetGates_coordinates layout constant).2,
          (lowGates_coordinates layout constant).2, Nat.add_zero]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
