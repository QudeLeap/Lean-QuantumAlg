/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Arithmetic

/-!
# Carry values of the same actual source ports and static quantum offset

The carry recurrence reads the original addressed source and control values.
Taking a lower native prefix retains every one of those reads. These pure
row values are used to state the actual native gate-fold invariant
[G25, main.tex:209-239,253-271].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {length : Nat}

/-- Original source carries for the selected quantum offset, through the supplied finite prefix. -/
def carryValues (layout : CarryLayout encoding length) (constant : BitVec length)
    (state : Data) : Nat → Bool
  | 0 => false
  | index + 1 =>
      if inside : index < length then
        Bool.carry ((layout.source ⟨index, inside⟩).get state)
          (constant.getLsbD index && layout.control.get state)
          (layout.carryValues constant state index)
      else false

/-- Carries depend only on the original source/control values, with no dirty-output premise. -/
lemma carryValues_congr (layout : CarryLayout encoding length) (constant : BitVec length)
    (first second : Data) (sameControl : layout.control.get first = layout.control.get second)
    (sameSource : ∀ index, (layout.source index).get first = (layout.source index).get second)
    (count : Nat) :
    layout.carryValues constant first count = layout.carryValues constant second count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      by_cases inside : count < length
      · rw [carryValues, carryValues, dif_pos inside, dif_pos inside,
          sameControl, sameSource, ih]
      · rw [carryValues, carryValues, dif_neg inside, dif_neg inside]

/-- The actual lower prefix has exactly the same carry values through its own final carry. -/
lemma carryValues_lower {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (state : Data) (count : Nat) (bounded : count ≤ length) :
    layout.lower.carryValues (constant.setWidth length) state count =
      layout.carryValues constant state count := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      have inside : count < length := by omega
      have larger : count < length + 1 := by omega
      rw [carryValues, carryValues, dif_pos inside, dif_pos larger,
        ih (by omega), BitVec.getLsbD_setWidth]
      simp only [decide_eq_true inside, Bool.true_and, lower]
      rfl

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
