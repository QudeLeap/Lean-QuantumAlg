/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Layout

/-!
# Arithmetic of the two-dirty-bit constant comparison

An extended constant addition records its overflow in an arbitrary high
bit. A low-word offset then restores the original target. Inverting the
high bit converts the greater-or-equal carry to a less-than comparison
[G17, paper.tex:380-389]. The positive-pivot hypothesis is internal to the
nonzero branch; the public comparison uses identity for pivot zero.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

/-- The pivot as a compile-time low-word constant, including a full-capacity pivot. -/
def pivotWord (width pivot : Nat) : Fin (2 ^ width) :=
  ⟨pivot % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩

/-- The additive inverse of a fitted pivot in the target word. -/
def negatedPivot (width pivot : Nat) : Fin (2 ^ width) :=
  ⟨(2 ^ width - pivot) % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩

/-- Extend the subtracting constant with a zero high bit, not an allocated input. -/
def extendedNegatedPivot (width pivot : Nat) : Fin (2 ^ (1 + width)) :=
  prodEquiv (m := 1) (n := width) (0, negatedPivot width pivot)

/-- The independent lower-word offset action, preserving both arbitrary bits. -/
def lowOffsetOutput {width : Nat} (constant : Fin (2 ^ width))
    (state : Registers width) : Registers width :=
  (state.1, HRS.oneDirtyOutput constant state.2)

/-- Invert the comparison target only. -/
def flagFlipOutput {width : Nat} (state : Registers width) : Registers width :=
  (!state.1, state.2)

/-- The exact comparison contract includes arbitrary initial flag and helper values. -/
def comparisonOutput {width : Nat} (pivot : Nat) (state : Registers width) : Registers width :=
  (state.1 ^^ decide (state.2.1.val < pivot), state.2)

private theorem oneBit_add_carry (flag carry : Bool) :
    HRS.addWord (0 : Fin (2 ^ 1))
        (if carry then HRS.incrementWord (BinaryLabelEncoding.bool.encode flag)
          else BinaryLabelEncoding.bool.encode flag) =
      BinaryLabelEncoding.bool.encode (flag ^^ carry) := by
  cases flag <;> cases carry <;> rfl

/-- A zero-high-bit extended constant adds into the low word and xor-toggles the high bit. -/
theorem gidneyPackedOffset_zero_high (width : Nat) (constant : Fin (2 ^ width))
    (state : Registers width) :
    packedOffsetOutput (prodEquiv (m := 1) (n := width) (0, constant)) state =
      (state.1 ^^ decide (2 ^ width ≤ state.2.1.val + constant.val),
        (HRS.addWord constant state.2.1, state.2.2)) := by
  apply (packingEquiv width).injective
  rw [packedOffsetOutput, Equiv.apply_symm_apply]
  simp only [gidneyPackingEquiv_apply, HRS.oneDirtyOutput]
  apply Prod.ext
  · exact (HRS.hrsAddWord_halves width 1 state.2.1 constant
      (BinaryLabelEncoding.bool.encode state.1) (0 : Fin (2 ^ 1))).trans
        (congrArg (fun high => prodEquiv (m := 1) (n := width)
          (high, HRS.addWord constant state.2.1)) (oneBit_add_carry state.1 _))
  · rfl

/-- The two compiled low-word constants cancel on every input. -/
theorem gidneyPivotOffsets_cancel (width pivot : Nat) (hpivot : pivot ≤ 2 ^ width)
    (input : Fin (2 ^ width)) :
    HRS.addWord (pivotWord width pivot) (HRS.addWord (negatedPivot width pivot) input) =
      input := by
  apply Fin.ext
  change (((input.val + (2 ^ width - pivot) % 2 ^ width) % 2 ^ width +
    pivot % 2 ^ width) % 2 ^ width) = input.val
  calc
    _ = (input.val + ((2 ^ width - pivot) + pivot)) % 2 ^ width := by
      simp only [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
    _ = (input.val + 2 ^ width) % 2 ^ width := by rw [Nat.sub_add_cancel hpivot]
    _ = input.val := by simp only [Nat.add_mod_right, Nat.mod_eq_of_lt input.isLt]

/-- A positive fitted pivot gives the exact nonnegative subtracting representative. -/
theorem gidneyNegatedPivot_val (width pivot : Nat) (hpositive : 0 < pivot) :
    (negatedPivot width pivot).val = 2 ^ width - pivot := by
  apply Nat.mod_eq_of_lt
  have := Nat.two_pow_pos width
  omega

/-- The actual extended-add/low-add/flag-X arithmetic restores the word and helper exactly. -/
theorem gidneyComparison_positive_steps (width pivot : Nat)
    (hpositive : 0 < pivot) (hpivot : pivot ≤ 2 ^ width) (state : Registers width) :
    flagFlipOutput
        (lowOffsetOutput (pivotWord width pivot)
          (packedOffsetOutput (extendedNegatedPivot width pivot) state)) =
      comparisonOutput pivot state := by
  rw [extendedNegatedPivot, gidneyPackedOffset_zero_high]
  change (!(state.1 ^^ decide (2 ^ width ≤
      state.2.1.val + (negatedPivot width pivot).val)),
      (HRS.addWord (pivotWord width pivot)
        (HRS.addWord (negatedPivot width pivot) state.2.1), state.2.2)) = _
  rw [gidneyPivotOffsets_cancel width pivot hpivot,
    gidneyNegatedPivot_val width pivot hpositive]
  apply Prod.ext
  · change (!(state.1 ^^ decide (2 ^ width ≤ state.2.1.val + (2 ^ width - pivot)))) =
      (state.1 ^^ decide (state.2.1.val < pivot))
    by_cases hlt : state.2.1.val < pivot
    · have hcarry : ¬2 ^ width ≤ state.2.1.val + (2 ^ width - pivot) := by omega
      simp only [decide_eq_false hcarry, decide_eq_true hlt, Bool.xor_false, Bool.xor_true]
    · have hcarry : 2 ^ width ≤ state.2.1.val + (2 ^ width - pivot) := by omega
      simp only [decide_eq_true hcarry, decide_eq_false hlt, Bool.xor_true, Bool.xor_false,
        Bool.not_not]
  · rfl

/-- At pivot zero, the mathematical comparator is identity for every width. -/
theorem gidneyComparison_zero (width : Nat) (state : Registers width) :
    comparisonOutput 0 state = state := by
  rcases state with ⟨flag, input, helper⟩
  simp only [comparisonOutput, Nat.not_lt_zero, decide_false, Bool.xor_false]

end

end QuantumAlg.MAU.Addition.Gidney
