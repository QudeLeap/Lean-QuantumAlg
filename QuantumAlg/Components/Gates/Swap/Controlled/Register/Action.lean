/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled.Register
import all QuantumAlg.Components.Gates.Swap.Controlled.Register
import all QuantumAlg.Components.Gates.Swap.Controlled.Qubits
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Actual coordinate action of an ordered controlled register exchange

The actual pair list preserves the control. Distinct word positions exchange
their two original values exactly when that original control is one.
-/

namespace QuantumAlg.Gate.ControlledRegisterSwap

noncomputable section

private lemma left_injective (width : Nat) : Function.Injective (left width) := by
  intro first second same
  have equal := congrArg Fin.val same
  change 1 + first.val = 1 + second.val at equal
  exact Fin.ext (by omega)

private lemma right_injective (width : Nat) : Function.Injective (right width) := by
  intro first second same
  have equal := congrArg Fin.val same
  change 1 + width + first.val = 1 + width + second.val at equal
  exact Fin.ext (by omega)

private lemma words_disjoint (width : Nat) (first second : Fin width) :
    left width first ≠ right width second := by
  intro same
  have equal := congrArg Fin.val same
  change 1 + first.val = 1 + width + second.val at equal
  omega

private lemma pair_control (width : Nat) (index : Fin width)
    (basis : Fin (1 + (width + width)) → Fin 2) :
    pairPermutation width index basis (control width) = basis (control width) :=
  ControlledSwap.action_control _ _ _ (control_left width index) (control_right width index) basis

private lemma pair_left (width : Nat) (selected index : Fin width)
    (basis : Fin (1 + (width + width)) → Fin 2) :
    pairPermutation width selected basis (left width index) =
      if basis (control width) = 0 then basis (left width index)
      else if index = selected then basis (right width index) else basis (left width index) := by
  change ControlledSwap.qubitAction _ _ _ basis _ = _
  unfold ControlledSwap.qubitAction
  by_cases zero : basis (control width) = 0
  · rw [if_pos zero, if_pos zero]
  · rw [if_neg zero, if_neg zero]
    by_cases same : index = selected
    · subst index
      rw [if_pos rfl, Equiv.swap_apply_left]
    · rw [if_neg same, Equiv.swap_apply_of_ne_of_ne
        (fun equal => same (left_injective width equal)) (words_disjoint width index selected)]

private lemma pair_right (width : Nat) (selected index : Fin width)
    (basis : Fin (1 + (width + width)) → Fin 2) :
    pairPermutation width selected basis (right width index) =
      if basis (control width) = 0 then basis (right width index)
      else if index = selected then basis (left width index) else basis (right width index) := by
  change ControlledSwap.qubitAction _ _ _ basis _ = _
  unfold ControlledSwap.qubitAction
  by_cases zero : basis (control width) = 0
  · rw [if_pos zero, if_pos zero]
  · rw [if_neg zero, if_neg zero]
    by_cases same : index = selected
    · subst index
      rw [if_pos rfl, Equiv.swap_apply_right]
    · rw [if_neg same, Equiv.swap_apply_of_ne_of_ne
        (words_disjoint width selected index).symm
        (fun equal => same (right_injective width equal))]

/-- Every coordinate of a duplicate-free pair list has its exact original-value action. -/
lemma sequence_coordinates (width : Nat) (indices : List (Fin width))
    (unique : indices.Nodup) (basis : Fin (1 + (width + width)) → Fin 2) :
    sequencePermutation width indices basis (control width) = basis (control width) ∧
      ∀ index : Fin width,
        (sequencePermutation width indices basis (left width index) =
          if basis (control width) = 0 then basis (left width index)
          else if index ∈ indices then basis (right width index)
          else basis (left width index)) ∧
        (sequencePermutation width indices basis (right width index) =
          if basis (control width) = 0 then basis (right width index)
          else if index ∈ indices then basis (left width index)
          else basis (right width index)) := by
  induction indices with
  | nil =>
      constructor
      · rfl
      · intro index
        simp only [Fin.isValue, List.not_mem_nil, ↓reduceIte, ite_self]
        exact ⟨rfl, rfl⟩
  | cons selected rest ih =>
      obtain ⟨absent, uniqueRest⟩ := List.nodup_cons.mp unique
      obtain ⟨unchanged, values⟩ := ih uniqueRest
      let restBasis : Fin (1 + (width + width)) → Fin 2 :=
        sequencePermutation width rest basis
      have fixed : restBasis (control width) = basis (control width) := unchanged
      constructor
      · exact (pair_control width selected restBasis).trans fixed
      · intro index
        have atLeft := pair_left width selected index restBasis
        have atRight := pair_right width selected index restBasis
        have oldLeft : restBasis (left width index) =
            if basis (control width) = 0 then basis (left width index)
            else if index ∈ rest then basis (right width index) else basis (left width index) :=
          (values index).1
        have oldRight : restBasis (right width index) =
            if basis (control width) = 0 then basis (right width index)
            else if index ∈ rest then basis (left width index) else basis (right width index) :=
          (values index).2
        constructor
        · refine atLeft.trans ?_
          rw [fixed, oldLeft, oldRight]
          by_cases zero : basis (control width) = 0
          · simp [zero]
            rfl
          · by_cases same : index = selected
            · subst index
              simp [zero, absent]
              rfl
            · simp [zero, same]
              rfl
        · refine atRight.trans ?_
          rw [fixed, oldRight, oldLeft]
          by_cases zero : basis (control width) = 0
          · simp [zero]
            rfl
          · by_cases same : index = selected
            · subst index
              simp [zero, absent]
              rfl
            · simp [zero, same]
              rfl
end

end QuantumAlg.Gate.ControlledRegisterSwap
