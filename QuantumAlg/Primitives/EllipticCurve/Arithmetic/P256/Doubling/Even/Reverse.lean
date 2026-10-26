/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Preservation

/-! # Complete inverse of the native increment controlled by the original low target bit -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private lemma reverse_control_congr {first second : Registers} (same : first = second) :
    targetLow.get first = targetLow.get second := congrArg targetLow.get same

private lemma reverse_source_congr {first second : Registers} (same : first = second) :
    first.1.1 = second.1.1 := congrArg (fun state : Registers => state.1.1) same

private lemma reverse_flag_congr {first second : Registers} (same : first = second) :
    first.2 = second.2 := congrArg (fun state : Registers => state.2) same

private lemma reverse_coordinates_eq {First Second Third : Type}
    {first second : (First × Second) × Third}
    (left : first.1.1 = second.1.1) (right : first.1.2 = second.1.2)
    (flag : first.2 = second.2) : first = second :=
  Prod.ext (Prod.ext left right) flag

-- Coordinate readout is transported through certified full-state equations, without native folding.
attribute [local irreducible] GateSpec.stepList evenSuffixStep

/-- The retained original low bit selects subtraction of the same high-word place value. -/
def evenSuffixReverseWordStep (length : Nat) (state : Registers) : Registers :=
  if targetLow.get state then
    ((state.1.1, ⟨(state.1.2.val + (2 ^ width - 2 ^ (width - length))) % 2 ^ width,
      Nat.mod_lt _ (Nat.two_pow_pos width)⟩), state.2)
  else state

/-- Reversal retains the same original physical control, including all dirty input labels. -/
lemma evenSuffix_reverse_control (length : Nat) (fits : length < width) (state : Registers) :
    targetLow.get (stepList (evenSuffixGates length fits).reverse state) =
      targetLow.get state := by
  let before := stepList (evenSuffixGates length fits).reverse state
  have forward : evenSuffixStep length fits before = state := by
    have inverse := stepList_reverse_stepList (evenSuffixGates length fits).reverse state
    rw [List.reverse_reverse, evenSuffixGates_step] at inverse
    exact inverse
  exact (evenSuffix_control length fits before).symm.trans (reverse_control_congr forward)

/-- Every original native instruction, including the borrowed-word repairs, is reversed. -/
lemma evenSuffix_reverse_step (length : Nat) (fits : length < width) (state : Registers) :
    stepList (evenSuffixGates length fits).reverse state =
      evenSuffixReverseWordStep length state := by
  let before := stepList (evenSuffixGates length fits).reverse state
  have forward : evenSuffixStep length fits before = state := by
    have inverse := stepList_reverse_stepList (evenSuffixGates length fits).reverse state
    rw [List.reverse_reverse, evenSuffixGates_step] at inverse
    exact inverse
  have control : targetLow.get before = targetLow.get state :=
    (evenSuffix_control length fits before).symm.trans (reverse_control_congr forward)
  have source : before.1.1 = state.1.1 :=
    (evenSuffix_addend length fits before).symm.trans (reverse_source_congr forward)
  have flag : before.2 = state.2 :=
    (evenSuffix_flag length fits before).symm.trans (reverse_flag_congr forward)
  by_cases selected : targetLow.get state = true
  · rw [evenSuffixReverseWordStep, if_pos selected]
    have beforeSelected : targetLow.get before = true := control.trans selected
    have target := evenSuffix_target_of_control length fits before beforeSelected
    rw [forward] at target
    have placeFits : 2 ^ (width - length) ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have inverse := Nat.FixedWidth.ModularSuffix.increment_inverse placeFits before.1.2.isLt
    rw [← target] at inverse
    exact reverse_coordinates_eq source (Fin.ext inverse.symm) flag
  · have disabled : targetLow.get state = false := Bool.eq_false_iff.mpr selected
    have beforeDisabled : targetLow.get before = false := control.trans disabled
    rw [evenSuffixReverseWordStep, if_neg selected]
    exact (evenSuffix_of_control_false length fits before beforeDisabled).symm.trans forward

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
