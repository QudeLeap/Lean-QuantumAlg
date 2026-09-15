/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Readout

/-!
# Correctness of the first and last TTK stages

The first stage xors each non-low addend bit into the corresponding right bit.
The last stage xors every restored addend bit into its right bit. Both theorems
hold for arbitrary width and arbitrary operand states [TTK09,
qic-loglogaddition-quant.tex:290-295,315-318,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec

private def leftWord (n : Nat) : EncodedBit.Word (encoding n) n := ⟨leftBit n⟩
private def rightWord (n : Nat) : EncodedBit.Word (encoding n) n := ⟨rightBit n⟩

private def upperIndex {n : Nat} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by omega⟩

private theorem upperIndex_injective (n : Nat) :
    Function.Injective (upperIndex (n := n)) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  change i.val + 1 = j.val + 1 at hval
  omega

private def upperLeftWord (n : Nat) : EncodedBit.Word (encoding n) (n - 1) :=
  ⟨fun i => leftBit n (upperIndex i)⟩

private def upperRightWord (n : Nat) : EncodedBit.Word (encoding n) (n - 1) :=
  ⟨fun i => rightBit n (upperIndex i)⟩

/-- Stage one preserves every addend bit, for all word widths. -/
theorem ttkPreXor_left (n : Nat) (s : Registers n) (i : Fin n) :
    (leftBit n i).get (stepList (preXorGates n) s) = (leftBit n i).get s := by
  change (leftBit n i).get
    (EncodedBit.Word.xorIntoStep (upperLeftWord n) (upperRightWord n)
      (fun j => ttkLeftRight_disjoint n (upperIndex j) (upperIndex j)) s) = _
  apply EncodedBit.Word.xorIntoStep_get_observed_of_target_ne
  intro j
  exact Ne.symm (ttkLeftRight_disjoint n i (upperIndex j))

/-- Stage one changes precisely the right bits above the low bit. -/
theorem ttkPreXor_right (n : Nat) (s : Registers n) (i : Fin n) :
    (rightBit n i).get (stepList (preXorGates n) s) =
      if i.val = 0 then (rightBit n i).get s
      else ((rightBit n i).get s ^^ (leftBit n i).get s) := by
  change (rightBit n i).get
    (EncodedBit.Word.xorIntoStep (upperLeftWord n) (upperRightWord n)
      (fun j => ttkLeftRight_disjoint n (upperIndex j) (upperIndex j)) s) = _
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    apply EncodedBit.Word.xorIntoStep_get_observed_of_target_ne
    intro j
    apply ttkRightRight_disjoint
    intro h
    have hval := congrArg Fin.val h
    change j.val + 1 = i.val at hval
    omega
  · rw [if_neg hi]
    let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
    have hj : upperIndex j = i := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have h := EncodedBit.Word.xorIntoStep_get_target
      (upperLeftWord n) (upperRightWord n)
      (fun k => ttkLeftRight_disjoint n (upperIndex k) (upperIndex k)) j
      (fun k hkj => ttkRightRight_disjoint n (upperIndex k) (upperIndex j)
        (fun heq => hkj (upperIndex_injective n heq)))
      (fun k => Ne.symm (ttkLeftRight_disjoint n (upperIndex j) (upperIndex k))) s
    change (rightBit n (upperIndex j)).get
      (EncodedBit.Word.xorIntoStep (upperLeftWord n) (upperRightWord n)
        (fun k => ttkLeftRight_disjoint n (upperIndex k) (upperIndex k)) s) =
      ((rightBit n (upperIndex j)).get s ^^ (leftBit n (upperIndex j)).get s) at h
    rw [hj] at h
    exact h

/-- Stage six preserves the fully restored addend. -/
theorem ttkFinalXor_left (n : Nat) (s : Registers n) (i : Fin n) :
    (leftBit n i).get (stepList (finalXorGates n) s) = (leftBit n i).get s := by
  change (leftBit n i).get
    (EncodedBit.Word.xorIntoStep (leftWord n) (rightWord n)
      (fun j => ttkLeftRight_disjoint n j j) s) = _
  apply EncodedBit.Word.xorIntoStep_get_observed_of_target_ne
  intro j
  exact Ne.symm (ttkLeftRight_disjoint n i j)

/-- Stage six xors each addend bit into exactly its matching target bit. -/
theorem ttkFinalXor_right (n : Nat) (s : Registers n) (i : Fin n) :
    (rightBit n i).get (stepList (finalXorGates n) s) =
      ((rightBit n i).get s ^^ (leftBit n i).get s) := by
  change (rightBit n i).get
    (EncodedBit.Word.xorIntoStep (leftWord n) (rightWord n)
      (fun j => ttkLeftRight_disjoint n j j) s) = _
  exact EncodedBit.Word.xorIntoStep_get_target (leftWord n) (rightWord n)
    (fun j => ttkLeftRight_disjoint n j j) i
    (fun j hji => ttkRightRight_disjoint n j i hji)
    (fun j => Ne.symm (ttkLeftRight_disjoint n i j)) s

end

end QuantumAlg.MAU.Addition.TTK
