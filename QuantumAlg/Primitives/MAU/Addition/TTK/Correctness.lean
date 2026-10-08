/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Xor.Stages
import all QuantumAlg.Primitives.MAU.Addition.TTK.Xor.Chain
import all QuantumAlg.Primitives.MAU.Addition.TTK.Carry
import all QuantumAlg.Primitives.MAU.Addition.TTK.Uncompute
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Exact low-word correctness of the TTK adder

The six actual gate sweeps implement low-word addition for every word width.
The carry boundary and finishing lemmas also support the explicit overflow
interface without duplicating the operand proof
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec
open Nat.BinaryArithmetic

/-- The first three operand sweeps store the canonical carries in the addend. -/
theorem ttkCarryBoundary (n : Nat) (original : Registers n) :
    (∀ i : Fin n, (leftBit n i).get
      (stepList (carryGates n)
        (stepList (descendingXorGates n) (stepList (preXorGates n) original))) =
      (original.1.val.testBit i.val ^^
        natAddCarry original.1.val original.2.val i.val)) ∧
    (∀ i : Fin n, (rightBit n i).get
      (stepList (carryGates n)
        (stepList (descendingXorGates n) (stepList (preXorGates n) original))) =
      if i.val = 0 then original.2.val.testBit i.val
      else (original.2.val.testBit i.val ^^ original.1.val.testBit i.val)) := by
  apply ttkCarrySweep n original
    (stepList (descendingXorGates n) (stepList (preXorGates n) original))
  · intro i
    rw [(ttkDescendingXor n (stepList (preXorGates n) original)).1 i]
    simp only [ttkPreXor_left]
    simp only [ttkLeftBit_get, previousBit]
  · intro i
    rw [(ttkDescendingXor n (stepList (preXorGates n) original)).2 i,
      ttkPreXor_right]
    simp only [ttkRightBit_get, ttkLeftBit_get]

/-- The final three sweeps restore the addend and produce the low sum exactly. -/
theorem ttkFinishCarry (n : Nat) (original s : Registers n)
    (hleft : ∀ i : Fin n, (leftBit n i).get s =
      (original.1.val.testBit i.val ^^
        natAddCarry original.1.val original.2.val i.val))
    (hright : ∀ i : Fin n, (rightBit n i).get s =
      if i.val = 0 then original.2.val.testBit i.val
      else (original.2.val.testBit i.val ^^ original.1.val.testBit i.val)) :
    stepList (finalXorGates n)
      (stepList (ascendingXorGates n) (stepList (descendingUncomputeGates n) s)) =
      lowOutput original := by
  have hu := ttkUncomputeSweep n original s hleft hright
  have ha := ttkAscendingXor n original (stepList (descendingUncomputeGates n) s)
    (by
      intro i
      simpa only [ttkLeftBit_get, previousBit] using hu.1 i)
  have hl : ∀ i : Fin n, (leftBit n i).get
      (stepList (finalXorGates n)
        (stepList (ascendingXorGates n) (stepList (descendingUncomputeGates n) s))) =
      original.1.val.testBit i.val := by
    intro i
    rw [ttkFinalXor_left, ha.1 i, ttkLeftBit_get]
  have hr : ∀ i : Fin n, (rightBit n i).get
      (stepList (finalXorGates n)
        (stepList (ascendingXorGates n) (stepList (descendingUncomputeGates n) s))) =
      (original.1.val + original.2.val).testBit i.val := by
    intro i
    rw [ttkFinalXor_right, ha.2 i, hu.2 i, ha.1 i, ttkLeftBit_get,
      testBit_add_eq_xor3]
    exact (Bool.xor_comm _ _).trans (Bool.xor_assoc _ _ _).symm
  apply Prod.ext
  · apply Nat.FixedWidth.word_eq_of_testBit_eq (width := n)
    intro i
    simpa only [ttkLeftBit_get, lowOutput] using hl i
  · apply Nat.FixedWidth.word_eq_of_testBit_eq (width := n)
    intro i
    have hmod : ((original.1.val + original.2.val) % 2 ^ n).testBit i.val =
        (original.1.val + original.2.val).testBit i.val := by
      rw [Nat.testBit_mod_two_pow]
      simp [i.isLt]
    simpa only [ttkRightBit_get, lowOutput, hmod] using hr i

/-- The literal six-stage gate list implements low-word addition for all widths. -/
theorem ttkLowRipple_step (n : Nat) (original : Registers n) :
    stepList (lowRippleGates n) original = lowOutput original := by
  have h := ttkCarryBoundary n original
  simpa only [lowRippleGates, stepList_append] using
    ttkFinishCarry n original
      (stepList (carryGates n)
        (stepList (descendingXorGates n) (stepList (preXorGates n) original))) h.1 h.2

/-- The compiled no-workspace circuit realizes the independent low-word sum. -/
theorem ttkLowRipple_realizes_addition (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (lowRippleProgram n) lowOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (lowRippleGates n) (ttkLowRipple_step n)

end

end QuantumAlg.MAU.Addition.TTK
