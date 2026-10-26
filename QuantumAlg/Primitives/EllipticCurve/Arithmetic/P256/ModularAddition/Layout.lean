/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import all QuantumAlg.Primitives.MAU.Addition.TTK.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates
import Mathlib.Tactic.FinCases

/-!
# Two quantum field words and one modular-reduction flag

The HRS carry borrows 254 existing addend bits and restores them. The other
two addend bits remain in the physical complement. No operand is read into
classical storage and no new word is allocated by this placement.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit

abbrev Registers := MAU.Addition.TTK.OverflowRegisters width

abbrev encoding : BinaryLabelEncoding Registers := MAU.Addition.TTK.overflowEncoding width

def addendBit (index : Fin width) : EncodedBit encoding :=
  MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.leftBit width index)

def targetBit (index : Fin width) : EncodedBit encoding :=
  MAU.Addition.TTK.withOverflowBit (MAU.Addition.TTK.rightBit width index)

def reductionBit : EncodedBit encoding := MAU.Addition.TTK.overflowBit width

private lemma product_onto {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (leftOnto : Function.Surjective left.encode) (rightOnto : Function.Surjective right.encode) :
    Function.Surjective (BinaryLabelEncoding.prod left right).encode := by
  intro label
  obtain ⟨⟨leftLabel, rightLabel⟩, rfl⟩ :=
    (prodEquiv (m := left.width) (n := right.width)).surjective label
  obtain ⟨leftState, rfl⟩ := leftOnto leftLabel
  obtain ⟨rightState, rfl⟩ := rightOnto rightLabel
  exact ⟨(leftState, rightState), rfl⟩

private lemma bool_onto : Function.Surjective BinaryLabelEncoding.bool.encode := by
  intro flag
  fin_cases flag
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

private lemma overflow_onto (wordWidth : Nat) :
    Function.Surjective (MAU.Addition.TTK.overflowEncoding wordWidth).encode :=
  product_onto (MAU.Addition.TTK.encoding wordWidth) BinaryLabelEncoding.bool
    (product_onto (BinaryLabelEncoding.finIdentity wordWidth)
      (BinaryLabelEncoding.finIdentity wordWidth)
      Function.surjective_id Function.surjective_id) bool_onto

private lemma carry_onto (wordWidth : Nat) :
    Function.Surjective (MAU.Addition.HRS.carryEncoding wordWidth).encode :=
  product_onto (BinaryLabelEncoding.finIdentity wordWidth)
    (BinaryLabelEncoding.finIdentity (wordWidth - 2 + 1))
    Function.surjective_id Function.surjective_id

section

-- Keep the certified fixed width symbolic while specializing the generic encoding proof.
attribute [local irreducible] width

lemma encoding_onto : Function.Surjective encoding.encode :=
  overflow_onto width

lemma carryEncoding_onto : Function.Surjective (MAU.Addition.HRS.carryEncoding width).encode :=
  carry_onto width

end

/-- HRS input is the target word, output is the existing flag, and dirty work is existing addend. -/
def carryPosition (index : Fin (MAU.Addition.HRS.carryEncoding width).width) :
    Fin encoding.width :=
  ⟨if index.val < width then width + index.val
    else if index.val = width then width + width else index.val - width - 1, by
      have bounded := index.isLt
      change index.val < width + (width - 2 + 1) at bounded
      change (if index.val < width then width + index.val
        else if index.val = width then width + width else index.val - width - 1) <
          width + width + 1
      have atLeastTwo : 2 ≤ width := by decide
      by_cases input : index.val < width
      · rw [if_pos input]
        omega
      · rw [if_neg input]
        by_cases output : index.val = width
        · rw [if_pos output]
          omega
        · rw [if_neg output]
          omega⟩

lemma carryPosition_injective : Function.Injective carryPosition := by
  intro left right same
  have positions := congrArg Fin.val same
  have leftBound := left.isLt
  have rightBound := right.isLt
  change left.val < width + (width - 2 + 1) at leftBound
  change right.val < width + (width - 2 + 1) at rightBound
  apply Fin.ext
  change (if left.val < width then width + left.val
    else if left.val = width then width + width else left.val - width - 1) =
      (if right.val < width then width + right.val
        else if right.val = width then width + width else right.val - width - 1) at positions
  have atLeastTwo : 2 ≤ width := by decide
  split_ifs at positions <;> omega

def carrySubsystem : WireSubsystem (MAU.Addition.HRS.carryEncoding width) encoding where
  wires := ⟨carryPosition, carryPosition_injective⟩

/-- The complement is the exact existing two-bit remainder of the preserved addend. -/
lemma interface_width : encoding.width = 513 := rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
