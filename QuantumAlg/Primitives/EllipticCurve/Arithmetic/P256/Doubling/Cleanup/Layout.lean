/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Carry

/-!
# Original-wire high-word comparison for doubling cleanup

The actual comparison reads the upper 255 target bits, toggles the original
reduction flag and borrows 253 original source bits. The original low target
bit and a distinct existing source bit remain outside this subsystem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

abbrev highWidth : Nat := 255

private lemma high_onto :
    Function.Surjective (MAU.Addition.HRS.carryEncoding highWidth).encode :=
  ModularAddition.carry_onto highWidth

/-- Its high-word overflow is the comparison against half the odd complement. -/
def comparisonConstant : Fin (2 ^ highWidth) :=
  ⟨2 ^ highWidth - complement / 2, by norm_num [complement]⟩

/-- Input occupies original target positions 256 through 510; output is the original flag. -/
def comparisonPosition (index : Fin (MAU.Addition.HRS.carryEncoding highWidth).width) :
    Fin encoding.width :=
  ⟨if index.val < highWidth then width + index.val
    else if index.val = highWidth then width + width else index.val - highWidth - 1, by
      have bounded := index.isLt
      change index.val < highWidth + (highWidth - 2 + 1) at bounded
      change (if index.val < highWidth then width + index.val
        else if index.val = highWidth then width + width else index.val - highWidth - 1) <
          width + width + 1
      have widths : width = highWidth + 1 := rfl
      split_ifs <;> omega⟩

lemma comparisonPosition_injective : Function.Injective comparisonPosition := by
  intro left right same
  have positions := congrArg Fin.val same
  have leftBound := left.isLt
  have rightBound := right.isLt
  change left.val < highWidth + (highWidth - 2 + 1) at leftBound
  change right.val < highWidth + (highWidth - 2 + 1) at rightBound
  apply Fin.ext
  dsimp only [comparisonPosition] at positions
  have widths : width = highWidth + 1 := rfl
  split_ifs at positions <;> omega

def comparisonSubsystem : WireSubsystem (MAU.Addition.HRS.carryEncoding highWidth) encoding where
  wires := ⟨comparisonPosition, comparisonPosition_injective⟩

/-- One actual source bit outside all input, output and dirty comparison wires. -/
def controlWork : EncodedBit encoding := addendBit ⟨2, by decide⟩

lemma low_outside : targetLow.wire ∉ Set.range comparisonSubsystem.wires := by
  rintro ⟨source, same⟩
  have location := congrArg Fin.val same
  have bounded := source.isLt
  change source.val < highWidth + (highWidth - 2 + 1) at bounded
  change (if source.val < highWidth then width + source.val
    else if source.val = highWidth then width + width else source.val - highWidth - 1) =
      width + (width - 1 - 0) at location
  have widths : width = highWidth + 1 := rfl
  split_ifs at location <;> omega

lemma work_outside : controlWork.wire ∉ Set.range comparisonSubsystem.wires := by
  rintro ⟨source, same⟩
  have location := congrArg Fin.val same
  have bounded := source.isLt
  change source.val < highWidth + (highWidth - 2 + 1) at bounded
  change (if source.val < highWidth then width + source.val
    else if source.val = highWidth then width + width else source.val - highWidth - 1) =
      width - 1 - 2 at location
  have widths : width = highWidth + 1 := rfl
  split_ifs at location <;> omega

lemma low_work_ne : targetLow.wire ≠ controlWork.wire := by
  intro same
  have positions := congrArg Fin.val same
  change width + (width - 1) = width - 1 - 2 at positions
  have positive : 3 ≤ width := by decide
  omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup
