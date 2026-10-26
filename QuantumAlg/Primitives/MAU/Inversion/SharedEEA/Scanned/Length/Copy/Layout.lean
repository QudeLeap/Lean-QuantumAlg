/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources

/-!
# Three actual length-copy controls with only original dirty Iter

The retained active flag is original Ctrl or the high existing address bit.
The other controls are the original conjunction and one low prefix bit.
An actual original length-field bit is the arbitrary XOR target. All
physical source, target and borrowed-work separations are explicit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private def highIndex (width : Nat) : Fin (ScanMetadata.addressWidth width) :=
  ⟨0, by unfold ScanMetadata.addressWidth; omega⟩

/-- The static choice uses an existing address latch or the retained original control. -/
def active (width : Nat) (poolFlag : Bool) : EncodedBit (encoding width) :=
  if poolFlag then addressBit width (highIndex width)
  else sourceBit width (SharedEEA.controlBit width)

/-- Copy only the original low metadata width, in least-significant-first order. -/
def dataBit (width : Nat) (bit : Fin width.size) : EncodedBit (encoding width) :=
  prefixBit width bit.rev.succ

/-- The actual original target bit retains the original length word's finite XOR convention. -/
def targetBit (width : Nat) (field : Field) (bit : Fin width.size) :
    EncodedBit (encoding width) :=
  sourceBit width (outputBit width field bit)

private lemma active_conjunction (width : Nat) (poolFlag : Bool) :
    (active width poolFlag).wire ≠ (conjunctionBit width).wire := by
  cases poolFlag with
  | false => exact source_conjunction_ne width _
  | true => exact address_conjunction_ne width _

private lemma active_data (width : Nat) (poolFlag : Bool) (bit : Fin width.size) :
    (active width poolFlag).wire ≠ (dataBit width bit).wire := by
  cases poolFlag with
  | false => exact source_prefix_ne width _ _
  | true => exact address_prefix_ne width _ _

private lemma active_target (width : Nat) (poolFlag : Bool) (field : Field)
    (bit : Fin width.size) : (active width poolFlag).wire ≠ (targetBit width field bit).wire := by
  cases poolFlag with
  | true => exact (source_address_ne width _ _).symm
  | false =>
      apply source_source_ne
      intro same
      have values := congrArg Fin.val same
      have within := bit.rev.isLt
      cases field <;>
        simp only [outputBit, SharedEEA.coefficientLengthBit_wire,
          SharedEEA.divisorLengthBit_wire, SharedEEA.controlBit_wire] at values <;> omega

private lemma active_work (width : Nat) (poolFlag : Bool) :
    (active width poolFlag).wire ≠ (sourceBit width (SharedEEA.iterationBit width)).wire := by
  cases poolFlag with
  | true => exact (source_address_ne width _ _).symm
  | false =>
      apply source_source_ne
      intro same
      have values := congrArg Fin.val same
      rw [SharedEEA.controlBit_wire, SharedEEA.iterationBit_wire] at values
      omega

private def controls (width : Nat) (poolFlag : Bool) (bit : Fin width.size) :
    Fin 3 → EncodedBit (encoding width) :=
  Fin.cases (active width poolFlag)
    (Fin.cases (conjunctionBit width) (fun _index : Fin 1 => dataBit width bit))

private lemma controls_distinct (width : Nat) (poolFlag : Bool) (bit : Fin width.size) :
    Function.Injective (fun index => (controls width poolFlag bit index).wire) := by
  intro left right same
  fin_cases left <;> fin_cases right
  · rfl
  · exact False.elim (active_conjunction width poolFlag same)
  · exact False.elim (active_data width poolFlag bit same)
  · exact False.elim (active_conjunction width poolFlag same.symm)
  · rfl
  · exact False.elim ((prefix_conjunction_ne width bit.rev.succ).symm same)
  · exact False.elim (active_data width poolFlag bit same.symm)
  · exact False.elim (prefix_conjunction_ne width bit.rev.succ same)
  · rfl

/-- Every one of the three source controls is an original physical system; Iter is arbitrary. -/
def layout (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size) :
    Word.OneDirtyLayout (encoding := encoding width) 3 where
  source := ⟨controls width poolFlag bit⟩
  output := targetBit width field bit
  work := sourceBit width (SharedEEA.iterationBit width)
  source_injective := controls_distinct width poolFlag bit
  source_output_ne := by
    intro index
    fin_cases index
    · exact active_target width poolFlag field bit
    · exact (source_conjunction_ne width _).symm
    · exact (source_prefix_ne width _ _).symm
  source_work_ne := by
    intro index
    fin_cases index
    · exact active_work width poolFlag
    · exact (source_conjunction_ne width _).symm
    · exact (source_prefix_ne width _ _).symm
  work_output_ne := source_source_ne width _ _ (LengthCoordinates.work_output_ne width field bit)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy
