/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Coordinates
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Subtraction

/-!
# Actual terminal boundary arithmetic in the original prefix word

The retained other length field is padded by the actual conjunction bit.
The full existing prefix is the only target. Later clean preparation
must prove that padding bit zero before interpreting its operand as a
natural boundary. No source word, address bit or extra system is needed.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- One original padding bit followed by the complete retained other metadata word. -/
def source (width : Nat) : Field → Word (encoding width) (ScanMetadata.addressWidth width)
  | field => ⟨fun index => if zero : index.val = 0 then conjunctionBit width
      else sourceBit width (boundaryBit width field
        ⟨index.val - 1, by
          have within := index.isLt
          unfold ScanMetadata.addressWidth at within
          omega⟩)⟩

/-- The complete actual prefix in its original most-significant-first order. -/
def target (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) :=
  ⟨prefixBit width⟩

private lemma source_distinct (width : Nat) (field : Field)
    (left right : Fin (ScanMetadata.addressWidth width))
    (same : ((source width field).bit left).wire = ((source width field).bit right).wire) :
    left = right := by
  unfold source at same
  dsimp only at same
  split_ifs at same with leftZero rightZero
  · exact Fin.ext (leftZero.trans rightZero.symm)
  · exact False.elim ((source_conjunction_ne width _).symm same)
  · exact False.elim (source_conjunction_ne width _ same)
  · have original : (boundaryBit width field
          ⟨left.val - 1, by
            have within := left.isLt
            unfold ScanMetadata.addressWidth at within
            omega⟩).wire =
        (boundaryBit width field
          ⟨right.val - 1, by
            have within := right.isLt
            unfold ScanMetadata.addressWidth at within
            omega⟩).wire := by
      apply Fin.ext
      have values := congrArg (fun wire : Fin (Scanned.encoding width).width => wire.val) same
      rw [sourceBit_wire, sourceBit_wire] at values
      exact values
    have positions := congrArg Fin.val (boundaryBit_injective width field original)
    apply Fin.ext
    dsimp only at positions
    omega

private lemma target_distinct (width : Nat)
    (left right : Fin (ScanMetadata.addressWidth width))
    (same : ((target width).bit left).wire = ((target width).bit right).wire) : left = right := by
  have values := congrArg Fin.val same
  change (prefixBit width left).wire.val = (prefixBit width right).wire.val at values
  rw [prefixBit_wire, prefixBit_wire] at values
  apply Fin.ext
  omega

private lemma separate (width : Nat) (field : Field)
    (left right : Fin (ScanMetadata.addressWidth width)) :
    ((source width field).bit left).wire ≠ ((target width).bit right).wire := by
  unfold source target
  dsimp only
  split
  · exact (prefix_conjunction_ne width right).symm
  · exact source_prefix_ne width _ right

/-- The full native adder is placed on these same original physical source and prefix systems. -/
def placement (width : Nat) (field : Field) :
    Addition.TTK.WordPlacement (encoding width) (ScanMetadata.addressWidth width) where
  addend := source width field
  target := target width
  addendDistinct := source_distinct width field
  targetDistinct := target_distinct width
  separate := separate width field
  onto := encoding_surjective width

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary
