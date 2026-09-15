/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout

/-!
# Actual bit lenses of measured-arithmetic data ports

X is the original trailing Work2 input, A occupies only the first n
Work1 positions, and Y is the existing word following the shared EEA
frame. All lenses use the physical big-endian order. None includes
the retained padding, length, or control bits
[LYL+26, sec_point_add/sec_point_add.tex:51-105].
-/

namespace QuantumAlg.MeasuredUncompute.FramePorts

noncomputable section

open ProductPlacement MAU.Inversion

/-- The large Work1 port occupies its first n physical wires. -/
def accumulator (width : Nat) : EncodedBit.Word (frameEncoding width) width :=
  ⟨fun index => BinaryLabelEncoding.prodLeftBit (SharedEEA.encoding width)
    (BinaryLabelEncoding.finIdentity width)
    (SharedEEA.firstWordBit width ⟨index.val, by have bound := index.isLt; omega⟩)⟩

/-- The original Work2 data port follows its three leading padding bits. -/
def input (width : Nat) : EncodedBit.Word (frameEncoding width) width :=
  ⟨fun index => BinaryLabelEncoding.prodLeftBit (SharedEEA.encoding width)
    (BinaryLabelEncoding.finIdentity width)
    (SharedEEA.secondWordBit width ⟨3 + index.val, by have bound := index.isLt; omega⟩)⟩

/-- The existing Y word follows the complete two-word shared arithmetic frame. -/
def numerator (width : Nat) : EncodedBit.Word (frameEncoding width) width :=
  ⟨fun index => BinaryLabelEncoding.prodRightBit (SharedEEA.encoding width)
    (BinaryLabelEncoding.finIdentity width) (BinaryLabelEncoding.finIdentityBit width index)⟩

theorem accumulator_wire (width : Nat) (index : Fin width) :
    ((accumulator width).bit index).wire.val = index.val := rfl

theorem input_wire (width : Nat) (index : Fin width) :
    ((input width).bit index).wire.val = width + 6 + index.val := by
  change width + 3 + (3 + index.val) = _
  omega

theorem numerator_wire (width : Nat) (index : Fin width) :
    ((numerator width).bit index).wire.val =
      2 * width + 6 + tailWidth width + index.val := by
  change (SharedEEA.encoding width).width + index.val = _
  rw [SharedEEA.encoding_width]
  unfold tailWidth
  omega

theorem accumulator_read (width : Nat) (index : Fin width) (state : Frame width) :
    ((accumulator width).bit index).get state = state.1.firstWord.getMsbD index.val :=
  SharedEEA.firstWordBit_get width _ state.1

theorem input_read (width : Nat) (index : Fin width) (state : Frame width) :
    ((input width).bit index).get state = state.1.secondWord.getMsbD (3 + index.val) :=
  SharedEEA.secondWordBit_get width _ state.1

theorem numerator_read (width : Nat) (index : Fin width) (state : Frame width) :
    ((numerator width).bit index).get state = state.2.val.testBit index.rev.val := by
  change state.2.val.testBit (width - 1 - index.val) = _
  apply congrArg (fun bit => state.2.val.testBit bit)
  rw [Fin.val_rev]
  omega

/-- Every wire inside A has a unique actual identity. -/
theorem accumulator_distinct (width : Nat) (left right : Fin width) (different : left ≠ right) :
    ((accumulator width).bit left).wire ≠ ((accumulator width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [accumulator_wire, accumulator_wire] at values
  exact different (Fin.ext values)

/-- Every wire inside Y has a unique actual identity. -/
theorem numerator_distinct (width : Nat) (left right : Fin width) (different : left ≠ right) :
    ((numerator width).bit left).wire ≠ ((numerator width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [numerator_wire, numerator_wire] at values
  exact different (Fin.ext (by omega))

/-- No measured-word wire aliases any large-workspace wire. -/
theorem accumulator_numerator_ne (width : Nat) (left right : Fin width) :
    ((accumulator width).bit left).wire ≠ ((numerator width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [accumulator_wire, numerator_wire] at values
  have bound := left.isLt
  omega

/-- The divisor/input word is separate from both large-word reuse ports. -/
theorem input_separate (width : Nat) (index other : Fin width) :
    ((input width).bit index).wire ≠ ((accumulator width).bit other).wire ∧
      ((input width).bit index).wire ≠ ((numerator width).bit other).wire := by
  have inputBound := index.isLt
  have otherBound := other.isLt
  constructor
  · intro same
    have values := congrArg Fin.val same
    rw [input_wire, accumulator_wire] at values
    omega
  · intro same
    have values := congrArg Fin.val same
    rw [input_wire, numerator_wire] at values
    omega

end

end QuantumAlg.MeasuredUncompute.FramePorts
