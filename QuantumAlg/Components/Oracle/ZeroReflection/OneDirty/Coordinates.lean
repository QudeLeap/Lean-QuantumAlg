/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.ZeroReadout
import all QuantumAlg.Components.BinaryLabelEncoding

/-!
# Literal source-word and one-dirty-wire coordinates for zero reflection

The source word occupies the first physical positions in its existing
big-endian order. A single arbitrary Boolean work value occupies the final
position. Existing product-encoding bit lenses provide the exact identities,
readouts and flips; no arbitrary same-cardinality equivalence is used.
-/

namespace QuantumAlg.ZeroReflection.OneDirty

open EncodedBit.Word

noncomputable section

/-- Original source basis label and one arbitrary work-bit value. -/
abbrev Data (controls : Nat) := Fin (2 ^ (controls + 1)) × Bool

/-- The existing product encoding, with the source first and work last. -/
def encoding (controls : Nat) : BinaryLabelEncoding (Data controls) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity (controls + 1))
    BinaryLabelEncoding.bool

/-- Lift the original source position, without changing its physical identity. -/
def sourceBit (controls : Nat) (index : Fin (controls + 1)) : EncodedBit (encoding controls) :=
  BinaryLabelEncoding.prodLeftBit (BinaryLabelEncoding.finIdentity (controls + 1))
    BinaryLabelEncoding.bool (BinaryLabelEncoding.finIdentityBit (controls + 1) index)

/-- The last physical position stores the one arbitrary work bit. -/
def workBit (controls : Nat) : EncodedBit (encoding controls) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity (controls + 1))
    BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit

/-- Every lifted source position has precisely its original physical index. -/
theorem sourceBit_wire_val (controls : Nat) (index : Fin (controls + 1)) :
    (sourceBit controls index).wire.val = index.val := rfl

/-- The work wire is the single position immediately after the source. -/
theorem workBit_wire_val (controls : Nat) :
    (workBit controls).wire.val = controls + 1 := rfl

/-- Reading a lifted source position reads that exact original source bit. -/
theorem sourceBit_get (controls : Nat) (index : Fin (controls + 1)) (state : Data controls) :
    (sourceBit controls index).get state =
      (BinaryLabelEncoding.finIdentityBit (controls + 1) index).get state.1 := rfl

/-- The work readout is the actual arbitrary Boolean supplied in the input. -/
theorem workBit_get (controls : Nat) (state : Data controls) :
    (workBit controls).get state = state.2 := rfl

/-- The first source bit is the phase target; the remaining source bits are controls. -/
def layout (controls : Nat) : OneDirtyLayout (encoding := encoding controls) controls where
  source := ⟨fun index => sourceBit controls index.succ⟩
  output := sourceBit controls 0
  work := workBit controls
  source_injective := by
    intro left right same
    have values := congrArg (fun wire : Fin (encoding controls).width => wire.val) same
    change left.val + 1 = right.val + 1 at values
    exact Fin.ext (by omega)
  source_output_ne := by
    intro index same
    have values := congrArg (fun wire : Fin (encoding controls).width => wire.val) same
    change index.val + 1 = 0 at values
    omega
  source_work_ne := by
    intro index same
    have values := congrArg (fun wire : Fin (encoding controls).width => wire.val) same
    change index.val + 1 = controls + 1 at values
    omega
  work_output_ne := by
    intro same
    have values := congrArg (fun wire : Fin (encoding controls).width => wire.val) same
    change controls + 1 = 0 at values
    omega

/-- The layout's reflected-zero condition is exactly the original source label being zero. -/
theorem reflectedZero_iff (controls : Nat) (state : Data controls) :
    (layout controls).reflectedZero state ↔ state.1 = 0 := by
  rw [← BinaryLabelEncoding.finIdentity_all_zero_iff (controls + 1) state.1]
  change ((∀ index : Fin controls,
      (BinaryLabelEncoding.finIdentityBit (controls + 1) index.succ).get state.1 = false) ∧
    (BinaryLabelEncoding.finIdentityBit (controls + 1) 0).get state.1 = false) ↔ _
  constructor
  · rintro ⟨tail, head⟩ index
    exact Fin.cases head tail index
  · intro allBits
    exact ⟨fun index => allBits index.succ, allBits 0⟩

end

end QuantumAlg.ZeroReflection.OneDirty
