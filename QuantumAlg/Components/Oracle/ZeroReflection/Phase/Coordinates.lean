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
# Original phase and source coordinates for an internally borrowed work wire

Both control and work are distinct positions already present in the phase
register. The source keeps its original trailing positions. Existing product
bit lenses preserve the value and identity of every supplied wire; there is
no extra system and no initialization premise for the borrowed phase wire.
-/

namespace QuantumAlg.ZeroReflection.PhaseWorkspace

open EncodedBit.Word

noncomputable section

/-- Original phase and source labels in their original register order. -/
abbrev Data (phases controls : Nat) := Fin (2 ^ phases) × Fin (2 ^ (controls + 1))

/-- The existing big-endian product encoding of phase followed by source. -/
def encoding (phases controls : Nat) : BinaryLabelEncoding (Data phases controls) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity phases)
    (BinaryLabelEncoding.finIdentity (controls + 1))

/-- The source bit at its existing physical position after the phase register. -/
def sourceBit (phases controls : Nat) (index : Fin (controls + 1)) :
    EncodedBit (encoding phases controls) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity phases)
    (BinaryLabelEncoding.finIdentity (controls + 1))
    (BinaryLabelEncoding.finIdentityBit (controls + 1) index)

/-- An existing phase position, with its exact original value and physical identity. -/
def phaseBit (phases controls : Nat) (index : Fin phases) :
    EncodedBit (encoding phases controls) :=
  BinaryLabelEncoding.prodLeftBit (BinaryLabelEncoding.finIdentity phases)
    (BinaryLabelEncoding.finIdentity (controls + 1))
    (BinaryLabelEncoding.finIdentityBit phases index)

theorem sourceBit_wire_val (phases controls : Nat) (index : Fin (controls + 1)) :
    (sourceBit phases controls index).wire.val = phases + index.val := rfl

theorem phaseBit_wire_val (phases controls : Nat) (index : Fin phases) :
    (phaseBit phases controls index).wire.val = index.val := rfl

theorem sourceBit_get (phases controls : Nat) (index : Fin (controls + 1))
    (state : Data phases controls) :
    (sourceBit phases controls index).get state =
      (BinaryLabelEncoding.finIdentityBit (controls + 1) index).get state.2 := rfl

theorem phaseBit_get (phases controls : Nat) (index : Fin phases)
    (state : Data phases controls) :
    (phaseBit phases controls index).get state =
      (BinaryLabelEncoding.finIdentityBit phases index).get state.1 := rfl

/-- Every original phase wire is physically distinct from every original source wire. -/
theorem phaseBit_ne_sourceBit (phases controls : Nat) (phase : Fin phases)
    (source : Fin (controls + 1)) :
    (phaseBit phases controls phase).wire ≠ (sourceBit phases controls source).wire := by
  intro same
  have values := congrArg (fun wire : Fin (encoding phases controls).width => wire.val) same
  change phase.val = phases + source.val at values
  omega

/-- The source layout borrows exactly the selected existing phase wire. -/
def layout (phases controls : Nat) (work : Fin phases) :
    OneDirtyLayout (encoding := encoding phases controls) controls where
  source := ⟨fun index => sourceBit phases controls index.succ⟩
  output := sourceBit phases controls 0
  work := phaseBit phases controls work
  source_injective := by
    intro left right same
    have values := congrArg (fun wire : Fin (encoding phases controls).width => wire.val) same
    change phases + (left.val + 1) = phases + (right.val + 1) at values
    exact Fin.ext (by omega)
  source_output_ne := by
    intro index same
    have values := congrArg (fun wire : Fin (encoding phases controls).width => wire.val) same
    change phases + (index.val + 1) = phases + 0 at values
    omega
  source_work_ne := fun index => (phaseBit_ne_sourceBit phases controls work index.succ).symm
  work_output_ne := phaseBit_ne_sourceBit phases controls work 0

/-- The source-zero predicate reads only the original source label. -/
theorem reflectedZero_iff (phases controls : Nat) (work : Fin phases)
    (state : Data phases controls) :
    (layout phases controls work).reflectedZero state ↔ state.2 = 0 := by
  rw [← BinaryLabelEncoding.finIdentity_all_zero_iff (controls + 1) state.2]
  change ((∀ index : Fin controls,
      (BinaryLabelEncoding.finIdentityBit (controls + 1) index.succ).get state.2 = false) ∧
    (BinaryLabelEncoding.finIdentityBit (controls + 1) 0).get state.2 = false) ↔ _
  constructor
  · rintro ⟨tail, head⟩ index
    exact Fin.cases head tail index
  · intro allBits
    exact ⟨fun index => allBits index.succ, allBits 0⟩

/-- The selected external control is distinct from all source controls. -/
theorem control_source_ne (phases controls : Nat) (control work : Fin phases)
    (index : Fin controls) :
    (phaseBit phases controls control).wire ≠
      ((layout phases controls work).source.bit index).wire :=
  phaseBit_ne_sourceBit phases controls control index.succ

/-- The selected control is distinct from the source phase target. -/
theorem control_output_ne (phases controls : Nat) (control work : Fin phases) :
    (phaseBit phases controls control).wire ≠ (layout phases controls work).output.wire :=
  phaseBit_ne_sourceBit phases controls control 0

/-- Distinct original phase positions stay distinct when used as control and work. -/
theorem control_work_ne (phases controls : Nat) (control work : Fin phases)
    (different : control ≠ work) :
    (phaseBit phases controls control).wire ≠ (layout phases controls work).work.wire := by
  intro same
  apply different
  apply Fin.ext
  exact congrArg (fun wire : Fin (encoding phases controls).width => wire.val) same

end

end QuantumAlg.ZeroReflection.PhaseWorkspace
