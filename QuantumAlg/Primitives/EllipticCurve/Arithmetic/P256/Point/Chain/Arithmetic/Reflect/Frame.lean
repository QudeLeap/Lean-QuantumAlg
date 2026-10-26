/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl

/-!
# Original two payload words and full retained reflection complement

The constant workspace is the original Work1 payload and the target is
the original Work2 payload. Numerical bits keep their physical identities.
The whole remaining frame includes the initialized EEA metadata, all pool
positions, numerator, C, N and arbitrary W. No gate word is expanded here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic

namespace Reflect

noncomputable section

open EncodedBit

private def word (port : WordPort) : EncodedBit.Word Frame.encoding 256 :=
  ⟨fun index => port.bit index.rev⟩

private lemma word_distinct (port : WordPort) :
    Function.Injective (fun index => ((word port).bit index).wire) := by
  intro first second same
  exact Fin.rev_injective (WordPort.bit_index_injective port same)

def words : MAU.Addition.TTK.WordPlacement Frame.encoding 256 where
  addend := word .work1
  target := word .work2
  addendDistinct := word_distinct .work1
  targetDistinct := word_distinct .work2
  separate := fun first second => WordPort.bit_ports_disjoint .work1 .work2 (by decide)
    first.rev second.rev
  onto := Frame.encoding_surjective

def subsystem := words.subsystem

private def complementIndex {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (selected : WireSubsystem source target) (bit : selected.Complement) :
    Fin selected.complementWidth := Fintype.equivFin selected.Complement bit

private lemma complementIndex_injective {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (selected : WireSubsystem source target) : Function.Injective (complementIndex selected) :=
  (Fintype.equivFin selected.Complement).injective

attribute [local irreducible] WireSubsystem.complementWidth

private lemma source_onto : Function.Surjective (MAU.Addition.TTK.encoding 256).encode :=
  MAU.Addition.TTK.WordPlacement.source_onto (width := 256)

abbrev Rest := Fin (2 ^ subsystem.complementWidth)

def restEncoding : BinaryLabelEncoding Rest := .finIdentity subsystem.complementWidth

def layout : FullPlacement (.prod (MAU.Addition.TTK.encoding 256) restEncoding)
    Frame.encoding :=
  subsystem.full source_onto Frame.encoding_surjective

private lemma afterPayload_outside (bit : EncodedBit Frame.encoding)
    (afterPayload : 515 ≤ bit.wire.val) : bit.wire ∉ Set.range subsystem.wires := by
  rintro ⟨index, same⟩
  obtain ⟨selected, rfl⟩ :=
    (finSumFinEquiv : Fin 256 ⊕ Fin 256 ≃ Fin (256 + 256)).surjective index
  cases selected with
  | inl position =>
      have location := wordPairSubsystem_left words.addend words.target
        words.addendDistinct words.targetDistinct words.separate position
      change subsystem.wires (finSumFinEquiv (Sum.inl position)) =
        (Frame.work1Bit position.rev).wire at location
      have values := congrArg Fin.val (location.symm.trans same)
      rw [Frame.work1Bit_wire] at values
      have within := position.rev.isLt
      omega
  | inr position =>
      have location := wordPairSubsystem_right words.addend words.target
        words.addendDistinct words.targetDistinct words.separate position
      change subsystem.wires (finSumFinEquiv (Sum.inr position)) =
        (Frame.work2Bit position.rev).wire at location
      have values := congrArg Fin.val (location.symm.trans same)
      rw [Frame.work2Bit_wire] at values
      have within := position.rev.isLt
      omega

private def restBit (bit : EncodedBit Frame.encoding)
    (outside : bit.wire ∉ Set.range subsystem.wires) : EncodedBit restEncoding :=
  BinaryLabelEncoding.finIdentityBit subsystem.complementWidth
    (complementIndex subsystem ⟨bit.wire, outside⟩)

private lemma control_outside :
    Native.BorrowedControl.flag.wire ∉ Set.range subsystem.wires :=
  afterPayload_outside _ (by rw [Native.BorrowedControl.flag_wire]; omega)

private lemma borrowed_outside : Frame.workBit.wire ∉ Set.range subsystem.wires :=
  afterPayload_outside _ (by rw [Frame.workBit_wire]; omega)

def controlBit : EncodedBit restEncoding :=
  restBit Native.BorrowedControl.flag control_outside

def borrowedBit : EncodedBit restEncoding :=
  restBit Frame.workBit borrowed_outside

lemma controlBit_get (state : Frame.Raw) :
    controlBit.get (layout.grouping state).2 = Native.BorrowedControl.flag.get state :=
  subsystem.full_complement_read source_onto Frame.encoding_surjective
    Native.BorrowedControl.flag control_outside state

lemma borrowedBit_get (state : Frame.Raw) :
    borrowedBit.get (layout.grouping state).2 = Frame.workBit.get state :=
  subsystem.full_complement_read source_onto Frame.encoding_surjective
    Frame.workBit borrowed_outside state

lemma control_borrowed_ne : controlBit.wire ≠ borrowedBit.wire := by
  intro same
  have sameIndex :
      complementIndex subsystem
          ⟨Native.BorrowedControl.flag.wire, control_outside⟩ =
        complementIndex subsystem ⟨Frame.workBit.wire, borrowed_outside⟩ := same
  have actual := congrArg Subtype.val (complementIndex_injective subsystem sameIndex)
  have values := congrArg Fin.val actual
  rw [Native.BorrowedControl.flag_wire, Frame.workBit_wire] at values
  omega

end

end Reflect

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic
