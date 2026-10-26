/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State.Metadata

/-!
# Original selector-prefix restoration through real query arithmetic

Every original prefix is in the same21-bit scan pool. The numerical
arithmetic coordinates retain that entire pool, including their three
zero flags. Both enable directions use the identical unchanged digit.
Consequently changing the actual arithmetic target preserves every
original prefix read, including the enable output itself. The complete
clean-prefix premise of paid measured unlookup is therefore preserved.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

private lemma streamInput_scan_get (stream : Fin 2)
    (bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256))
    (state : Frame.Raw) (address : Address) :
    (pointBit (Frame.scanBit bit)).get (streamInput stream state address) =
      (Frame.scanBit bit).get state := by
  rw [streamInput_eq]
  split <;> rfl

private lemma scanPool_target_update (stream : Fin 2)
    (bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256))
    (lower : 559 ≤ bit.wire.val) (upper : bit.wire.val < 580)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address) :
    (pointBit (Frame.scanBit bit)).get
      (streamInput stream (Native.arithmeticState ports source newTarget third retained) address) =
    (pointBit (Frame.scanBit bit)).get
      (streamInput stream (Native.arithmeticState ports source target third retained) address) := by
  rw [streamInput_scan_get, streamInput_scan_get]
  exact Native.arithmeticState_nonword ports (Frame.scanBit bit)
    (Native.pool_wire_nonword (Frame.scanBit bit) lower upper)
    source target third source newTarget third retained

private lemma poolPrefix_target_update (stream : Fin 2) (index : Fin 15)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address) :
    (poolPrefixBit index).get
      (streamInput stream (Native.arithmeticState ports source newTarget third retained) address) =
    (poolPrefixBit index).get
      (streamInput stream (Native.arithmeticState ports source target third retained) address) := by
  have within := index.isLt
  have position := poolPrefixBit_wire index
  by_cases first : index.val < 10
  · simp only [poolPrefixBit, dif_pos first, pointBit_wire, Frame.scanBit_wire] at position ⊢
    apply scanPool_target_update <;> omega
  · simp only [poolPrefixBit, dif_neg first, pointBit_wire, Frame.scanBit_wire] at position ⊢
    apply scanPool_target_update <;> omega

/-- The two actual arithmetic endpoints have the same original complete digit. -/
lemma arithmeticInput_digit_update (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address) (index : Fin (width + 1)) :
    (Enable.digitBit stream width bounded index).get
      (streamInput stream (Native.arithmeticState ports source newTarget third retained) address) =
    (Enable.digitBit stream width bounded index).get
      (streamInput stream (Native.arithmeticState ports source target third retained) address) := by
  refine Fin.cases ?_ (fun index => ?_) index
  · change (streamBit stream).get _ = (streamBit stream).get _
    rw [streamInput_streamBit, streamInput_streamBit]
    exact Native.arithmeticState_complement ports Frame.pointControlBit
      (Placement.suffix_outside ports Frame.pointControlBit Frame.pointControlBit_wire.ge)
      source target third source newTarget third retained
  · change (addressBit ⟨index.val, by omega⟩).get _ =
      (addressBit ⟨index.val, by omega⟩).get _
    simp only [addressBit_get, streamInput_address]

/-- The real native target update preserves all fifteen original pool-prefix readouts. -/
lemma arithmeticInput_prefix_update (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address) (index : Fin 15) :
    (poolPrefixBit index).get
      (arithmeticInput stream width bounded ports source newTarget third retained address) =
    (poolPrefixBit index).get
      (arithmeticInput stream width bounded ports source target third retained address) := by
  unfold arithmeticInput
  exact Enable.step_get_congr stream width bounded (poolPrefixBit index) _ _
    (arithmeticInput_digit_update stream width bounded ports source target newTarget third
      retained address)
    (poolPrefix_target_update stream index ports source target newTarget third retained address)

/-- Both full and split unlookup prefixes keep the exact original clean-region obligation. -/
lemma arithmeticInput_clean_update (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (prefixWidth : Nat) (prefixBound : prefixWidth ≤ 15) (depth : Nat)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address)
    (clean : (selector stream prefixWidth prefixBound).CleanFrom depth
      (arithmeticInput stream width bounded ports source target third retained address)) :
    (selector stream prefixWidth prefixBound).CleanFrom depth
      (arithmeticInput stream width bounded ports source newTarget third retained address) := by
  intro index later
  have original := clean index later
  change (poolPrefixBit ⟨index.val, by omega⟩).get _ = false at original ⊢
  rw [arithmeticInput_prefix_update stream width bounded ports source target newTarget third
    retained address]
  exact original

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
