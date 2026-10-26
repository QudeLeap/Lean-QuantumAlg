/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Restoration

/-!
# Complete original21-bit scan-pool restoration across real query arithmetic

Prefix restoration alone is insufficient for the next reused inversion.
The actual arithmetic-coordinate endpoints retain every address, prefix
and conjunction bit in the entire original pool. The same unchanged digit
controls both enable directions, so their output is retained as well.
The following exact pool equality preserves the caller's original clean
pool without adding a cleanliness premise on any other source coordinate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

private lemma originalSource_width : (MAU.Inversion.SharedEEA.encoding 256).width = 559 := by
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

lemma arithmeticInput_scanPool_update (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256))
    (lower : 559 ≤ bit.wire.val) (upper : bit.wire.val < 580)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address) :
    (pointBit (Frame.scanBit bit)).get
      (arithmeticInput stream width bounded ports source newTarget third retained address) =
    (pointBit (Frame.scanBit bit)).get
      (arithmeticInput stream width bounded ports source target third retained address) := by
  unfold arithmeticInput
  exact Enable.step_get_congr stream width bounded (pointBit (Frame.scanBit bit)) _ _
    (arithmeticInput_digit_update stream width bounded ports source target newTarget third
      retained address)
    (scanPool_target_update stream bit lower upper ports source target newTarget third
      retained address)

/-- Every physical bit of the actual shared scan pool has its original value. -/
lemma arithmeticInput_pool_update (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address) :
    (arithmeticInput stream width bounded ports source newTarget third retained address).1.1.1.2 =
      (arithmeticInput stream width bounded ports source target third retained
        address).1.1.1.2 := by
  apply Prod.ext
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have actual := arithmeticInput_scanPool_update stream width bounded
      (MAU.Inversion.SharedEEA.Scanned.addressBit 256 ⟨index, within⟩)
      (by rw [MAU.Inversion.SharedEEA.Scanned.addressBit_wire, originalSource_width]; omega)
      (by
        rw [MAU.Inversion.SharedEEA.Scanned.addressBit_wire, originalSource_width]
        change 559 + index < 580
        have limit : index < 10 := by simpa only
          [Frame.payloadWidth, NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth] using within
        omega)
      ports source target newTarget third retained address
    simpa only [pointBit_get, Frame.scanBit_get,
      MAU.Inversion.SharedEEA.Scanned.addressBit_get] using actual
  · apply Prod.ext
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      have actual := arithmeticInput_scanPool_update stream width bounded
        (MAU.Inversion.SharedEEA.Scanned.prefixBit 256 ⟨index, within⟩)
        (by rw [MAU.Inversion.SharedEEA.Scanned.prefixBit_wire, originalSource_width]; omega)
        (by
          rw [MAU.Inversion.SharedEEA.Scanned.prefixBit_wire, originalSource_width]
          change 559 + NumberTheory.SharedEEA.ScanMetadata.addressWidth 256 + index < 580
          rw [NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth]
          have limit : index < 10 := by simpa only
            [Frame.payloadWidth, NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth] using within
          omega)
        ports source target newTarget third retained address
      simpa only [pointBit_get, Frame.scanBit_get,
        MAU.Inversion.SharedEEA.Scanned.prefixBit_get] using actual
    · exact arithmeticInput_scanPool_update stream width bounded
        (MAU.Inversion.SharedEEA.Scanned.conjunctionBit 256)
        (by rw [MAU.Inversion.SharedEEA.Scanned.conjunctionBit_wire, originalSource_width]; omega)
        (by rw [MAU.Inversion.SharedEEA.Scanned.conjunctionBit_wire, originalSource_width,
          NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth]; omega)
        ports source target newTarget third retained address

/-- The next actual inversion receives the same entire clean pool as before the query body. -/
lemma arithmeticInput_cleanPool_update (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address)
    (clean : Frame.CleanPool
      (arithmeticInput stream width bounded ports source target third retained address).1) :
    Frame.CleanPool
      (arithmeticInput stream width bounded ports source newTarget third retained address).1 :=
  (arithmeticInput_pool_update stream width bounded ports source target newTarget third
    retained address).trans clean

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
