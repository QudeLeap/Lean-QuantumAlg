/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Coordinates
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Update

/-! # Affine point boundary and selected digit after source feeding -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

attribute [local irreducible] modulus sourceBlank Inversion.Seed.blank

private lemma raw_digit_flags_address
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (bit : Fin (width + 1))
    (first last : Raw) (flags : first.1.2 = last.1.2) (address : first.2 = last.2) :
    (Enable.digitBit stream width bounded bit).get first =
      (Enable.digitBit stream width bounded bit).get last := by
  cases bit using Fin.cases with
  | zero =>
      change (streamBit stream).get first = (streamBit stream).get last
      unfold streamBit
      split
      · exact congrArg (fun controls : Frame.Controls => controls.1) flags
      · exact congrArg (fun controls : Frame.Controls => controls.2.2) flags
  | succ bit =>
      change (addressBit ⟨bit.val, lt_of_lt_of_le bit.isLt bounded⟩).get first =
        (addressBit ⟨bit.val, lt_of_lt_of_le bit.isLt bounded⟩).get last
      rw [addressBit_get, addressBit_get, address]

private lemma initialized_blank_digit
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (bit : Fin (width + 1))
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    (Enable.digitBit stream width bounded bit).get
        (Chain.Arithmetic.Call.clearedInitial input numerator flags address) =
      (Enable.digitBit stream width bounded bit).get
        (sourceBlank input numerator flags address) := by
  exact raw_digit_flags_address stream width bounded bit _ _
    ((Chain.Arithmetic.Call.Endpoint.clearedInitial_flags input numerator flags address).trans
      (sourceBlank_flags input numerator flags address).symm)
    (show (Chain.Arithmetic.Call.clearedInitial input numerator flags address).2 =
      (sourceBlank input numerator flags address).2 from
      (sourceBlank_address input numerator flags address).symm)

private lemma initialized_blank_row
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    Tables.selectedRow stream width bounded
        (Chain.Arithmetic.Call.clearedInitial input numerator flags address) =
      Tables.selectedRow stream width bounded (sourceBlank input numerator flags address) :=
  Tables.selectedRow_eq_of_digit stream width bounded _ _
    (fun bit => initialized_blank_digit stream width bounded bit input numerator flags address)

private lemma initialized_blank_enabled
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    Chain.Arithmetic.Call.Endpoint.divisionEnabled stream width bounded
        input numerator flags address =
      Chain.Control.digitEnabled stream width bounded
        (sourceBlank input numerator flags address) := by
  have predicate :
      (∀ bit, (Enable.digitBit stream width bounded bit).get
        (Chain.Arithmetic.Call.clearedInitial input numerator flags address) = false) ↔
      (∀ bit, (Enable.digitBit stream width bounded bit).get
        (sourceBlank input numerator flags address) = false) :=
    forall_congr' (fun bit => by
      rw [initialized_blank_digit stream width bounded bit input numerator flags address])
  simp only [Chain.Arithmetic.Call.Endpoint.divisionEnabled, Chain.Control.digitEnabled, predicate]


private lemma driver_row_blank {ctx : RuntimeCtx .quantum}
    (parameters : Driver.Parameters ctx)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (same : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) (flags : Frame.Controls) (address : Address) :
    Driver.driverSelectedRow parameters curve same point flags address =
      Tables.selectedRow parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound (Driver.driverAffineBlank curve same point
          flags address) := by
  unfold Driver.driverSelectedRow Driver.driverAffineInitialized
    Driver.driverAffineBlank
  dsimp only
  exact initialized_blank_row parameters.stream _ parameters.addressBound _ _ flags address

private lemma driver_enabled_blank {ctx : RuntimeCtx .quantum}
    (parameters : Driver.Parameters ctx)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (same : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) (flags : Frame.Controls) (address : Address) :
    Driver.driverAffineEnabled parameters curve same point flags address =
      Chain.Control.digitEnabled parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Driver.driverAffineBlank curve same point flags address) := by
  unfold Driver.driverAffineEnabled Driver.driverAffineBlank
  dsimp only
  exact initialized_blank_enabled parameters.stream _ parameters.addressBound _ _ flags address


private lemma fed_affine_blank {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (same : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) :
    let fed := Sampling.sourceFedRaw parameters index source
      (Driver.driverAffineBlank curve same point (false, false, false) 0)
    fed = Driver.driverAffineBlank curve same point fed.1.2 fed.2 := by
  unfold Driver.driverAffineBlank
  dsimp only
  exact sourceFedRaw_blank parameters index source _ _ (false, false, false) 0

private lemma fed_affine_changePoint {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (same : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (first last : AffinePoint curve.curve) :
    let fed := Sampling.sourceFedRaw parameters index source
      (Driver.driverAffineBlank curve same first (false, false, false) 0)
    Sampling.sourceFedRaw parameters index source
        (Driver.driverAffineBlank curve same last (false, false, false) 0) =
      Driver.driverAffineBlank curve same last fed.1.2 fed.2 := by
  unfold Driver.driverAffineBlank
  dsimp only
  exact sourceFedRaw_changePoint parameters index source _ _ _ _ (false, false, false) 0

private lemma fed_affine_normal {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (same : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) :
    (Sampling.sourceFedRaw parameters index source
      (Driver.driverAffineBlank curve same point (false, false, false) 0)).1.2.2.1 =
        false := by
  unfold Driver.driverAffineBlank
  dsimp only
  exact sourceFedRaw_normal parameters index source _ _ (false, false, false) 0


private lemma selectedRow_width_value (stream : Fin 2) (first last : Nat)
    (firstBound : first ≤ 15) (lastBound : last ≤ 15) (same : first = last) (raw : Raw) :
    (Tables.selectedRow stream first firstBound raw).val =
      (Tables.selectedRow stream last lastBound raw).val := by
  cases same
  rfl


section AddressElaboration

attribute [local irreducible] Sampling.sourceFedRaw Tables.selectedRow
  Driver.driverAffineBlank Driver.driverSelectedRow

/-- Specialize the symbolic width equality before supplying the complete physical label. -/
private lemma selectedRow_index_value (index : Sampling.WindowIndex) (raw : Raw) :
    (Tables.selectedRow index.stream (index.highRemaining + index.lowWidth)
      index.addressBound raw).val =
        (Tables.selectedRow index.stream index.lowerWidth index.lowerWidth_bound raw).val :=
  selectedRow_width_value index.stream (index.highRemaining + index.lowWidth) index.lowerWidth
    index.addressBound index.lowerWidth_bound index.addressWidth raw


private lemma fed_affine_address_current {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (same : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) :
    let fed := Sampling.sourceFedRaw parameters index source
      (Driver.driverAffineBlank curve same
        point (false, false, false) 0)
    (Driver.driverSelectedRow (parameters.pointParameters index)
      curve same point fed.1.2 fed.2).val =
        (parameters.sourcePartition index source).1.val := by
  dsimp only
  let blank := Driver.driverAffineBlank curve
    same point (false, false, false) 0
  let fed := Sampling.sourceFedRaw parameters index source blank
  have blankEq := fed_affine_blank parameters index source
    curve same point
  have selected := driver_row_blank (parameters.pointParameters index)
    curve same point fed.1.2 fed.2
  have actual : (Driver.driverSelectedRow (parameters.pointParameters index)
      curve same point fed.1.2 fed.2).val =
        (Tables.selectedRow index.stream index.lowerWidth index.lowerWidth_bound fed).val := by
    have restored := congrArg (fun raw : Raw =>
      (Tables.selectedRow index.stream index.lowerWidth index.lowerWidth_bound raw).val)
      blankEq.symm
    have initial : (Driver.driverSelectedRow (parameters.pointParameters index)
        curve same point fed.1.2 fed.2).val =
          (Tables.selectedRow index.stream (index.highRemaining + index.lowWidth)
            index.addressBound
            (Driver.driverAffineBlank curve same
              point fed.1.2 fed.2)).val := by
      simpa only [Sampling.Parameters.pointParameters] using congrArg Fin.val selected
    have width := selectedRow_index_value index
      (Driver.driverAffineBlank curve same point fed.1.2 fed.2)
    exact initial.trans (width.trans restored)
  exact actual.trans
    (congrArg Fin.val (Sampling.sourceFedRaw_selectedRow parameters index source blank))



end AddressElaboration

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
