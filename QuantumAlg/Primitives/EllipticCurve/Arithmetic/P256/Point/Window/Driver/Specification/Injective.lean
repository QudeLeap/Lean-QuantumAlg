/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification

/-!
# Faithful affine points in the complete original blank workspace

The actual raw label retains both ordinary field coordinates. Fixed flags and
an address therefore leave exactly the mathematical affine-point collisions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

noncomputable section

open ClassicalAlgorithms.EllipticCurve
open MAU.Inversion.SharedEEA MAU.Inversion.SharedEEA.Scanned

attribute [local irreducible] modulus

private lemma transport_state_injective {width : Nat} (same : width = 256) :
    Function.Injective (Inversion.Transport.state same) := by
  cases same
  intro first last retained
  simpa only [Inversion.Transport.state_refl] using retained

private lemma residentBlank_coordinates (width : Nat)
    (firstInput lastInput : BitVec (width + 3)) (pool : Pool width)
    (flags : Frame.Controls) (firstNumerator lastNumerator : Fin (2 ^ width))
    (same : ControlledResidentSeed.blank width firstInput pool flags firstNumerator =
      ControlledResidentSeed.blank width lastInput pool flags lastNumerator) :
    firstInput = lastInput ∧ firstNumerator = lastNumerator := by
  have grouped := congrArg (ControlledResidentFrame.layout width).grouping same
  simp only [ControlledResidentSeed.blank, ← ControlledResidentFrame.layout_reassemble,
    Equiv.apply_symm_apply] at grouped
  exact ⟨congrArg (fun value : ControlledResidentFrame.Grouped width =>
      value.1.1.1.secondWord) grouped,
    congrArg (fun value : ControlledResidentFrame.Grouped width => value.2.1) grouped⟩

private lemma sourceBlank_coordinates
    (firstInput lastInput firstNumerator lastNumerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Address)
    (same : sourceBlank firstInput firstNumerator flags address =
      sourceBlank lastInput lastNumerator flags address) :
    firstInput = lastInput ∧ firstNumerator = lastNumerator := by
  have transported := congrArg Prod.fst same
  change Inversion.Transport.state Inversion.modulus_size
      (ControlledResidentSeed.blank modulus.size
        (InitialPortProgram.inputFrame modulus firstInput).secondWord
        (0, (0, false)) flags firstNumerator) =
    Inversion.Transport.state Inversion.modulus_size
      (ControlledResidentSeed.blank modulus.size
        (InitialPortProgram.inputFrame modulus lastInput).secondWord
        (0, (0, false)) flags lastNumerator) at transported
  have original := transport_state_injective Inversion.modulus_size transported
  have coordinates := residentBlank_coordinates modulus.size _ _ _ _ _ _ original
  refine ⟨Fin.ext ?_, coordinates.2⟩
  have values := congrArg BitVec.toNat coordinates.1
  simpa only [InitialPortProgram.inputFrame_input, InitialFrame.initial_secondWord] using values

private lemma affineAtModulus_injective {width : Nat} (curve : CurveSpec width) {target : Nat}
    (same : curve.field.modulus = target) :
    Function.Injective (MeasuredPointAddition.affineAtModulus curve same) := by
  cases same
  intro first last retained
  exact retained

/-- The complete fixed-flag, fixed-address blank label identifies exactly one affine point. -/
lemma driverAffineBlank_injective (curve : CurveSpec 256)
    (sameModulus : curve.field.modulus = modulus) (flags : Frame.Controls) (address : Address) :
    Function.Injective (fun point => driverAffineBlank curve sameModulus point flags address) := by
  intro first last same
  have coordinates := sourceBlank_coordinates _ _ _ _ flags address same
  have firstCoordinate := congrArg (fun value : Fin (2 ^ modulus.size) =>
    (value.val : ZMod modulus)) coordinates.1
  have secondCoordinate := congrArg (fun value : Fin (2 ^ modulus.size) =>
    (value.val : ZMod modulus)) coordinates.2
  simp only [Residue.input_cast] at firstCoordinate secondCoordinate
  apply affineAtModulus_injective curve sameModulus
  exact AffinePoint.ext_coordinates _ _ firstCoordinate secondCoordinate

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver
