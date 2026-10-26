/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Inputs
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Source
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Row
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Prepared

/-!
# The original paid restart loads the same complete affine source label

Equality concerns the entire physical basis label,
including every work bit and address, rather than only the two coordinates.
No instruction, preparation promise or caller-domain premise is added.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve

attribute [local irreducible] PrimeFieldShortWeierstrass.Arithmetic.P256.modulus

private lemma transported_coordinate_values {width target : Nat} (curve : CurveSpec width)
    (sameModulus : curve.field.modulus = target) (point : AffinePoint curve.curve) :
    (MeasuredPointAddition.affineAtModulus curve sameModulus point).x.val = point.x.val ∧
      (MeasuredPointAddition.affineAtModulus curve sameModulus point).y.val = point.y.val := by
  cases sameModulus
  exact ⟨rfl, rfl⟩

private lemma loader_seed_affine (curve : CurveSpec 256)
    (sameModulus : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) :
    Initialization.seed (coordinateWord curve point.x) (coordinateWord curve point.y) =
      Driver.driverAffineBlank curve sameModulus point (false, false, false) 0 := by
  have coordinates := transported_coordinate_values curve sameModulus point
  have first :
      Fin.cast (congrArg (fun size => 2 ^ size)
          PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion.modulus_size).symm
          (coordinateWord curve point.x) =
        PrimeFieldShortWeierstrass.Arithmetic.P256.Residue.input
          (MeasuredPointAddition.affineAtModulus curve sameModulus point).x := by
    apply Fin.ext
    exact coordinates.1.symm
  have second :
      Fin.cast (congrArg (fun size => 2 ^ size)
          PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion.modulus_size).symm
          (coordinateWord curve point.y) =
        PrimeFieldShortWeierstrass.Arithmetic.P256.Residue.input
          (MeasuredPointAddition.affineAtModulus curve sameModulus point).y := by
    apply Fin.ext
    exact coordinates.2.symm
  exact (Initialization.seed_sourceBlank
    (coordinateWord curve point.x) (coordinateWord curve point.y)).trans
    (congrArg₂ (fun x y => sourceBlank x y (false, false, false) 0) first second)

private lemma physicalSeed_affine {ctx : RuntimeCtx .quantum}
    (cleanup : Cleanup.Parameters ctx) (parameters : Sampling.Parameters ctx)
    (curve : CurveSpec 256)
    (sameModulus : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) :
    Initialization.physicalSeed cleanup (coordinateWord curve point.x)
        (coordinateWord curve point.y) =
      parameters.physicalLabel
        (Driver.driverAffineBlank curve sameModulus point (false, false, false) 0) := by
  change parameters.physicalLabel
      (Initialization.seed (coordinateWord curve point.x) (coordinateWord curve point.y)) = _
  exact congrArg parameters.physicalLabel (loader_seed_affine curve sameModulus point)

/-- The actual transported factory restart prepares precisely the sampler's original source ket. -/
lemma factory_restart_seed {outer inner : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (lift : Transport outer inner) (same : outer.quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift) (output : CWriteRef inner (.finite 2)) :
    ((inputs I sameWires results frame base target).transport lift same).restartSeed output =
      ((inputs I sameWires results frame base target).samplerParameters
        lift same scratch fresh).physicalLabel
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          (FullRange.chronologicalFixedSeed I) (false, false, false) 0) := by
  exact physicalSeed_affine
    (((inputs I sameWires results frame base target).transport lift same).restartCleanup output)
    ((inputs I sameWires results frame base target).samplerParameters lift same scratch fresh)
    (actualCurveSpec I) (actualCurveSpec_modulus I)
    (FullRange.chronologicalFixedSeed I)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
