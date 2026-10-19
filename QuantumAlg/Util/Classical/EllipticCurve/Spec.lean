/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Classical.Modular.Basic
public import QuantumAlg.Util.EllipticCurve
import all QuantumAlg.Util.EllipticCurve

/-!
# Public fixed-width elliptic-curve specification

This narrow module exposes the curve certificate used by public classical
elliptic-curve endpoints without exporting their implementation dependencies.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace EllipticCurve

open Modular

noncomputable section

/-- A fitted prime-field curve together with the Mathlib witness needed to
turn its affine equation into nonsingularity. -/
public structure CurveSpec (width : Nat) where
  /-- The prime modulus and its fixed-width capacity proof. -/
  field : ModulusSpec width
  /-- The existing short-Weierstrass curve certificate over that modulus. -/
  curve : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass field.modulus
  /-- The corresponding Mathlib affine curve is elliptic. -/
  elliptic : curve.toWeierstrassCurve.toAffine.IsElliptic

namespace CurveSpec

/-- The curve certificate exports the prime-field fact used by `ZMod`. -/
lemma primeFact {width : Nat} (spec : CurveSpec width) :
    Fact spec.field.modulus.Prime :=
  ⟨spec.curve.prime⟩

/-- The stored affine ellipticity witness, exposed under the fixed-width
specification. -/
lemma affineIsElliptic {width : Nat} (spec : CurveSpec width) :
    spec.curve.toWeierstrassCurve.toAffine.IsElliptic :=
  spec.elliptic

/-- The local prime-field instance associated with a fixed-width curve
specification. -/
public instance instFactPrime {width : Nat} (spec : CurveSpec width) :
    Fact spec.field.modulus.Prime :=
  spec.primeFact

/-- The local Mathlib ellipticity instance associated with a fixed-width curve
specification. -/
public instance instAffineIsElliptic {width : Nat} (spec : CurveSpec width) :
    spec.curve.toWeierstrassCurve.toAffine.IsElliptic :=
  spec.affineIsElliptic

/-- Over the stored elliptic curve, the local short-Weierstrass affine equation
is exactly Mathlib's nonsingularity predicate. -/
lemma affineEquation_iff_nonsingular {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) :
    spec.curve.AffineEquation x y ↔
      spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y := by
  rw [← spec.curve.affineEquation_iff_mathlib_equation]
  exact WeierstrassCurve.Affine.equation_iff_nonsingular

end CurveSpec

end

end EllipticCurve

end ClassicalAlgorithms
end QuantumAlg

end
