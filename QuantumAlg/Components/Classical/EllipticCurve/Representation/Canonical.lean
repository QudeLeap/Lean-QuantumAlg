/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model

/-!
# Canonical words from an already represented finite nominal input

These width-parametric lemmas turn an already represented finite nominal
input into its unique canonical encoding and coordinate words. A successful
decode determines the encoding; no preprocessing instruction or stronger
caller premise is added.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve

open ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

/-- A represented finite nominal point is its unique canonical code. -/
lemma representedAffine_eq_encodePoint {width : Nat} (spec : CurveSpec width)
    (value : CShape.Value (PointShape width))
    (point : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint spec.curve)
    (represented : PointRepresents spec value point.toMathlib) :
    value = encodePoint spec point.toMathlib := by
  have encoded := ClassicalAlgorithms.EllipticCurve.encode_eq_of_decode_eq_some
    spec (decodeCode value) point.toMathlib represented
  exact (encodeCode_decodeCode value).symm.trans (congrArg encodeCode encoded.symm)

/-- Both structural words agree with the same represented finite point. -/
lemma representedAffine_coordinate_words {width : Nat} (spec : CurveSpec width)
    (value : CShape.Value (PointShape width))
    (point : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint spec.curve)
    (represented : PointRepresents spec value point.toMathlib) :
    value.ellipticCurvePointX = coordinateWord spec point.x ∧
      value.ellipticCurvePointY = coordinateWord spec point.y := by
  rw [representedAffine_eq_encodePoint spec value point represented]
  exact ⟨rfl, rfl⟩

/-- The paid subtraction's exact numeric output is the canonical negative Y word. -/
lemma coordinateWord_neg_value {width : Nat} (curve : CurveSpec width)
    (y : ZMod curve.field.modulus) :
    (0 + curve.field.modulus - (coordinateWord curve y).val) % curve.field.modulus =
      (coordinateWord curve (-y)).val := by
  let _ : NeZero curve.field.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos curve.field)⟩
  simpa only [zero_add, coordinateWord_val] using (ZMod.neg_val' y).symm

end

end QuantumAlg.ClassicalRoutines.EllipticCurve
