/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Point

/-!
# Original canonical coordinate inputs for the same finite affine point

The original coordinate-word constructor retains both field values without
truncation. This pure value
fact supplies no storage reference or unproved claim about an actual Store.
The enclosing original input construction must still establish its four
real structural reads. No new preprocessing instruction is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

noncomputable section

open ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

/-- The original canonical coordinate words represent their same original affine point. -/
lemma affineCoordinateValue {width : Nat} (spec : CurveSpec width)
    (point : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint spec.curve) :
    CoordinateValue spec (.unsignedWord (coordinateWord spec point.x))
      (.unsignedWord (coordinateWord spec point.y)) point.toMathlib := by
  let : NeZero spec.field.modulus := ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec.field)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ZMod.val_lt point.x
  · exact ZMod.val_lt point.y
  · simpa only [CShape.Value.toNat, coordinateWord_val, ZMod.natCast_zmod_val]
      using point.nonsingular
  · simp only [CShape.Value.toNat, coordinateWord_val, ZMod.natCast_zmod_val,
      QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint.toMathlib]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
