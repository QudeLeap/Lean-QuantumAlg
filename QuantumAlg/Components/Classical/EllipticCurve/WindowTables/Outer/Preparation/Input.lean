/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Input

/-!
# The same original four source reads supply both paid base families

The original input Store supplies the generator coordinates and the already
signed second point coordinates through its actual four structural references.
Their canonical value certificates feed the unchanged paid paired preparation.
This internal consumer does not construct those original Store reads, add a
negation instruction, or charge previously deferred external preprocessing.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame

open Execution ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve
open Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat} (frame : Frame ctx width)

private lemma negativeAffineCoordinateValue (curve : CurveSpec width)
    (target : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve) :
    CoordinateValue curve (.unsignedWord (coordinateWord curve target.x))
      (.unsignedWord (coordinateWord curve (-target.y))) (-target.toMathlib) := by
  let negative : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve :=
    ⟨target.x, -target.y, ShortWeierstrass.neg_nonsingular curve _ _ target.nonsingular⟩
  have same : negative.toMathlib = -target.toMathlib :=
    (ShortWeierstrass.neg_eval_some curve target.x target.y target.nonsingular).symm
  rw [← same]
  exact affineCoordinateValue curve negative

/-- Actual original source reads give both families in the same returned Store. -/
lemma pairedBasesRecord_signed_values (curve : CurveSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (first target : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (targetOrder : addOrderOf target.toMathlib = order)
    (loaded : before.1.read (wordRead frame.coordinates.modulus) =
      .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.coordinates.curveA).toNat : ZMod curve.field.modulus) =
      curve.curve.a)
    (firstYFree : frame.coordinates.x.key ∉ firstY.storageKeys)
    (secondXFree : Preparation.OutputFree frame.coordinates secondX)
    (secondYFree : Preparation.OutputFree frame.coordinates secondY)
    (firstXValue : before.1.read firstX = .unsignedWord (coordinateWord curve first.x))
    (firstYValue : before.1.read firstY = .unsignedWord (coordinateWord curve first.y))
    (secondXValue : before.1.read secondX = .unsignedWord (coordinateWord curve target.x))
    (secondYValue : before.1.read secondY = .unsignedWord (coordinateWord curve (-target.y))) :
    let returned := (frame.pairedBasesRecord curve.field firstX firstY secondX secondY
      environment before).1.1
    returned.read (wordRead frame.coordinates.modulus) = before.1.read
        (wordRead frame.coordinates.modulus) ∧
      returned.read frame.coordinates.curveA = before.1.read frame.coordinates.curveA ∧
      (∀ index : Fin 17, CoordinateValue curve
        (returned.read (rowRead frame.coordinates.x (firstBaseRows index)))
        (returned.read (rowRead frame.coordinates.y (firstBaseRows index)))
        ((2 ^ (16 * index.val)) • first.toMathlib)) ∧
      (∀ index : Fin 17, CoordinateValue curve
        (returned.read (rowRead frame.coordinates.x (secondBaseRows index)))
        (returned.read (rowRead frame.coordinates.y (secondBaseRows index)))
        ((2 ^ (16 * index.val)) • (-target.toMathlib))) := by
  have firstInput : CoordinateValue curve (before.1.read firstX)
      (before.1.read firstY) first.toMathlib := by
    rw [firstXValue, firstYValue]
    exact affineCoordinateValue curve first
  have secondInput : CoordinateValue curve (before.1.read secondX)
      (before.1.read secondY) (-target.toMathlib) := by
    rw [secondXValue, secondYValue]
    exact negativeAffineCoordinateValue curve target
  have secondOrder : addOrderOf (-target.toMathlib) = order := by
    rw [addOrderOf_neg]
    exact targetOrder
  exact frame.pairedBasesRecord_values curve firstX firstY secondX secondY environment before
    first.toMathlib (-target.toMathlib) order prime large firstOrder secondOrder loaded curveValue
    firstYFree secondXFree secondYFree firstInput secondInput

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame
