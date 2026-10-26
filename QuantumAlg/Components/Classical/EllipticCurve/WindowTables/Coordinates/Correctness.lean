/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Point

/-!
# Original group value of the actual paid coordinate doubling

The canonical coordinate invariant is attached to the Store returned by
the same actual fifteen-slot record. The real loaded modulus and curve
coefficient are read from the original Store. Source and destination may
coincide, and no old working-word value is assumed.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- Both actual returned coordinate words represent precisely the original doubled group point. -/
lemma doubleStore_coordinateValue (curve : CurveSpec width) (source destination : Fin length)
    (store : Store ctx) (point : Point curve)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((store.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (input : CoordinateValue curve (store.read (rowRead frame.x source))
      (store.read (rowRead frame.y source)) point)
    (doubled : point + point ≠ 0) :
    CoordinateValue curve
      ((frame.doubleStore curve.field source destination store).read (rowRead frame.x destination))
      ((frame.doubleStore curve.field source destination store).read (rowRead frame.y destination))
      (point + point) := by
  have actual := frame.doubleStore_read_values curve.field source destination store loaded
  dsimp only at actual
  rw [actual.1, actual.2]
  exact CoordinateValue.doubleWords_value curve _ _ _ point input curveValue doubled

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : CoordinateFrame ctx width length)

/-- The full chronological actual interpreter record returns that same original group value. -/
lemma doubleRecord_coordinateValue (curve : CurveSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) (point : Point curve)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (input : CoordinateValue curve (before.1.read (rowRead frame.x source))
      (before.1.read (rowRead frame.y source)) point)
    (doubled : point + point ≠ 0) :
    let returned := (frame.doubleRecord curve.field source destination environment before).1.1
    CoordinateValue curve (returned.read (rowRead frame.x destination))
      (returned.read (rowRead frame.y destination)) (point + point) := by
  dsimp only
  rw [frame.doubleRecord_store]
  exact frame.doubleStore_coordinateValue curve source destination before.1 point
    loaded curveValue input doubled

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
