/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Point

/-!
# Original group sum in the actual complete secant-row Store

Both original coordinate rows and the actual preceding batch-inverse C
word determine the same real ten-slot record. Its returned canonical
coordinate pair represents the original affine group sum. Every old
working word is unrestricted, and all histories/references remain in
the separately proved complete interpreter equation for this same record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Actual returned secant coordinates represent exactly the original two group points' sum. -/
lemma extendStore_coordinateValue (curve : CurveSpec width) (seed row destination : Fin length)
    (store : Store ctx) (point basePoint : Point curve)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (input : CoordinateValue curve (store.read (rowRead frame.arrays.x row))
      (store.read (rowRead frame.arrays.y row)) point)
    (baseInput : CoordinateValue curve (store.read (rowRead frame.arrays.x seed))
      (store.read (rowRead frame.arrays.y seed)) basePoint)
    (distinct : ((store.read (rowRead frame.arrays.x row)).toNat : ZMod curve.field.modulus) ≠
      (store.read (rowRead frame.arrays.x seed)).toNat)
    (inverseValue : ((store.read (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) =
      (((store.read (rowRead frame.arrays.x seed)).toNat : ZMod curve.field.modulus) -
        (store.read (rowRead frame.arrays.x row)).toNat)⁻¹) :
    CoordinateValue curve
      ((frame.extendStore curve.field seed row destination store).read
        (rowRead frame.arrays.x destination))
      ((frame.extendStore curve.field seed row destination store).read
        (rowRead frame.arrays.y destination)) (point + basePoint) := by
  have actual := frame.extendStore_read_values curve.field seed row destination store loaded
  dsimp only at actual
  rw [actual.1, actual.2]
  exact CoordinateValue.extendWords_value curve _ _ _ _ _ point basePoint input baseInput
    distinct inverseValue

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The true complete chronological interpreter record returns that same original group sum. -/
lemma extendRecord_coordinateValue (curve : CurveSpec width) (seed row destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point basePoint : Point curve)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (input : CoordinateValue curve (before.1.read (rowRead frame.arrays.x row))
      (before.1.read (rowRead frame.arrays.y row)) point)
    (baseInput : CoordinateValue curve (before.1.read (rowRead frame.arrays.x seed))
      (before.1.read (rowRead frame.arrays.y seed)) basePoint)
    (distinct : ((before.1.read (rowRead frame.arrays.x row)).toNat : ZMod curve.field.modulus) ≠
      (before.1.read (rowRead frame.arrays.x seed)).toNat)
    (inverseValue :
      ((before.1.read (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) =
      (((before.1.read (rowRead frame.arrays.x seed)).toNat : ZMod curve.field.modulus) -
        (before.1.read (rowRead frame.arrays.x row)).toNat)⁻¹) :
    let returned := (frame.extendRecord curve.field seed row destination environment before).1.1
    CoordinateValue curve (returned.read (rowRead frame.arrays.x destination))
      (returned.read (rowRead frame.arrays.y destination)) (point + basePoint) := by
  dsimp only
  rw [frame.extendRecord_store]
  exact frame.extendStore_coordinateValue curve seed row destination before.1 point basePoint
    loaded input baseInput distinct inverseValue

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
