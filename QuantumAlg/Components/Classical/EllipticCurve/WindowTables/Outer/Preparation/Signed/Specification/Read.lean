/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Specification

/-!
# Transport of the shared preparation invariant through actual reads

Four scalar reads and two complete arrays determine the original constants
and paired row families. These implications apply to any actual component's
returned Store and do not assume that a preparation program has run.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.Modular.NativePower

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The same four word values retain the one shared constant invariant. -/
lemma constants_of_word_reads (frame : Frame ctx width) (curve : CurveSpec width)
    (before after : Store ctx)
    (modulusRead : after.read (wordRead frame.modulus) = before.read (wordRead frame.modulus))
    (zeroRead : after.read (.storage frame.zero.toCStorageRef) =
      before.read (.storage frame.zero.toCStorageRef))
    (oneRead : after.read (.storage frame.one.toCStorageRef) =
      before.read (.storage frame.one.toCStorageRef))
    (curveRead : after.read (.storage frame.curveA.toCStorageRef) =
      before.read (.storage frame.curveA.toCStorageRef))
    (constants : Constants frame curve before) : Constants frame curve after := by
  constructor
  · exact modulusRead.trans constants.modulus
  · exact (congrArg CShape.Value.toNat zeroRead).trans constants.zero
  · exact (congrArg CShape.Value.toNat oneRead).trans constants.one
  · rw [curveRead]
    exact constants.curveA

/-- The actual two array reads retain every row in both original point families. -/
lemma pairedRows_of_array_reads (frame : Frame ctx width) (curve : CurveSpec width)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (before after : Store ctx)
    (xRead : after.read (.storage frame.x.toCStorageRef) =
      before.read (.storage frame.x.toCStorageRef))
    (yRead : after.read (.storage frame.y.toCStorageRef) =
      before.read (.storage frame.y.toCStorageRef))
    (rows : pairedRows curve frame first second before) :
    pairedRows curve frame first second after := by
  have xs (row : Fin 34) : after.read (rowRead frame.coordinates.x row) =
      before.read (rowRead frame.coordinates.x row) :=
    congrArg (fun value => value.get row) xRead
  have ys (row : Fin 34) : after.read (rowRead frame.coordinates.y row) =
      before.read (rowRead frame.coordinates.y row) :=
    congrArg (fun value => value.get row) yRead
  constructor
  · intro row
    rw [xs, ys]
    exact rows.1 row
  · intro row
    rw [xs, ys]
    exact rows.2 row

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
