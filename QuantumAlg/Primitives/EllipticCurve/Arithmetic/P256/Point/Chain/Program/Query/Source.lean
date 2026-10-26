/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Initialized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Residue

/-!
# Original initialized query source from the actual certified table

The same paid builder's full table certificate determines the stored
column read. The equality of array references binds that certificate to
the actual point parameters. The full row remains symbolic, including
row zero; this identity introduces no executable preprocessing.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Arithmetic.Call.clearedInitial Residue.input

/-- The same actual table certificate supplies the original initialized source read. -/
lemma queryInitializedSource_of_tableValue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (occurrence : Fin 6) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    parameters.QueryInitializedSource occurrence store x y
      (Window.Tables.selectedFieldColumn curve point parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
        (Window.QueryColumns.column occurrence)) flags address := by
  constructor
  have selected := Window.Tables.selectedWord_residue
    (stream := parameters.stream)
    (width := parameters.highRemaining + parameters.lowWidth)
    (bounded := parameters.addressBound) sameModulus values
    (Window.QueryColumns.column occurrence)
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
  simpa only [querySource, arrays] using selected

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
