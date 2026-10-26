/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Queries
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Source
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Initializer

/-!
# Actual initialized query actions from the retained paid table

The source equation comes from the same original table certificate at
this fragment's literal input Store. Changes of the numerical words or
genuine normal selector preserve its full top-plus-address row. These
identities generate no classical data and impose no quantum action
assumption on an enclosing point operation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Arithmetic.Call.clearedInitial Residue.input
  InstrumentBranchAction queryFieldNext

/-- A retained paid table supplies the source of every literal query instrument. -/
lemma queryInstrument_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (occurrence : Fin 6) (separation : parameters.QueryFieldSeparation occurrence)
    (seed : Window.Raw) (path : parameters.QueryOutcome (services := services) occurrence)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    let column := Window.Tables.selectedFieldColumn curve point parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (Window.QueryColumns.column occurrence)
    parameters.InstrumentBranchAction environment
      (parameters.queryFragmentInstrument environment occurrence) store path
      (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (Arithmetic.Call.clearedInitial
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).1)
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).2)
        flags address) reference := by
  dsimp only
  exact parameters.queryInstrument_initialized_residue environment occurrence store separation
    seed path x y _ flags address
    (parameters.queryInitializedSource_of_tableValue curve frame point sameModulus arrays
      store values occurrence x y flags address) reference

/-- The same stored source can be named at any prior X/Y and genuine-N value in this row. -/
lemma queryInitializedSource_table_anchor
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (occurrence : Fin 6) (x y anchorX anchorY : ZMod modulus)
    (flags : Frame.Controls) (normal : Bool) (address : Window.Address) :
    parameters.QueryInitializedSource occurrence store x y
      (Window.Tables.selectedFieldColumn curve point parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Arithmetic.Call.clearedInitial (Residue.input anchorX) (Residue.input anchorY)
          flags address)
        (Window.QueryColumns.column occurrence))
      (Arithmetic.Call.Endpoint.setNormal flags normal) address := by
  have actual := parameters.queryInitializedSource_of_tableValue curve frame point
    sameModulus arrays store values occurrence x y
    (Arithmetic.Call.Endpoint.setNormal flags normal) address
  rw [Window.Tables.selectedFieldColumn_clearedInitial_setNormal,
    Window.Tables.selectedFieldColumn_clearedInitial_values
      _ _ _ _ _ (Residue.input x) (Residue.input y)
      (Residue.input anchorX) (Residue.input anchorY)] at actual
  exact actual

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
