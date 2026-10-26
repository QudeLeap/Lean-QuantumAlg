/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Values.Preservation

/-!
# The same paid table at each literal intermediate point record

Complete-column reads retain the original table certificate at the actual
returned Store. The three fragment laws provide this fact without any
quantum domain, basis, canonicality or action premise. Each chronological
consumer can therefore read the same paid table after a real query or call.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment}

/-- Protected whole-column reads retain the same actual table on every original outcome. -/
lemma instrument_tableValue {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false}
    (actual : Execution.Instrument code Outcome environment) {length : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256 length) (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (reads : ∀ column, InstrumentPreservesRead actual
      (.storage (frame.finishColumns column).toCStorageRef)) (outcome : Outcome) :
    TableFrame.TableValue curve frame point (actual.record store outcome).1 := by
  apply TableFrame.TableValue.of_column_reads curve frame point store _ values
  intro column
  exact reads column store outcome

variable (parameters : Parameters ctx) (environment)

/-- An original native fragment leaves every complete table column at the same Store. -/
lemma nativeFragmentInstrument_tableValue
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum) {length : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256 length) (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (outcome : Unit) :
    TableFrame.TableValue curve frame point
      ((parameters.nativeFragmentInstrument environment body).record store outcome).1 :=
  instrument_tableValue _ curve frame point store values
    (fun _ => parameters.nativeFragmentInstrument_read environment body _) outcome

/-- The actual query's measured output and paid feedback retain the original complete table. -/
lemma queryFragmentInstrument_tableValue (occurrence : Fin 6) {length : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256 length) (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path : parameters.QueryOutcome (services := services) occurrence) :
    TableFrame.TableValue curve frame point
      ((parameters.queryFragmentInstrument environment occurrence).record store path).1 :=
  instrument_tableValue _ curve frame point store values
    (fun column => parameters.queryFragmentInstrument_read environment occurrence _
      (fun index => outputFree index column) (maskFree column)
      (fun index => parityFree index column) (temporaryFree column)) path

/-- The same real arithmetic record retains all table rows outside its two write families. -/
lemma arithmeticFragmentInstrument_tableValue (kind : Arithmetic.Call.Kind) {length : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256 length) (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path : Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
      parameters.output) :
    TableFrame.TableValue curve frame point
      ((parameters.arithmeticFragmentInstrument environment kind).record store path).1 :=
  instrument_tableValue _ curve frame point store values
    (fun column => parameters.arithmeticFragmentInstrument_read environment kind _
      (fun index => outputFree index column) (maskFree column)) path

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
