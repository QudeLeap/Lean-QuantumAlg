/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Values.Preservation
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Store
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Store

/-!
# The same actual five-table certificate after real queries and arithmetic calls

Every actual retained record keeps all original columns outside its real
write destinations. The original builder's certificate therefore applies
to the exact next Store read by the subsequent chronological operation.
Separation is a property of the actual supplied storage references; it is
independent of the quantum input, measured values and arithmetic domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Tables

noncomputable section

open Execution EncodedBit.WindowLookup
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {length : Nat} (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256 length) (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)

include values

/-- Every original column remains certified in the actual next runtime-query Store. -/
lemma queryRecord_tableValue {lowWidth highRemaining : Nat}
    (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts parameters.physical parameters.sameWires
        parameters.frame.result parameters.output)).Path) :
    TableFrame.TableValue curve frame point (parameters.insertedRecord body store path).1 := by
  apply TableFrame.TableValue.of_column_reads curve frame point store _ values
  intro column
  exact parameters.insertedRecord_read_input (services := services) body
    (.storage (frame.finishColumns column).toCStorageRef)
    (fun index => outputFree index column) (maskFree column)
    (fun index => parityFree index column) (temporaryFree column) store path

/-- Both actual measured arithmetic calls retain the same full certified original tables. -/
lemma callRecord_tableValue
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (kind : Chain.Arithmetic.Call.Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (outputFree : ∀ index column, (output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (outcome : Chain.Reset.Instrument.Outcome (services := services) .numerator sameWires output) :
    TableFrame.TableValue curve frame point
      (Chain.Arithmetic.Call.record (services := services) sameWires output mask kind stream width
        bounded store outcome).1 := by
  apply TableFrame.TableValue.of_column_reads curve frame point store _ values
  intro column
  exact Chain.Arithmetic.Call.callRecord_read_input (services := services)
    sameWires output mask kind stream width bounded
    (.storage (frame.finishColumns column).toCStorageRef)
    (fun index => outputFree index column) (maskFree column) store outcome

end

end Tables

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
