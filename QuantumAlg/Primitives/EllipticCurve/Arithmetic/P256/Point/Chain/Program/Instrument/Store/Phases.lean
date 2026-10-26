/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Phases
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Values.Preservation

/-!
# Protected original table reads through the complete point instrument

The original twenty chronological fragments retain every classical read
outside their actual feedback destinations. Each successive fragment
receives the preceding actual record's Store. The same paid builder's
complete table certificate therefore survives the entire point operation,
independently of the quantum input and arithmetic admission.
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

attribute [local implicit_reducible] enable clearEnable

/-- Every complete actual point record retains the same protected structural input read. -/
lemma pointProgramInstrument_read {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parameters.parity index).key ∉ observed.storageKeys)
    (temporaryFree : parameters.temporary.key ∉ observed.storageKeys) :
    InstrumentPreservesRead (parameters.pointProgramInstrument environment) observed := by
  unfold pointProgramInstrument differencesInstrument divisionInstrument multiplicationInstrument
    reflectionInstrument finishInstrument
  have nativeRead (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum) :
      InstrumentPreservesRead (parameters.nativeFragmentInstrument environment body) observed :=
    parameters.nativeFragmentInstrument_read environment body observed
  have queryRead (occurrence : Fin 6) :
      InstrumentPreservesRead
        (parameters.queryFragmentInstrument environment occurrence) observed :=
    parameters.queryFragmentInstrument_read environment occurrence observed
      outputFree maskFree parityFree temporaryFree
  have callRead (kind : Arithmetic.Call.Kind) :
      InstrumentPreservesRead
        (parameters.arithmeticFragmentInstrument environment kind) observed :=
    parameters.arithmeticFragmentInstrument_read environment kind observed outputFree maskFree
  exact (instrumentPreservesRead_seq _ _ observed
    (instrumentPreservesRead_seq _ _ observed
      (nativeRead _)
      (instrumentPreservesRead_seq _ _ observed
        (queryRead 0)
        (queryRead 1)))
    (instrumentPreservesRead_seq _ _ observed
      (instrumentPreservesRead_seq _ _ observed
        (nativeRead _)
        (instrumentPreservesRead_seq _ _ observed
          (callRead .division)
          (nativeRead _)))
      (instrumentPreservesRead_seq _ _ observed
        (instrumentPreservesRead_seq _ _ observed
          (queryRead 2)
          (instrumentPreservesRead_seq _ _ observed
            (nativeRead _)
            (instrumentPreservesRead_seq _ _ observed
              (nativeRead _)
              (instrumentPreservesRead_seq _ _ observed
                (nativeRead _)
                (instrumentPreservesRead_seq _ _ observed
                  (callRead .multiplication)
                  (nativeRead _))))))
        (instrumentPreservesRead_seq _ _ observed
          (instrumentPreservesRead_seq _ _ observed
            (queryRead 3)
            (instrumentPreservesRead_seq _ _ observed
              (nativeRead _)
              (instrumentPreservesRead_seq _ _ observed
                (nativeRead _)
                (instrumentPreservesRead_seq _ _ observed
                  (nativeRead _)
                  (nativeRead _)))))
          (instrumentPreservesRead_seq _ _ observed
            (queryRead 4)
            (instrumentPreservesRead_seq _ _ observed
              (queryRead 5)
              (nativeRead _)))))))

/-- The same original full table certificate holds in every literal final point Store. -/
lemma pointProgramInstrument_tableValue {length : Nat}
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
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys) :
    ∀ outcome, TableFrame.TableValue curve frame point
      ((parameters.pointProgramInstrument environment).record store outcome).1 := by
  intro outcome
  apply TableFrame.TableValue.of_column_reads curve frame point store _ values
  intro column
  exact parameters.pointProgramInstrument_read environment
    (.storage (frame.finishColumns column).toCStorageRef)
    (fun index => outputFree index column) (maskFree column)
    (fun index => parityFree index column) (temporaryFree column) store outcome

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
