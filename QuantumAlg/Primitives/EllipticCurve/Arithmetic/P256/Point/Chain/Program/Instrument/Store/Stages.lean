/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Phases

/-!
# Protected reads at the actual intermediate point-stage Stores

Each phase retains every structural input read outside its real feedback
destinations. These separate prefix laws supply the same paid-table values
to the next actual phase. No quantum input, arithmetic-domain or action
assumption is used, and every original outcome remains quantified.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {shape : CShape} (observed : CInputRef ctx shape)

attribute [local implicit_reducible] enable clearEnable

/-- Every actual differences phase record retains the same protected structural read. -/
lemma differencesInstrument_read
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parameters.parity index).key ∉ observed.storageKeys)
    (temporaryFree : parameters.temporary.key ∉ observed.storageKeys) :
    InstrumentPreservesRead (parameters.differencesInstrument environment) observed := by
  unfold differencesInstrument
  exact (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.queryFragmentInstrument_read environment 0 observed
      outputFree maskFree parityFree temporaryFree)
    (parameters.queryFragmentInstrument_read environment 1 observed
      outputFree maskFree parityFree temporaryFree)))

/-- Every actual division phase record retains the same protected structural read. -/
lemma divisionInstrument_read
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys) :
    InstrumentPreservesRead (parameters.divisionInstrument environment) observed := by
  unfold divisionInstrument
  exact (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.arithmeticFragmentInstrument_read environment .division observed
      outputFree maskFree)
    (parameters.nativeFragmentInstrument_read environment _ observed)))

/-- Every actual multiplication phase record retains the same protected structural read. -/
lemma multiplicationInstrument_read
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parameters.parity index).key ∉ observed.storageKeys)
    (temporaryFree : parameters.temporary.key ∉ observed.storageKeys) :
    InstrumentPreservesRead (parameters.multiplicationInstrument environment) observed := by
  unfold multiplicationInstrument
  exact (instrumentPreservesRead_seq _ _ observed
    (parameters.queryFragmentInstrument_read environment 2 observed
      outputFree maskFree parityFree temporaryFree)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.arithmeticFragmentInstrument_read environment .multiplication observed
      outputFree maskFree)
    (parameters.nativeFragmentInstrument_read environment _ observed))))))

/-- Every actual reflection phase record retains the same protected structural read. -/
lemma reflectionInstrument_read
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parameters.parity index).key ∉ observed.storageKeys)
    (temporaryFree : parameters.temporary.key ∉ observed.storageKeys) :
    InstrumentPreservesRead (parameters.reflectionInstrument environment) observed := by
  unfold reflectionInstrument
  exact (instrumentPreservesRead_seq _ _ observed
    (parameters.queryFragmentInstrument_read environment 3 observed
      outputFree maskFree parityFree temporaryFree)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.nativeFragmentInstrument_read environment _ observed)
    (parameters.nativeFragmentInstrument_read environment _ observed)))))

/-- Every actual finish phase record retains the same protected structural read. -/
lemma finishInstrument_read
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parameters.parity index).key ∉ observed.storageKeys)
    (temporaryFree : parameters.temporary.key ∉ observed.storageKeys) :
    InstrumentPreservesRead (parameters.finishInstrument environment) observed := by
  unfold finishInstrument
  exact (instrumentPreservesRead_seq _ _ observed
    (parameters.queryFragmentInstrument_read environment 4 observed
      outputFree maskFree parityFree temporaryFree)
    (instrumentPreservesRead_seq _ _ observed
    (parameters.queryFragmentInstrument_read environment 5 observed
      outputFree maskFree parityFree temporaryFree)
    (parameters.nativeFragmentInstrument_read environment _ observed)))

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
