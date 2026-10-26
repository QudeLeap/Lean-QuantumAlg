/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Inserted
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Store.Preservation

/-!
# The real complete query record preserves every protected original table

The runtime loader and native arithmetic write no classical storage.
The actual measured reset and paid feedback retain every original
structural read separate from the supplied result and feedback cells.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable.CycleParameters

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {wordWidth lowWidth highRemaining : Nat}
    (parameters : CycleParameters encoding ctx wordWidth lowWidth highRemaining)

/-- Actual final Store reads keep all protected original words, including entire other columns. -/
lemma insertedRecord_read_input
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parameters.parity index).key ∉ observed.storageKeys)
    (temporaryFree : parameters.temporary.key ∉ observed.storageKeys) (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts parameters.physical parameters.sameWires
        parameters.frame.result parameters.output)).Path) :
    (parameters.insertedRecord body store path).1.read observed = store.read observed :=
  RuntimeUnlookup.record_read_input (services := services)
    parameters.frame parameters.physical parameters.sameWires
    parameters.output parameters.mask parameters.parity parameters.temporary
    (splitInputs parameters.source) observed outputFree maskFree parityFree temporaryFree store path

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable.CycleParameters
