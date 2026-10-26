/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Store
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame

/-!
# Runtime table reads survive the actual physical measurement and reset

The actual Store writes are the named finite outcomes and paid packed mask.
Every structurally supplied table read outside these cells is retained for
the subsequent runtime AND/XOR feedback, for every actual measurement path.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The real complete word reset preserves every structural read outside its real destinations. -/
lemma measuredWordFinalStore_read_other (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits width)) {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (output index).key ∉ observed.storageKeys)
    (maskFree : mask.key ∉ observed.storageKeys) (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) :
    (measuredWordFinalStore (oracles := oracles) (services := services)
      physical sameWires target output mask store path).read observed = store.read observed := by
  refine (Store.read_applyOp_of_not_mem_storageKeys _ (resultPackOp output mask) observed
    maskFree).trans ?_
  apply Circuit.writeMeasurementPath_read_input
    (resultReadouts physical sameWires target output) observed _ store path
  intro item member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  change (finiteOutput (resultWire_qubit physical sameWires (target.bit index))
    (output index)).key ∉ observed.storageKeys
  rw [finiteOutput_key]
  exact outputFree index

end

end QuantumAlg.EncodedBit.WindowLookup
