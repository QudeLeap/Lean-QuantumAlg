/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Circuit
import all QuantumAlg.Algorithms.QPE.Circuit
import all QuantumAlg.Algorithms.QPE.Query.Ladder
import all QuantumAlg.Algorithms.QPE.Readout
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Literal native event counts of the three-stage QPE word

Counts include every actual Hadamard, source-query repetition, controlled-phase
expansion and physical SWAP of the inverse readout. Fixed zero preparation and
Z measurement belong to the complete runtime, outside this unitary segment.
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

/-- Counts are projected from the same actual word whose full matrix realizes QPE. -/
public lemma qpeNative_circuit_event_count (phaseWidth : Nat) (systemWidth : Nat)
    (event : Resource.Event (.quantum AlgorithmGate.model (UnitarySource.model systemWidth true))) :
    ResourcePool.count event (circuit phaseWidth systemWidth).eventCost =
      (2 * phaseWidth + 3 * phaseWidth.choose 2) *
        (if .gate .singleQubit = event then 1 else 0) +
      (2 * phaseWidth.choose 2 + 3 * (phaseWidth / 2)) *
        (if .gate .cnot = event then 1 else 0) +
      (2 ^ phaseWidth - 1) * (if .oracle .controlled = event then 1 else 0) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    initialLayer, readoutLayer,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    Gate.HadamardLayer.hadamardLayer_circuit_eventCost
      (UnitarySource.model systemWidth true) phaseWidth,
    qpeNative_queryLadder_eventCost AlgorithmGate.model phaseWidth systemWidth,
    qpeReadout_native_event_count (UnitarySource.model systemWidth true) event phaseWidth]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton]
  ring

end

end QuantumAlg.QuantumPhaseEstimation.Native
