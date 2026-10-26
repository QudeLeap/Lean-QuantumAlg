/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Parameters
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Resources.Events
import all QuantumAlg.Components.GateModel.Algorithm.Resources.Hybrid

/-!
# Complete nongate coordinates of an actual runtime load/unlookup pair

The selected lookup is a pure native word and contributes no nongate event.
The actual measured unlookup contributes its complete independent finite
pool, including the width-indexed pack and every paid parity instruction.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable.CycleParameters

open AlgorithmGate

noncomputable section

/-- Actual runtime selection adds no unaccounted nongate coordinate to its measured feedback. -/
lemma nongate_pool_le {Data : Type} {encoding : BinaryLabelEncoding Data}
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {wordWidth lowWidth highRemaining : Nat}
    (parameters : CycleParameters encoding ctx wordWidth lowWidth highRemaining)
    (path : (parameters.circuit (services := services)).Path) :
    nonGateEnvelope (parameters.circuit.resourcePool path) ≤
      nonGateEnvelope (RuntimeUnlookup.envelope services wordWidth lowWidth highRemaining) := by
  unfold circuit at path ⊢
  rw [cycleCircuit_resourcePool, nonGateEnvelope_add, lookupCircuit_resourcePool,
    nonGateEnvelope_unitary, zero_add]
  exact nonGateEnvelope_mono (RuntimeUnlookup.circuit_pool_le parameters.frame parameters.physical
    parameters.sameWires parameters.output parameters.mask parameters.parity parameters.temporary
    (splitInputs parameters.source) path.2)

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable.CycleParameters
