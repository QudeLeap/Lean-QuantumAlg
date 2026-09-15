/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Depth

/-!
# Actual native short-DLP family with independent resource contracts

Each runtime parameter selects the real two-exponentiation circuit. All
members share the same actual exponent, power and auxiliary wires; the
independent budgets retain native control labels and bound every duration
assignment. The source preparation, QFT readout and Born semantics are
provided by the same circuit graph.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Parameter-selected actual members, complete native pools, and a common literal wire layout. -/
def compiledCircuitFamily {Parameter : Type} (m ell width N : Nat)
    (generator target : Parameter → (ZMod N)ˣ) :
    UnitaryCircuitFamily Parameter (Qubits (totalQubits (registerParameters m ell width))) where
  member parameter := compiledCircuit m ell width N (generator parameter) (target parameter)
  eventEnvelope := compiledCircuitEventEnvelope m ell width N
  member_eventCost_le parameter :=
    compiledCircuit_eventCost_le m ell width N (generator parameter) (target parameter)
  depthEnvelope := compiledCircuitDepthEnvelope m ell width N
  member_eventDepth_le parameter assignment :=
    compiledCircuit_eventDepth_le m ell width N (generator parameter) (target parameter) assignment
  commonPhysicalIdx := List.range (totalQubits (registerParameters m ell width))
  member_physical_idx parameter :=
    compiledCircuit_physical_idx m ell width N (generator parameter) (target parameter)

end

end QuantumAlg.ShortDLP.CompiledMAU
