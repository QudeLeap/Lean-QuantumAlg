/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Inputs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program

/-!
# Actual batch-to-recovery structural wiring

The completed batch's concrete context is instantiated only at this boundary.
The generic recovery inputs and their store laws remain independent of bank
preparation, measurement allocation and the sixteen-round context expansion.
Both references are the actual retained cells already produced by that batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery

/-- Concrete recovery inputs read the exact completed native batch's existing live cells. -/
def fromBatch (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat) :
    Inputs (NativeBatch.context base noQuantum N) N where
  parameter := NativeBatch.finalParameter base noQuantum N
  outcomes := NativeBatch.finalResults base noQuantum N

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery
