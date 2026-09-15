/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction

/-!
# Identity entries for the finite-cyclic Born calculation

The untouched workspace contributes the original Kronecker delta.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge

noncomputable section

/-- Matrix entries of an untouched workspace identity circuit. -/
@[simp] theorem identityCircuit_entry (n : Nat) (systemIdx : List Nat)
    (hvalid : systemIdx.Nodup) (left right : Fin (2 ^ n)) :
    ((UnitaryCircuit.identity (Qubits n) systemIdx hvalid : UnitaryCircuit (Qubits n)).matrix :
      HilbertOperator (Qubits n)) left right =
        if left = right then 1 else 0 := by
  rfl

end

end QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge
