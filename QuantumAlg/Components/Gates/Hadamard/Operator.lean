/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Hadamard targets with untouched trailing qubits

The tensor operator describes a local Hadamard and identity spectators.
Physical execution is supplied separately by the native placement constructors.
-/

namespace QuantumAlg.Gate

noncomputable section

/-- Metadata-free Hadamard action on the leading qubit of a larger register. -/
def leadingHadamardOp (n : Nat) : UnitaryOperator (Qubits (1 + n)) :=
  HOp.tensor (1 : UnitaryOperator (Qubits n))

end

end QuantumAlg.Gate
