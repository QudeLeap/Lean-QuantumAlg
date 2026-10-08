/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# A native operation on the sole physical qubit

The one-wire binary view is exactly the supplied certified one-qubit
operator. This is a placement theorem, without a new native instruction.
-/

namespace QuantumAlg.Gate

noncomputable section

/-- On a single physical qubit, the native binary matrix is the supplied operator. -/
public theorem singleQubitAt_singleton_binaryMatrix (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    (singleQubitAt (QuantumSignature.qubits 1).canonicalPlacement.layout
      oracles operator (0 : Fin 1) rfl).binaryMatrix = operator := by
  have actual := singleQubitAt_first_binaryMatrix oracles 0 operator
  change (singleQubitAt (QuantumSignature.qubits 1).canonicalPlacement.layout
    oracles operator (0 : Fin 1) rfl).binaryMatrix =
      operator.tensor (1 : UnitaryOperator (Qubits 0))
    at actual
  rw [actual]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [UnitaryOperator.tensor_apply, prodEquiv, finProdFinEquiv, Matrix.one_apply] <;> rfl

end

end QuantumAlg.Gate
