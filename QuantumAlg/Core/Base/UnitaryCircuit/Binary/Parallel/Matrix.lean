/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Exact tensor semantics of consecutive parallel binary execution

The proof observes the two physically placed words. It neither grants a tensor
operator as an executable instruction nor replaces their parallel resources.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- The actual parallel construction realizes the exact tensor of its words. -/
public lemma parallelBinary_binaryMatrix {gates : GateModel} {oracles : OracleModel}
    {leftWidth rightWidth : Nat}
    (left : UnitaryCircuit gates oracles
      (QuantumSignature.qubits leftWidth).canonicalPlacement.layout)
    (right : UnitaryCircuit gates oracles
      (QuantumSignature.qubits rightWidth).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    ((parallelBinary left right).binaryMatrix environment) = (left.binaryMatrix
      environment).tensor (right.binaryMatrix environment) := by
  have same : ((parallelBinary left right).matrix environment) =
      (((onBinaryPrefix rightWidth left).seq (onBinarySuffix leftWidth right)).matrix environment)
        := rfl
  rw [binaryMatrix, same]
  change (((onBinaryPrefix rightWidth left).seq (onBinarySuffix leftWidth right)).binaryMatrix
    environment) = _
  rw [unitaryCircuit_binaryMatrix_seq, unitaryCircuit_onBinaryPrefix_binaryMatrix,
    unitaryCircuit_onBinarySuffix_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor 1 ((right.binaryMatrix environment) : HilbertOperator (Qubits
    rightWidth)) *
      HilbertOperator.tensor ((left.binaryMatrix environment) : HilbertOperator (Qubits
        leftWidth)) 1 = _
  rw [HilbertOperator.tensor_mul_tensor, one_mul, mul_one]
  rfl

end

end QuantumAlg.UnitaryCircuit
