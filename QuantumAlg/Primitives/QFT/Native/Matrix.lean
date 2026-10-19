/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Native QFT operators in the original binary labels

This mathematical projection changes only the labels of the operator computed
from an actual native word. Its composition laws allow reuse of the original
Fourier-matrix proof without replacing execution by an arbitrary operator.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

/-- Express the actual word's operator in the original big-endian integer labels. -/
@[expose] public def onBinaryLabels {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout n))
    (environment : oracles.Interpretation) :
    UnitaryOperator (Qubits n) :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n) (body.matrix environment)

/-- Sequential native execution has the same operator composition order in binary labels. -/
public lemma qftNative_binaryMatrix_seq {oracles : OracleModel} {n : Nat}
    (first second : UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout n))
    (environment : oracles.Interpretation) :
    onBinaryLabels (first.seq second) environment = onBinaryLabels second environment *
      onBinaryLabels first environment := by
  unfold onBinaryLabels
  rw [UnitaryCircuit.seq_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_mul _ (second.matrix environment) (first.matrix
    environment)

/-- The empty native word remains the identity in the original binary labels. -/
public lemma qftNative_binaryMatrix_identity (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    onBinaryLabels (UnitaryCircuit.identity AlgorithmGate.model oracles (QFTPrimitive.layout n))
      environment =
      (1 : UnitaryOperator (Qubits n)) := by
  exact UnitaryOperator.unitaryOperator_reindex_one (QuantumSignature.qubitsIndexEquiv n)

/-- Each expanded subroutine returns its original addressed operator under this projection. -/
public lemma qftNative_primitive_binaryMatrix (oracles : OracleModel) {n : Nat}
    (primitive : QFTPrimitive n)
    (environment : oracles.Interpretation) :
    onBinaryLabels (primitive.circuit oracles) environment = primitive.operator := by
  have actual := QFTPrimitive.qftPrimitive_circuit_matrix (environment := environment) oracles
    primitive
  refine (congrArg
    (UnitaryOperator.reindex (R := (QFTPrimitive.layout n).register) (S := Qubits n)
      (QuantumSignature.qubitsIndexEquiv n)) actual).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n).symm primitive.operator

end

end QuantumAlg.QuantumFourierTransform.Native
