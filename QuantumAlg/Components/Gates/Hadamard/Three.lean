/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Three original prefix Hadamards with an untouched suffix

Each gate is an actual default one-qubit operation on its original prefix
wire. The source suffix may have any width and may be entangled with the prefix.
-/

namespace QuantumAlg.Gate.Hadamard
noncomputable section

private def first (oracles : OracleModel) (width : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  Gate.singleQubitAt (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
    oracles Gate.HOp (0 : Fin (1 + width)) rfl

/-- Actual Hadamards on exactly the first three original physical wires. -/
def three (oracles : OracleModel) (width : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (1 + (1 + (1 + width)))).canonicalPlacement.layout :=
  ((first oracles (1 + (1 + width))).seq
    (UnitaryCircuit.onBinarySuffix 1 (first oracles (1 + width)))).seq
    (UnitaryCircuit.onBinarySuffix 1 (UnitaryCircuit.onBinarySuffix 1 (first oracles width)))

/-- The full operator is the tensor of three Hadamards with the identity on the original suffix. -/
lemma threeHadamard_matrix (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    ((three oracles width).binaryMatrix environment) =
      Gate.HOp.tensor (Gate.HOp.tensor
        (Gate.HOp.tensor (1 : UnitaryOperator (Qubits width)))) := by
  simp only [three, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix, first,
    Gate.singleQubitAt_first_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor 1 (HilbertOperator.tensor 1
      (HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1)) 1)) *
    (HilbertOperator.tensor 1 (HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1)) 1) *
      HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1)) 1) = _
  rw [HilbertOperator.tensor_mul_tensor, Matrix.one_mul, Matrix.mul_one,
    HilbertOperator.tensor_mul_tensor, Matrix.one_mul,
    HilbertOperator.tensor_mul_tensor, Matrix.one_mul, Matrix.mul_one]
  rfl

/-- All three native Hadamards are charged; none touches or queries the source suffix. -/
lemma threeHadamard_events (oracles : OracleModel) (width : Nat) :
    (three oracles width).eventCost =
      3 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  simp only [three, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost, first, Gate.singleQubitAt_eventCost,
    show (3 : Nat) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]

/-- The constructed sequential wrapper has three counted native dependency steps. -/
lemma threeHadamard_depth (oracles : OracleModel) (width : Nat) :
    (three oracles width).evaluatedEventDepth (fun _ => 1) = 3 := by
  simp only [three, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth]
  rfl

end
end QuantumAlg.Gate.Hadamard
