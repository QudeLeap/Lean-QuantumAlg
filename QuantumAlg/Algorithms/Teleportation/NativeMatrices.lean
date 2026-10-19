/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Construction
public import QuantumAlg.Algorithms.Teleportation.Mathematics
import all QuantumAlg.Algorithms.Teleportation.Construction
import all QuantumAlg.Algorithms.Teleportation.Geometry
import all QuantumAlg.Algorithms.Teleportation.Mathematics
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.SingleQubit.Last.Binary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Exact native words underlying the teleportation channel

The physical CNOT, Hadamard and conditional Pauli words have precisely the
operators in the source's measured protocol [dW19, qcnotes.tex:790,804]. The
context coordinate map preserves actual wire identities and dimensions.
-/

namespace QuantumAlg.QuantumTeleportation.Block

noncomputable section

open Execution Gate

private lemma aliceCnot_binaryMatrix
    (environment : OracleModel.empty.Interpretation) : (aliceCnot.binaryMatrix environment)
    = CNOTOp := by
  unfold UnitaryCircuit.binaryMatrix aliceCnot
  rw [UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm CNOTOp) = CNOTOp
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv 2).symm _

/-- Alice's actual two native gates are exactly the source's premeasurement unitary. -/
lemma teleportation_aliceWord_binaryMatrix (environment : OracleModel.empty.Interpretation) :
    (aliceWord.binaryMatrix environment) = teleportBellMeasure := by
  let cnot : UnitaryCircuit AlgorithmGate.model .empty layout :=
    UnitaryCircuit.onBinaryPrefix 1 aliceCnot
  let hadamard : UnitaryCircuit AlgorithmGate.model .empty layout :=
    Gate.singleQubitAt layout .empty HOp 0 rfl
  have cnotMatrix : (cnot.binaryMatrix environment)
    = CNOTOp.tensor (1 : UnitaryOperator (Qubits 1)) :=
    (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix 1 aliceCnot environment).trans
      (congrArg (fun operator : UnitaryOperator (Qubits 2) =>
        operator.tensor (1 : UnitaryOperator (Qubits 1))) (aliceCnot_binaryMatrix environment))
  have hadamardMatrix : (hadamard.binaryMatrix environment) =
      HOp.tensor (1 : UnitaryOperator (Qubits 2)) :=
    Gate.singleQubitAt_first_binaryMatrix .empty 2 HOp environment
  exact (UnitaryCircuit.unitaryCircuit_binaryMatrix_seq cnot hadamard environment).trans
    (congrArg₂ (fun first second : UnitaryOperator (Qubits 3) => first * second)
      hadamardMatrix cnotMatrix)

private lemma identity_tensor_mul (first second : UnitaryOperator (Qubits 1)) :
    ((1 : UnitaryOperator (Qubits 2)).tensor first) *
      ((1 : UnitaryOperator (Qubits 2)).tensor second) =
        (1 : UnitaryOperator (Qubits 2)).tensor (first * second) := by
  ext row column
  change (HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
      (first : HilbertOperator (Qubits 1)) *
    HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
      (second : HilbertOperator (Qubits 1))) row column =
    HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
      ((first * second : UnitaryOperator (Qubits 1)) : HilbertOperator (Qubits 1)) row column
  rw [HilbertOperator.tensor_mul_tensor, Matrix.one_mul]
  rfl

private lemma selectedLast_binaryMatrix (bit : Bool) (operator : UnitaryOperator (Qubits 1))
    (environment : OracleModel.empty.Interpretation) :
    ((if bit then Gate.singleQubitAt layout .empty operator 2 rfl
      else UnitaryCircuit.identity AlgorithmGate.model .empty layout).binaryMatrix environment) =
        (1 : UnitaryOperator (Qubits 2)).tensor (if bit then operator else 1) := by
  cases bit with
  | false =>
      change ((UnitaryCircuit.identity AlgorithmGate.model .empty
        (QuantumSignature.qubits 3).canonicalPlacement.layout).binaryMatrix environment) =
          (1 : UnitaryOperator (Qubits 2)).tensor (1 : UnitaryOperator (Qubits 1))
      rw [UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
      apply Subtype.ext
      change (1 : HilbertOperator (Qubits 3)) =
        HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
          (1 : HilbertOperator (Qubits 1))
      exact (HilbertOperator.one_tensor_one (m := 2) (n := 1)).symm
  | true =>
      exact Gate.singleQubitAt_last_binaryMatrix .empty 2 operator environment

/-- The actual feedback word acts on Bob alone and implements exactly the selected correction. -/
lemma teleportation_correctionWord_binaryMatrix (first second : Bool)
    (environment : OracleModel.empty.Interpretation) :
    ((correctionWord first second).binaryMatrix environment) =
      (1 : UnitaryOperator (Qubits 2)).tensor (teleportCorrection first second) := by
  let firstWord : UnitaryCircuit AlgorithmGate.model .empty layout :=
    if second then Gate.singleQubitAt layout .empty XOp 2 rfl
    else .identity AlgorithmGate.model .empty layout
  let secondWord : UnitaryCircuit AlgorithmGate.model .empty layout :=
    if first then Gate.singleQubitAt layout .empty ZOp 2 rfl
    else .identity AlgorithmGate.model .empty layout
  calc
    _ = (secondWord.binaryMatrix environment) * (firstWord.binaryMatrix environment) :=
      UnitaryCircuit.unitaryCircuit_binaryMatrix_seq firstWord secondWord environment
    _ = ((1 : UnitaryOperator (Qubits 2)).tensor (if first then ZOp else 1)) *
        ((1 : UnitaryOperator (Qubits 2)).tensor (if second then XOp else 1)) :=
      congrArg₂ (fun left right : UnitaryOperator (Qubits 3) => left * right)
        (selectedLast_binaryMatrix first ZOp environment) (selectedLast_binaryMatrix second XOp
          environment)
    _ = _ := identity_tensor_mul _ _

/-- Moving the words into the live context changes only their explicit basis coordinates. -/
lemma onContext_matrix (word : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation) :
    ((onContext word).matrix environment) =
      UnitaryOperator.reindex binaryBasis.symm (word.binaryMatrix environment) := by
  calc
    _ = UnitaryOperator.reindex
        (basisOfEqualWires layout context.quantumLayout layout_wires_eq_context) (word.matrix
          environment) :=
      Execution.unitaryOfEqualWires_matrix layout context.quantumLayout
        layout_wires_eq_context environment word
    _ = _ := by
      apply Subtype.ext
      ext row column
      let physical := basisOfEqualWires layout context.quantumLayout layout_wires_eq_context
      change (word.matrix environment) (physical.symm row) (physical.symm column) =
        (word.matrix environment) ((QuantumSignature.qubitsIndexEquiv 3).symm
          ((QuantumSignature.qubitsIndexEquiv 3) (physical.symm row)))
          ((QuantumSignature.qubitsIndexEquiv 3).symm
            ((QuantumSignature.qubitsIndexEquiv 3) (physical.symm column)))
      exact congrArg₂ (fun left right : layout.register.Index =>
        ((word.matrix environment) : HilbertOperator layout.register) left right)
        ((QuantumSignature.qubitsIndexEquiv 3).symm_apply_apply (physical.symm row)).symm
        ((QuantumSignature.qubitsIndexEquiv 3).symm_apply_apply (physical.symm column)).symm

end

end QuantumAlg.QuantumTeleportation.Block
