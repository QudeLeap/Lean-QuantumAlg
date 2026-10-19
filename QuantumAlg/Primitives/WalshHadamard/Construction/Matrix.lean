/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Primitives.WalshHadamard.Construction
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Primitives.WalshHadamard.Pipeline
import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Oracle.Xor.Model
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Exact matrices of the native phase-query pipeline

The initial, query and final stages retain the original full operators and
target spectator state [dW19, qcnotes.tex:1005-1006,1149-1173].
-/

namespace QuantumAlg.WalshHadamard.Native

noncomputable section

open Gate.HadamardLayer

private lemma prefixDecoded (width : Nat) (left : Fin (2 ^ width)) (right : Fin 2) :
    (QuantumLayout.appendBasisEquiv (layout width) (lastLayout width)
      (hadamardLayer_layout_disjoint width)
      ((hadamardLayer_layout_append width).symm ▸
        (QuantumSignature.qubitsIndexEquiv (width + 1)).symm (prodEquiv (left, right)))).1 =
      (QuantumSignature.qubitsIndexEquiv width).symm left := by
  funext index
  apply Fin.ext
  have value := UnitaryCircuit.castLayout_basis_value
    (hadamardLayer_layout_append width).symm
    ((QuantumSignature.qubitsIndexEquiv (width + 1)).symm (prodEquiv (left, right)))
    (Fin.castAdd 1 index)
  have leftValue := congrArg Fin.val
    (BinaryBasis.bigEndianEquiv_prod_left (leftWidth := width) (rightWidth := 1) left right index)
  exact value.trans leftValue

private lemma suffixDecoded (width : Nat) (left : Fin (2 ^ width)) (right : Fin 2) :
    (QuantumLayout.appendBasisEquiv (layout width) (lastLayout width)
      (hadamardLayer_layout_disjoint width)
      ((hadamardLayer_layout_append width).symm ▸
        (QuantumSignature.qubitsIndexEquiv (width + 1)).symm (prodEquiv (left, right)))).2 =
      (fun _ : Fin 1 => right) := by
  funext index
  fin_cases index
  apply Fin.ext
  have value := UnitaryCircuit.castLayout_basis_value
    (hadamardLayer_layout_append width).symm
    ((QuantumSignature.qubitsIndexEquiv (width + 1)).symm (prodEquiv (left, right)))
    (Fin.natAdd width 0)
  have last : (BinaryBasis.bigEndianEquiv 1).symm right 0 = right := by
    fin_cases right <;> rfl
  have rightValue := congrArg Fin.val
    (BinaryBasis.bigEndianEquiv_prod_right (leftWidth := width) (rightWidth := 1) left right 0)
  exact value.trans (rightValue.trans (congrArg Fin.val last))

private lemma spectator_entry (width : Nat) (row column : Fin 2) :
    (1 : UnitaryOperator (lastLayout width).register)
      (fun _ : Fin 1 => row) (fun _ : Fin 1 => column) =
        (1 : UnitaryOperator (Qubits 1)) row column := by
  change (if (fun _ : Fin 1 => row) = (fun _ : Fin 1 => column) then (1 : ℂ) else 0) =
    if row = column then 1 else 0
  have same : (fun _ : Fin 1 => row) = (fun _ : Fin 1 => column) ↔ row = column := by
    constructor
    · intro equality
      exact congrFun equality 0
    · intro equality
      subst column
      rfl
  simp only [same]

/-- The actual final stage preserves the entire target state, with its original matrix. -/
lemma walshNative_finalLayer_binaryMatrix (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    ((finalLayer oracles width).binaryMatrix environment) = finalHadamardOperator width := by
  ext row column
  rcases (prodEquiv (m := width) (n := 1)).surjective row with ⟨⟨rowLeft, rowRight⟩, rfl⟩
  rcases (prodEquiv (m := width) (n := 1)).surjective column with
    ⟨⟨columnLeft, columnRight⟩, rfl⟩
  rw [finalHadamardOperator, UnitaryOperator.tensor_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  change ((finalLayer oracles width).matrix environment)
    ((QuantumSignature.qubitsIndexEquiv (width + 1)).symm (prodEquiv (rowLeft, rowRight)))
    ((QuantumSignature.qubitsIndexEquiv (width + 1)).symm
      (prodEquiv (columnLeft, columnRight))) = _
  rw [finalLayer, UnitaryCircuit.castLayout_matrix_entry,
    UnitaryCircuit.tensor_native_matrix_entry, prefixDecoded, prefixDecoded,
    suffixDecoded, suffixDecoded, UnitaryCircuit.identity_matrix]
  exact congrArg₂ (· * ·)
    (congrArg (fun operator : UnitaryOperator (Qubits width) => operator rowLeft columnLeft)
      (native_binary_matrix oracles width environment))
    (spectator_entry width rowRight columnRight)

/-- The initial full layer equals the original input-register/target tensor operator. -/
lemma walshNative_initialLayer_binaryMatrix (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    ((Gate.HadamardLayer.circuit oracles (width + 1)).binaryMatrix environment) =
      initialHadamardOperator width := by
  change binaryOperator oracles (width + 1) environment = _
  rw [native_binary_matrix]
  ext row column
  rcases (prodEquiv (m := width) (n := 1)).surjective row with ⟨⟨rowLeft, rowRight⟩, rfl⟩
  rcases (prodEquiv (m := width) (n := 1)).surjective column with
    ⟨⟨columnLeft, columnRight⟩, rfl⟩
  rw [initialHadamardOperator, UnitaryOperator.tensor_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, hadamardLayerOperator_apply, hadamardLayerOperator_apply,
    invSqrtCard_succ, walshSign_prodEquiv]
  fin_cases rowRight <;> fin_cases columnRight <;>
    simp [Gate.HOp, walshSign, dotParity, bit]

/-- The actual declared XOR query retains the original binary-label operator. -/
lemma walshNative_query_binaryMatrix {width : Nat} (function : Fin (2 ^ width) → Bool) :
    ((XorOracle.circuit AlgorithmGate.model width).binaryMatrix
      (XorOracle.interpretation function)) = xorOracleOp function := by
  unfold UnitaryCircuit.binaryMatrix
  rw [XorOracle.xorOracle_native_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (width + 1)).symm (xorOracleOp function)

/-- All three actual stages compose to the original full phase-query operator. -/
lemma walshNative_queryPipeline_binaryMatrix {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    ((queryPipeline width).binaryMatrix (XorOracle.interpretation function)) =
      finalHadamardOperator width * (xorOracleOp function * initialHadamardOperator width) := by
  rw [queryPipeline, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, walshNative_initialLayer_binaryMatrix,
    walshNative_query_binaryMatrix, walshNative_finalLayer_binaryMatrix]

/-- The actual native pipeline reaches the original normalized final joint state. -/
lemma walshNative_queryPipeline_apply_input {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    ((queryPipeline width).binaryMatrix
      (XorOracle.interpretation function)).apply (input width) = finalJointState function := by
  rw [walshNative_queryPipeline_binaryMatrix]
  apply NormalizedVector.ext
  intro index
  change ((finalHadamardOperator width *
    (xorOracleOp function * initialHadamardOperator width)).applyVec
      (input width : HilbertVector (Qubits (width + 1)))) index = _
  rw [UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec]
  rfl

end

end QuantumAlg.WalshHadamard.Native
