/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.SingleQubit.Last
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Gates.SingleQubit.Last
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Exact tensor matrix of a final native one-qubit operation

The physical prefix and final wire use their original big-endian binary labels.
-/

namespace QuantumAlg.Gate

noncomputable section

private theorem prefixDecoded (width : Nat) (left : Fin (2 ^ width)) (right : Fin 2) :
    (fun index : Fin width =>
      (QuantumSignature.qubitsIndexEquiv (width + 1)).symm
        (prodEquiv (left, right)) index.castSucc) =
      (QuantumSignature.qubitsIndexEquiv width).symm left := by
  funext index
  exact BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := width) (rightWidth := 1) left right index

private theorem lastDecoded (width : Nat) (left : Fin (2 ^ width)) (right : Fin 2) :
    (QuantumSignature.qubitsIndexEquiv (width + 1)).symm
      (prodEquiv (left, right)) (Fin.last width) = right := by
  have original := BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := width) (rightWidth := 1) left right 0
  have last : (BinaryBasis.bigEndianEquiv 1).symm right 0 = right := by
    fin_cases right <;> rfl
  exact original.trans last

/-- The actual final-wire operation has exactly the full identity-tensor-operator matrix. -/
public theorem singleQubitAt_last_binaryMatrix (oracles : OracleModel) (width : Nat)
    (operator : UnitaryOperator (Qubits 1)) :
    (singleQubitAt (QuantumSignature.qubits (width + 1)).canonicalPlacement.layout
      oracles operator (Fin.last width) rfl).binaryMatrix =
        (1 : UnitaryOperator (Qubits width)).tensor operator := by
  ext row column
  rcases (prodEquiv (m := width) (n := 1)).surjective row with ⟨⟨rowLeft, rowRight⟩, rfl⟩
  rcases (prodEquiv (m := width) (n := 1)).surjective column with
    ⟨⟨columnLeft, columnRight⟩, rfl⟩
  rw [UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change (singleQubitAt (QuantumSignature.qubits (width + 1)).canonicalPlacement.layout
    oracles operator (Fin.last width) rfl).matrix
    ((QuantumSignature.qubitsIndexEquiv (width + 1)).symm (prodEquiv (rowLeft, rowRight)))
    ((QuantumSignature.qubitsIndexEquiv (width + 1)).symm
      (prodEquiv (columnLeft, columnRight))) = _
  rw [singleQubitAt_last_matrix_entry, prefixDecoded, prefixDecoded, lastDecoded, lastDecoded]
  have same : (QuantumSignature.qubitsIndexEquiv width).symm rowLeft =
      (QuantumSignature.qubitsIndexEquiv width).symm columnLeft ↔ rowLeft = columnLeft :=
    (QuantumSignature.qubitsIndexEquiv width).symm.injective.eq_iff
  change operator rowRight columnRight * (if _ then (1 : ℂ) else 0) =
    (if rowLeft = columnLeft then 1 else 0) * operator rowRight columnRight
  simp only [same, mul_comm]

end

end QuantumAlg.Gate
