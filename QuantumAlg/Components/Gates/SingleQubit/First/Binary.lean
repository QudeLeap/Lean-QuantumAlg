/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.SingleQubit.First
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Gates.SingleQubit.First
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Exact tensor matrix of a leading native one-qubit operation

The leading wire and complete physical suffix use their original big-endian binary labels.
-/

namespace QuantumAlg.Gate

noncomputable section

private lemma suffixDecoded (width : Nat) (left : Fin 2) (right : Fin (2 ^ width)) :
    (fun index : Fin width =>
      (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
        (prodEquiv (left, right)) (Fin.natAdd 1 index)) =
      (QuantumSignature.qubitsIndexEquiv width).symm right := by
  funext index
  exact BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := 1) (rightWidth := width) left right index

private lemma firstDecoded (width : Nat) (left : Fin 2) (right : Fin (2 ^ width)) :
    (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
      (prodEquiv (left, right)) (0 : Fin (1 + width)) = left := by
  have original := BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := 1) (rightWidth := width) left right 0
  have first : (BinaryBasis.bigEndianEquiv 1).symm left 0 = left := by
    fin_cases left <;> rfl
  exact original.trans first

/-- The actual leading-wire operation has exactly the full operator-tensor-identity matrix. -/
public lemma singleQubitAt_first_binaryMatrix (oracles : OracleModel) (width : Nat)
    (operator : UnitaryOperator (Qubits 1)) (environment : oracles.Interpretation) :
    ((singleQubitAt (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
      oracles operator (0 : Fin (1 + width)) rfl).binaryMatrix environment) =
        operator.tensor (1 : UnitaryOperator (Qubits width)) := by
  ext row column
  rcases (prodEquiv (m := 1) (n := width)).surjective row with ⟨⟨rowLeft, rowRight⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := width)).surjective column with
    ⟨⟨columnLeft, columnRight⟩, rfl⟩
  rw [UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change ((singleQubitAt (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
    oracles operator (0 : Fin (1 + width)) rfl).matrix environment)
    ((QuantumSignature.qubitsIndexEquiv (1 + width)).symm (prodEquiv (rowLeft, rowRight)))
    ((QuantumSignature.qubitsIndexEquiv (1 + width)).symm
      (prodEquiv (columnLeft, columnRight))) = _
  rw [singleQubitAt_first_matrix_entry, suffixDecoded, suffixDecoded, firstDecoded, firstDecoded]
  have same : (QuantumSignature.qubitsIndexEquiv width).symm rowRight =
      (QuantumSignature.qubitsIndexEquiv width).symm columnRight ↔ rowRight = columnRight :=
    (QuantumSignature.qubitsIndexEquiv width).symm.injective.eq_iff
  change operator rowLeft columnLeft * (if _ then (1 : ℂ) else 0) =
    operator rowLeft columnLeft * (if rowRight = columnRight then 1 else 0)
  simp only [same]

end

end QuantumAlg.Gate
