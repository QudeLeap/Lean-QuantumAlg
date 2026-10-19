/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Layout.Quantum.Relabeling
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# The full matrix of native suffix execution

The relocated native word retains its original binary operator, with identity
on the complete existing prefix.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

private def pair {prefixWidth suffixWidth : Nat}
    (left : Fin (2 ^ prefixWidth)) (right : Fin (2 ^ suffixWidth)) :=
  (QuantumSignature.qubitsIndexEquiv (prefixWidth + suffixWidth)).symm (prodEquiv (left, right))

private lemma selected_pair {prefixWidth suffixWidth : Nat}
    (left : Fin (2 ^ prefixWidth)) (right : Fin (2 ^ suffixWidth)) :
    ((binarySuffixEmbedding prefixWidth suffixWidth).splitBasis (pair left right)).1 =
      (QuantumSignature.qubitsIndexEquiv suffixWidth).symm right := by
  funext index
  apply Fin.ext
  exact (QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (binarySuffixEmbedding prefixWidth suffixWidth) (pair left right) index).trans
    (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) left right index))

private lemma prefix_outside (prefixWidth suffixWidth : Nat) (index : Fin prefixWidth) :
    Fin.castAdd suffixWidth index ∈ (binarySuffixEmbedding prefixWidth suffixWidth).selectionᶜ := by
  apply Finset.mem_compl.mpr
  intro member
  obtain ⟨position, _, same⟩ := Finset.mem_map.mp member
  have values := congrArg Fin.val same
  change prefixWidth + position.val = index.val at values
  have bound : index.val < prefixWidth := index.isLt
  omega

private lemma outside_prefix (prefixWidth suffixWidth : Nat)
    (position : Fin (prefixWidth + suffixWidth))
    (outside : position ∈ (binarySuffixEmbedding prefixWidth suffixWidth).selectionᶜ) :
    ∃ index : Fin prefixWidth, Fin.castAdd suffixWidth index = position := by
  revert outside
  refine Fin.addCases (fun index => ?_) (fun index => ?_) position
  · intro _
    exact ⟨index, rfl⟩
  · intro outside
    exact False.elim (Finset.mem_compl.mp outside
      (Finset.mem_map_of_mem (binarySuffixEmbedding prefixWidth suffixWidth).position
        (Finset.mem_univ index)))

private lemma complement_pair {prefixWidth suffixWidth : Nat}
    (left first : Fin (2 ^ prefixWidth)) (right second : Fin (2 ^ suffixWidth)) :
    ((binarySuffixEmbedding prefixWidth suffixWidth).splitBasis (pair left right)).2 =
        ((binarySuffixEmbedding prefixWidth suffixWidth).splitBasis (pair first second)).2 ↔
      left = first := by
  constructor
  · intro same
    apply (QuantumSignature.qubitsIndexEquiv prefixWidth).symm.injective
    funext index
    have actual := congrFun same
      ⟨Fin.castAdd suffixWidth index, prefix_outside prefixWidth suffixWidth index⟩
    have one := BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) left right index
    have two := BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) first second index
    apply Fin.ext
    exact (congrArg Fin.val one).symm.trans
      ((congrArg Fin.val actual).trans (congrArg Fin.val two))
  · intro same
    subst first
    funext position
    rw [QuantumLayout.Embedding.embedding_splitBasis_complement_value,
      QuantumLayout.Embedding.embedding_splitBasis_complement_value]
    obtain ⟨index, equal⟩ := outside_prefix prefixWidth suffixWidth position.val position.property
    apply Fin.ext
    rw [← equal]
    exact (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) left right index)).trans
      (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
        (leftWidth := prefixWidth) (rightWidth := suffixWidth) left second index)).symm

/-- Suffix placement retains the exact full operator and every original prefix state. -/
lemma unitaryCircuit_onBinarySuffix_binaryMatrix
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat} (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    ((onBinarySuffix prefixWidth body).binaryMatrix environment) =
      (1 : UnitaryOperator (Qubits prefixWidth)).tensor (body.binaryMatrix environment) := by
  ext row column
  rcases (prodEquiv (m := prefixWidth) (n := suffixWidth)).surjective row with
    ⟨⟨rowLeft, rowRight⟩, rfl⟩
  rcases (prodEquiv (m := prefixWidth) (n := suffixWidth)).surjective column with
    ⟨⟨columnLeft, columnRight⟩, rfl⟩
  rw [UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change (binarySuffixEmbedding prefixWidth suffixWidth).liftOperator
    ((body.relabel (binarySuffixShift prefixWidth)).matrix environment)
    (pair rowLeft rowRight) (pair columnLeft columnRight) = _
  rw [QuantumLayout.Embedding.liftOperator_entry, selected_pair, selected_pair]
  rw [relabel_matrix]
  have same := complement_pair rowLeft columnLeft rowRight columnRight
  change (body.binaryMatrix environment) rowRight columnRight * (if _ then (1 : ℂ) else 0) =
    (if rowLeft = columnLeft then 1 else 0) * (body.binaryMatrix environment) rowRight columnRight
  simp only [same, mul_comm]

/-- Suffix placement applies the body to the suffix state and fixes an
arbitrary normalized prefix state. -/
lemma unitaryCircuit_onBinarySuffix_apply_tensor
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout)
    (prefixState : NormalizedVector (Qubits prefixWidth))
    (suffix : NormalizedVector (Qubits suffixWidth)) (environment : oracles.Interpretation) :
    ((onBinarySuffix prefixWidth body).binaryMatrix environment).apply (prefixState.tensor suffix) =
      prefixState.tensor ((body.binaryMatrix environment).apply suffix) := by
  rw [unitaryCircuit_onBinarySuffix_binaryMatrix,
    UnitaryOperator.tensor_apply_tensor, UnitaryOperator.one_apply]

/-- Suffix placement fixes an arbitrary raw prefix vector and applies the
original word to an arbitrary raw suffix vector. -/
public lemma unitaryCircuit_onBinarySuffix_applyVec_tensor
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits suffixWidth).canonicalPlacement.layout)
    (prefixState : HilbertVector (Qubits prefixWidth))
    (suffix : HilbertVector (Qubits suffixWidth)) (environment : oracles.Interpretation) :
    ((onBinarySuffix prefixWidth body).binaryMatrix environment).applyVec
        (HilbertVector.tensor prefixState suffix) =
      HilbertVector.tensor prefixState ((body.binaryMatrix environment).applyVec suffix) := by
  rw [unitaryCircuit_onBinarySuffix_binaryMatrix,
    UnitaryOperator.tensor_applyVec_tensor, UnitaryOperator.one_applyVec]

/-- Canonical-layout suffix placement has the same binary tensor operator. -/
public lemma onCanonicalBinarySuffix_binaryMatrix
    {gates : GateModel} {oracles : OracleModel} {suffixWidth : Nat}
    (prefixWidth : Nat)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical suffixWidth).toQuantum)
      (environment : oracles.Interpretation) :
    ((onCanonicalBinarySuffix prefixWidth body).binaryMatrix environment) =
      (1 : UnitaryOperator (Qubits prefixWidth)).tensor (body.binaryMatrix environment) := by
  exact unitaryCircuit_onBinarySuffix_binaryMatrix prefixWidth body environment

end

end QuantumAlg.UnitaryCircuit
