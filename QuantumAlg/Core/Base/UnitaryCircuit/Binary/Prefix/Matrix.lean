/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# The full matrix of native prefix execution

The ordered native word retains its original binary operator, tensored with
the identity on the complete existing suffix.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

private def pair {prefixWidth suffixWidth : Nat}
    (left : Fin (2 ^ prefixWidth)) (right : Fin (2 ^ suffixWidth)) :=
  (QuantumSignature.qubitsIndexEquiv (prefixWidth + suffixWidth)).symm (prodEquiv (left, right))

private lemma selected_pair {prefixWidth suffixWidth : Nat}
    (left : Fin (2 ^ prefixWidth)) (right : Fin (2 ^ suffixWidth)) :
    ((binaryPrefixEmbedding prefixWidth suffixWidth).splitBasis (pair left right)).1 =
      (QuantumSignature.qubitsIndexEquiv prefixWidth).symm left := by
  funext index
  apply Fin.ext
  exact (QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (binaryPrefixEmbedding prefixWidth suffixWidth) (pair left right) index).trans
    (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) left right index))

private lemma suffix_outside (prefixWidth suffixWidth : Nat) (index : Fin suffixWidth) :
    Fin.natAdd prefixWidth index ∈ (binaryPrefixEmbedding prefixWidth suffixWidth).selectionᶜ := by
  apply Finset.mem_compl.mpr
  intro member
  obtain ⟨position, _, same⟩ := Finset.mem_map.mp member
  have values := congrArg Fin.val same
  change position.val = prefixWidth + index.val at values
  have bound : position.val < prefixWidth := position.isLt
  omega

private lemma outside_suffix (prefixWidth suffixWidth : Nat)
    (position : Fin (prefixWidth + suffixWidth))
    (outside : position ∈ (binaryPrefixEmbedding prefixWidth suffixWidth).selectionᶜ) :
    ∃ index : Fin suffixWidth, Fin.natAdd prefixWidth index = position := by
  revert outside
  refine Fin.addCases (fun index => ?_) (fun index => ?_) position
  · intro outside
    exact False.elim (Finset.mem_compl.mp outside
      (Finset.mem_map_of_mem (binaryPrefixEmbedding prefixWidth suffixWidth).position
        (Finset.mem_univ index)))
  · intro _
    exact ⟨index, rfl⟩

private lemma complement_pair {prefixWidth suffixWidth : Nat}
    (left first : Fin (2 ^ prefixWidth)) (right second : Fin (2 ^ suffixWidth)) :
    ((binaryPrefixEmbedding prefixWidth suffixWidth).splitBasis (pair left right)).2 =
        ((binaryPrefixEmbedding prefixWidth suffixWidth).splitBasis (pair first second)).2 ↔
      right = second := by
  constructor
  · intro same
    apply (QuantumSignature.qubitsIndexEquiv suffixWidth).symm.injective
    funext index
    have actual := congrFun same
      ⟨Fin.natAdd prefixWidth index, suffix_outside prefixWidth suffixWidth index⟩
    have one := BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) left right index
    have two := BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) first second index
    apply Fin.ext
    exact (congrArg Fin.val one).symm.trans
      ((congrArg Fin.val actual).trans (congrArg Fin.val two))
  · intro same
    subst second
    funext position
    rw [QuantumLayout.Embedding.embedding_splitBasis_complement_value,
      QuantumLayout.Embedding.embedding_splitBasis_complement_value]
    obtain ⟨index, equal⟩ := outside_suffix prefixWidth suffixWidth position.val position.property
    apply Fin.ext
    rw [← equal]
    exact (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := prefixWidth) (rightWidth := suffixWidth) left right index)).trans
      (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_right
        (leftWidth := prefixWidth) (rightWidth := suffixWidth) first right index)).symm

/-- Prefix placement retains the exact full operator and identity on every suffix state. -/
public lemma unitaryCircuit_onBinaryPrefix_binaryMatrix
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat} (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    ((onBinaryPrefix suffixWidth body).binaryMatrix environment) =
      (body.binaryMatrix environment).tensor (1 : UnitaryOperator (Qubits suffixWidth)) := by
  ext row column
  rcases (prodEquiv (m := prefixWidth) (n := suffixWidth)).surjective row with
    ⟨⟨rowLeft, rowRight⟩, rfl⟩
  rcases (prodEquiv (m := prefixWidth) (n := suffixWidth)).surjective column with
    ⟨⟨columnLeft, columnRight⟩, rfl⟩
  rw [UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change (binaryPrefixEmbedding prefixWidth suffixWidth).liftOperator (body.matrix environment)
    (pair rowLeft rowRight) (pair columnLeft columnRight) = _
  rw [QuantumLayout.Embedding.liftOperator_entry, selected_pair, selected_pair]
  have same := complement_pair rowLeft columnLeft rowRight columnRight
  change (body.binaryMatrix environment) rowLeft columnLeft * (if _ then (1 : ℂ) else 0) =
    (body.binaryMatrix environment) rowLeft columnLeft * (if rowRight = columnRight then 1 else 0)
  simp only [same]

/-- Prefix placement applies the original word to an arbitrary raw prefix
vector and fixes an arbitrary raw suffix vector. -/
public lemma unitaryCircuit_onBinaryPrefix_applyVec_tensor
    {gates : GateModel} {oracles : OracleModel} {prefixWidth : Nat}
    (suffixWidth : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits prefixWidth).canonicalPlacement.layout)
    (prefixState : HilbertVector (Qubits prefixWidth))
    (suffix : HilbertVector (Qubits suffixWidth)) (environment : oracles.Interpretation) :
    ((onBinaryPrefix suffixWidth body).binaryMatrix environment).applyVec
        (HilbertVector.tensor prefixState suffix) =
      HilbertVector.tensor ((body.binaryMatrix environment).applyVec prefixState) suffix := by
  rw [unitaryCircuit_onBinaryPrefix_binaryMatrix,
    UnitaryOperator.tensor_applyVec_tensor, UnitaryOperator.one_applyVec]

end

end QuantumAlg.UnitaryCircuit
