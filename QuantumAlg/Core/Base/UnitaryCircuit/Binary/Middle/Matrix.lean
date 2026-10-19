/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Middle
public import QuantumAlg.Core.Base.Tensor.Certified
public import QuantumAlg.Util.FinPow
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Middle
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# The full matrix of native execution around a middle field

The relocated native word retains its original operator on the outer fields
and acts as the identity on the complete existing middle field.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

private def pair {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :=
  (QuantumSignature.qubitsIndexEquiv (leftWidth + rightWidth)).symm
    (prodEquiv (left, right))

private def triple {leftWidth middleWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (middle : Fin (2 ^ middleWidth))
    (right : Fin (2 ^ rightWidth)) :=
  (QuantumSignature.qubitsIndexEquiv
    (leftWidth + middleWidth + rightWidth)).symm
      (prodEquiv (prodEquiv (left, middle), right))

private lemma selected_triple {leftWidth middleWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (middle : Fin (2 ^ middleWidth))
    (right : Fin (2 ^ rightWidth)) :
    ((binaryMiddleEmbedding leftWidth middleWidth rightWidth).splitBasis
        (triple left middle right)).1 = pair left right := by
  funext index
  refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index
  · have actual := QuantumLayout.Embedding.embedding_splitBasis_selected_value
      (binaryMiddleEmbedding leftWidth middleWidth rightWidth)
      (triple left middle right) (Fin.castAdd rightWidth leftIndex)
    change
      (((binaryMiddleEmbedding leftWidth middleWidth rightWidth).splitBasis
          (triple left middle right)).1 (Fin.castAdd rightWidth leftIndex)).val =
        (triple left middle right
          (binaryMiddlePosition leftWidth middleWidth rightWidth
            (Fin.castAdd rightWidth leftIndex))).val at actual
    rw [binaryMiddlePosition_left] at actual
    have outer := BinaryBasis.bigEndianEquiv_prod_left
      (prodEquiv (m := leftWidth) (n := middleWidth) (left, middle)) right
      (Fin.castAdd middleWidth leftIndex)
    have inner := BinaryBasis.bigEndianEquiv_prod_left left middle leftIndex
    have source := BinaryBasis.bigEndianEquiv_prod_left left right leftIndex
    apply Fin.ext
    exact actual.trans
      ((congrArg Fin.val outer).trans
        ((congrArg Fin.val inner).trans (congrArg Fin.val source).symm))
  · have actual := QuantumLayout.Embedding.embedding_splitBasis_selected_value
      (binaryMiddleEmbedding leftWidth middleWidth rightWidth)
      (triple left middle right) (Fin.natAdd leftWidth rightIndex)
    change
      (((binaryMiddleEmbedding leftWidth middleWidth rightWidth).splitBasis
          (triple left middle right)).1 (Fin.natAdd leftWidth rightIndex)).val =
        (triple left middle right
          (binaryMiddlePosition leftWidth middleWidth rightWidth
            (Fin.natAdd leftWidth rightIndex))).val at actual
    rw [binaryMiddlePosition_right] at actual
    have outer := BinaryBasis.bigEndianEquiv_prod_right
      (prodEquiv (m := leftWidth) (n := middleWidth) (left, middle)) right rightIndex
    have source := BinaryBasis.bigEndianEquiv_prod_right left right rightIndex
    apply Fin.ext
    exact actual.trans
      ((congrArg Fin.val outer).trans (congrArg Fin.val source).symm)

private lemma middle_outside (leftWidth middleWidth rightWidth : Nat)
    (index : Fin middleWidth) :
    Fin.castAdd rightWidth (Fin.natAdd leftWidth index) ∈
      (binaryMiddleEmbedding leftWidth middleWidth rightWidth).selectionᶜ := by
  apply Finset.mem_compl.mpr
  intro member
  obtain ⟨source, _, same⟩ := Finset.mem_map.mp member
  have values := congrArg Fin.val same
  change binaryMiddleIndex leftWidth middleWidth source.val =
    leftWidth + index.val at values
  unfold binaryMiddleIndex at values
  split at values <;> omega

private lemma outside_middle (leftWidth middleWidth rightWidth : Nat)
    (position : Fin (leftWidth + middleWidth + rightWidth))
    (outside : position ∈
      (binaryMiddleEmbedding leftWidth middleWidth rightWidth).selectionᶜ) :
    ∃ index : Fin middleWidth,
      Fin.castAdd rightWidth (Fin.natAdd leftWidth index) = position := by
  revert outside
  refine Fin.addCases (fun leftMiddle => ?_) (fun rightIndex => ?_) position
  · refine Fin.addCases (fun leftIndex => ?_) (fun middleIndex => ?_) leftMiddle
    · intro outside
      exact False.elim (Finset.mem_compl.mp outside
        (by
          rw [← binaryMiddlePosition_left
            (middleWidth := middleWidth) (rightWidth := rightWidth) leftIndex]
          exact Finset.mem_map_of_mem
            (binaryMiddleEmbedding leftWidth middleWidth rightWidth).position
            (Finset.mem_univ _)))
    · intro _
      exact ⟨middleIndex, rfl⟩
  · intro outside
    exact False.elim (Finset.mem_compl.mp outside
      (by
        rw [← binaryMiddlePosition_right
          (leftWidth := leftWidth) (middleWidth := middleWidth) rightIndex]
        exact Finset.mem_map_of_mem
          (binaryMiddleEmbedding leftWidth middleWidth rightWidth).position
          (Finset.mem_univ _)))

private lemma complement_triple {leftWidth middleWidth rightWidth : Nat}
    (left first : Fin (2 ^ leftWidth))
    (middle second : Fin (2 ^ middleWidth))
    (right third : Fin (2 ^ rightWidth)) :
    ((binaryMiddleEmbedding leftWidth middleWidth rightWidth).splitBasis
        (triple left middle right)).2 =
        ((binaryMiddleEmbedding leftWidth middleWidth rightWidth).splitBasis
          (triple first second third)).2 ↔
      middle = second := by
  constructor
  · intro same
    apply (QuantumSignature.qubitsIndexEquiv middleWidth).symm.injective
    funext index
    have actual := congrFun same
      ⟨Fin.castAdd rightWidth (Fin.natAdd leftWidth index),
        middle_outside leftWidth middleWidth rightWidth index⟩
    have oneOuter := BinaryBasis.bigEndianEquiv_prod_left
      (prodEquiv (m := leftWidth) (n := middleWidth) (left, middle)) right
      (Fin.natAdd leftWidth index)
    have oneInner := BinaryBasis.bigEndianEquiv_prod_right left middle index
    have twoOuter := BinaryBasis.bigEndianEquiv_prod_left
      (prodEquiv (m := leftWidth) (n := middleWidth) (first, second)) third
      (Fin.natAdd leftWidth index)
    have twoInner := BinaryBasis.bigEndianEquiv_prod_right first second index
    apply Fin.ext
    exact (congrArg Fin.val oneInner).symm.trans
      ((congrArg Fin.val oneOuter).symm.trans
        ((congrArg Fin.val actual).trans
          ((congrArg Fin.val twoOuter).trans (congrArg Fin.val twoInner))))
  · intro same
    subst second
    funext position
    rw [QuantumLayout.Embedding.embedding_splitBasis_complement_value,
      QuantumLayout.Embedding.embedding_splitBasis_complement_value]
    obtain ⟨index, equal⟩ := outside_middle leftWidth middleWidth rightWidth
      position.val position.property
    apply Fin.ext
    rw [← equal]
    have oneOuter := BinaryBasis.bigEndianEquiv_prod_left
      (prodEquiv (m := leftWidth) (n := middleWidth) (left, middle)) right
      (Fin.natAdd leftWidth index)
    have oneInner := BinaryBasis.bigEndianEquiv_prod_right left middle index
    have twoOuter := BinaryBasis.bigEndianEquiv_prod_left
      (prodEquiv (m := leftWidth) (n := middleWidth) (first, middle)) third
      (Fin.natAdd leftWidth index)
    have twoInner := BinaryBasis.bigEndianEquiv_prod_right first middle index
    exact (congrArg Fin.val oneOuter).trans
      ((congrArg Fin.val oneInner).trans
        ((congrArg Fin.val twoInner).symm.trans (congrArg Fin.val twoOuter).symm))

/-- Middle placement acts by the original outer-field matrix and an identity
matrix entry on the preserved middle field. -/
public lemma unitaryCircuit_onBinaryMiddle_binaryMatrix_entry
    {gates : GateModel} {oracles : OracleModel}
    {leftWidth middleWidth rightWidth : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout)
    (rowLeft columnLeft : Fin (2 ^ leftWidth))
    (rowMiddle columnMiddle : Fin (2 ^ middleWidth))
    (rowRight columnRight : Fin (2 ^ rightWidth)) (environment : oracles.Interpretation) :
    ((onBinaryMiddle middleWidth body).binaryMatrix environment)
        (prodEquiv (prodEquiv (rowLeft, rowMiddle), rowRight))
        (prodEquiv (prodEquiv (columnLeft, columnMiddle), columnRight)) =
      (body.binaryMatrix environment) (prodEquiv (rowLeft, rowRight))
          (prodEquiv (columnLeft, columnRight)) *
        (if rowMiddle = columnMiddle then 1 else 0) := by
  change (binaryMiddleEmbedding leftWidth middleWidth rightWidth).liftOperator
      ((body.relabel (binaryMiddleShift leftWidth middleWidth)).matrix environment)
      (triple rowLeft rowMiddle rowRight)
      (triple columnLeft columnMiddle columnRight) = _
  rw [QuantumLayout.Embedding.liftOperator_entry, selected_triple, selected_triple,
    relabel_matrix]
  have same := complement_triple rowLeft columnLeft rowMiddle columnMiddle
    rowRight columnRight
  change (body.binaryMatrix environment) (prodEquiv (rowLeft, rowRight))
      (prodEquiv (columnLeft, columnRight)) * (if _ then (1 : ℂ) else 0) = _
  simp only [same]

/-- Insert an arbitrary middle vector between the left and right coordinates
of an outer binary vector. -/
@[expose] public def binaryMiddleVec {leftWidth middleWidth rightWidth : Nat}
    (outer : HilbertVector (Qubits (leftWidth + rightWidth)))
    (middle : HilbertVector (Qubits middleWidth)) :
    HilbertVector (Qubits (leftWidth + middleWidth + rightWidth)) :=
  WithLp.toLp 2 fun index =>
    let outerCoordinates :=
      (prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)).symm index
    let leftMiddle :=
      (prodEquiv (m := leftWidth) (n := middleWidth)).symm outerCoordinates.1
    outer (prodEquiv (leftMiddle.1, outerCoordinates.2)) * middle leftMiddle.2

/-- Pointwise form of middle-vector insertion in the canonical binary basis. -/
@[simp] public lemma binaryMiddleVec_apply
    {leftWidth middleWidth rightWidth : Nat}
    (outer : HilbertVector (Qubits (leftWidth + rightWidth)))
    (middle : HilbertVector (Qubits middleWidth))
    (left : Fin (2 ^ leftWidth)) (center : Fin (2 ^ middleWidth))
    (right : Fin (2 ^ rightWidth)) :
    binaryMiddleVec outer middle (prodEquiv (prodEquiv (left, center), right)) =
      outer (prodEquiv (left, right)) * middle center := by
  simp [binaryMiddleVec]

/-- Inserting a middle vector into a tensor of the two outer fields preserves
their physical order. -/
public lemma binaryMiddleVec_tensor
    {leftWidth middleWidth rightWidth : Nat}
    (left : HilbertVector (Qubits leftWidth))
    (right : HilbertVector (Qubits rightWidth))
    (middle : HilbertVector (Qubits middleWidth)) :
    binaryMiddleVec (HilbertVector.tensor left right) middle =
      HilbertVector.tensor (HilbertVector.tensor left middle) right := by
  apply WithLp.ofLp_injective
  funext index
  obtain ⟨⟨leftMiddle, rightIndex⟩, rfl⟩ :=
    (prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)).surjective index
  obtain ⟨⟨leftIndex, middleIndex⟩, rfl⟩ :=
    (prodEquiv (m := leftWidth) (n := middleWidth)).surjective leftMiddle
  rw [binaryMiddleVec_apply]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Middle placement applies the original word to the two outer fields and
leaves an arbitrary inserted middle vector unchanged. -/
public lemma unitaryCircuit_onBinaryMiddle_applyVec
    {gates : GateModel} {oracles : OracleModel}
    {leftWidth middleWidth rightWidth : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout)
    (outer : HilbertVector (Qubits (leftWidth + rightWidth)))
    (middle : HilbertVector (Qubits middleWidth)) (environment : oracles.Interpretation) :
    ((onBinaryMiddle middleWidth body).binaryMatrix environment).applyVec
        (binaryMiddleVec outer middle) =
      binaryMiddleVec ((body.binaryMatrix environment).applyVec outer) middle := by
  apply WithLp.ofLp_injective
  funext row
  obtain ⟨⟨rowLeftMiddle, rowRight⟩, rfl⟩ :=
    (prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)).surjective row
  obtain ⟨⟨rowLeft, rowMiddle⟩, rfl⟩ :=
    (prodEquiv (m := leftWidth) (n := middleWidth)).surjective rowLeftMiddle
  rw [binaryMiddleVec_apply]
  simp only [UnitaryOperator.applyVec_apply]
  rw [← Equiv.sum_comp
    (prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := leftWidth) (n := middleWidth)),
    Fintype.sum_prod_type]
  simp only [unitaryCircuit_onBinaryMiddle_binaryMatrix_entry,
    binaryMiddleVec_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [← Equiv.sum_comp (prodEquiv (m := leftWidth) (n := rightWidth)),
    Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_eq_single rowMiddle]
  · simp only [if_pos]
    calc
      _ = ∑ right : Fin (2 ^ rightWidth),
          ((body.binaryMatrix environment) (prodEquiv (rowLeft, rowRight))
              (prodEquiv (left, right)) *
            outer (prodEquiv (left, right))) * middle rowMiddle := by
            apply Finset.sum_congr rfl
            intro right _
            ring
      _ = _ := by rw [Finset.sum_mul]
  · intro other _ different
    simp [different.symm]
  · simp

end

end QuantumAlg.UnitaryCircuit
