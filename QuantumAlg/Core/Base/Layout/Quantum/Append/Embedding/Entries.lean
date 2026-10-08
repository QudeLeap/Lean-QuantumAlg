/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Append.Embedding
public import QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Append.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding

/-!
# Matrix entries of the two physical tensor segments

Each local operation retains identity on the entire opposite segment. Basis
coordinates are obtained by splitting the actual appended physical layout.
-/

namespace QuantumAlg.QuantumLayout

noncomputable section

variable {leftCount rightCount : Nat}
variable (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
variable (disjoint : List.Disjoint left.identities right.identities)

private theorem leftSelected (basis : (append left right disjoint).Basis) :
    ((appendLeftEmbedding left right disjoint).splitBasis basis).1 =
      (appendBasisEquiv left right disjoint basis).1 := by
  funext index
  apply Fin.ext
  exact Embedding.embedding_splitBasis_selected_value
    (appendLeftEmbedding left right disjoint) basis index

private theorem notLeft (index : Fin rightCount) :
    Fin.natAdd leftCount index ∉ (appendLeftEmbedding left right disjoint).selection := by
  intro present
  obtain ⟨source, _, same⟩ := Finset.mem_map.mp present
  have value := congrArg Fin.val same
  change source.val = leftCount + index.val at value
  omega

private def leftComplement (index : Fin rightCount) :
    SelectedPosition (appendLeftEmbedding left right disjoint).selectionᶜ :=
  ⟨Fin.natAdd leftCount index, Finset.mem_compl.mpr (notLeft left right disjoint index)⟩

private theorem leftComplement_eq_iff
    (row column : (append left right disjoint).Basis) :
    ((appendLeftEmbedding left right disjoint).splitBasis row).2 =
        ((appendLeftEmbedding left right disjoint).splitBasis column).2 ↔
      (appendBasisEquiv left right disjoint row).2 =
        (appendBasisEquiv left right disjoint column).2 := by
  constructor
  · intro same
    funext index
    apply Fin.ext
    have value := congrArg Fin.val (congrFun same (leftComplement left right disjoint index))
    exact value
  · intro same
    funext index
    apply Fin.ext
    have cases : (∃ first : Fin leftCount, Fin.castAdd rightCount first = index.val) ∨
        (∃ second : Fin rightCount, Fin.natAdd leftCount second = index.val) :=
      Fin.addCases (fun first => Or.inl ⟨first, rfl⟩)
        (fun second => Or.inr ⟨second, rfl⟩) index.val
    rcases cases with ⟨first, equal⟩ | ⟨second, equal⟩
    · have absent := Finset.mem_compl.mp index.property
      exact False.elim (absent
        (equal ▸ Finset.mem_map_of_mem _ (Finset.mem_univ first)))
    · have value := congrArg (fun basis : right.Basis => (basis second).val) same
      change (row index.val).val = (column index.val).val
      rw [← equal]
      exact value

/-- The left operation retains the full identity condition on the right segment. -/
public theorem appendLeftEmbedding_lift_entry (operator : UnitaryOperator left.register)
    (row column : (append left right disjoint).Basis) :
    (appendLeftEmbedding left right disjoint).liftOperator operator row column =
      operator (appendBasisEquiv left right disjoint row).1
        (appendBasisEquiv left right disjoint column).1 *
          (if (appendBasisEquiv left right disjoint row).2 =
            (appendBasisEquiv left right disjoint column).2 then 1 else 0) := by
  rw [Embedding.liftOperator_entry, leftSelected, leftSelected]
  simp only [leftComplement_eq_iff]

private theorem rightSelected (basis : (append left right disjoint).Basis) :
    ((appendRightEmbedding left right disjoint).splitBasis basis).1 =
      (appendBasisEquiv left right disjoint basis).2 := by
  funext index
  apply Fin.ext
  exact Embedding.embedding_splitBasis_selected_value
    (appendRightEmbedding left right disjoint) basis index

private theorem notRight (index : Fin leftCount) :
    Fin.castAdd rightCount index ∉ (appendRightEmbedding left right disjoint).selection := by
  intro present
  obtain ⟨source, _, same⟩ := Finset.mem_map.mp present
  have value := congrArg Fin.val same
  change leftCount + source.val = index.val at value
  omega

private def rightComplement (index : Fin leftCount) :
    SelectedPosition (appendRightEmbedding left right disjoint).selectionᶜ :=
  ⟨Fin.castAdd rightCount index, Finset.mem_compl.mpr (notRight left right disjoint index)⟩

private theorem rightComplement_eq_iff
    (row column : (append left right disjoint).Basis) :
    ((appendRightEmbedding left right disjoint).splitBasis row).2 =
        ((appendRightEmbedding left right disjoint).splitBasis column).2 ↔
      (appendBasisEquiv left right disjoint row).1 =
        (appendBasisEquiv left right disjoint column).1 := by
  constructor
  · intro same
    funext index
    apply Fin.ext
    have value := congrArg Fin.val (congrFun same (rightComplement left right disjoint index))
    exact value
  · intro same
    funext index
    apply Fin.ext
    have cases : (∃ first : Fin leftCount, Fin.castAdd rightCount first = index.val) ∨
        (∃ second : Fin rightCount, Fin.natAdd leftCount second = index.val) :=
      Fin.addCases (fun first => Or.inl ⟨first, rfl⟩)
        (fun second => Or.inr ⟨second, rfl⟩) index.val
    rcases cases with ⟨first, equal⟩ | ⟨second, equal⟩
    · have value := congrArg (fun basis : left.Basis => (basis first).val) same
      change (row index.val).val = (column index.val).val
      rw [← equal]
      exact value
    · have absent := Finset.mem_compl.mp index.property
      exact False.elim (absent
        (equal ▸ Finset.mem_map_of_mem _ (Finset.mem_univ second)))

/-- The right operation retains the full identity condition on the left segment. -/
public theorem appendRightEmbedding_lift_entry (operator : UnitaryOperator right.register)
    (row column : (append left right disjoint).Basis) :
    (appendRightEmbedding left right disjoint).liftOperator operator row column =
      operator (appendBasisEquiv left right disjoint row).2
        (appendBasisEquiv left right disjoint column).2 *
          (if (appendBasisEquiv left right disjoint row).1 =
            (appendBasisEquiv left right disjoint column).1 then 1 else 0) := by
  rw [Embedding.liftOperator_entry, rightSelected, rightSelected]
  simp only [rightComplement_eq_iff]

end

end QuantumAlg.QuantumLayout
