/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Observe

/-!
# Observing every live quantum wire

Selecting all positions relabels the same actual wire values; there is no
discarded physical subsystem. Its local density observation traces only the
external reference [dW19, qcnotes.tex:5381,6827]. The coordinate equivalence
below uses each original wire, including the empty-layout case.
-/

namespace QuantumAlg

noncomputable section

namespace QuantumLayout

def allSelectedBasisEquiv {count : Nat} (layout : QuantumLayout count) :
    layout.Basis ≃ layout.SelectedBasis Finset.univ where
  toFun := layout.restrictSelectedBasis Finset.univ
  invFun selected := fun index => selected ⟨index, Finset.mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance complementAllSubsingleton {count : Nat} (layout : QuantumLayout count) :
    Subsingleton (layout.ComplementBasis Finset.univ) where
  allEq left right := by
    funext index
    have impossible : index.val ∉ (Finset.univ : Finset (Fin count)) :=
      Finset.mem_compl.mp index.property
    exact (impossible (Finset.mem_univ _)).elim

lemma joinSelectedBasis_all {count : Nat} (layout : QuantumLayout count)
    (selected : layout.SelectedBasis Finset.univ)
    (complement : layout.ComplementBasis Finset.univ) :
    layout.joinSelectedBasis Finset.univ selected complement =
      layout.allSelectedBasisEquiv.symm selected := by
  funext index
  simp only [joinSelectedBasis, Finset.mem_univ, dif_pos]
  rfl

end QuantumLayout

namespace DensityOperator

lemma observeSelection_all {count : Nat} (layout : QuantumLayout count)
    (Reference : Register) (state : DensityOperator (Register.prod layout.register Reference)) :
    observeSelection layout Finset.univ Reference state =
      state.marginalLeft.reindex (S := layout.selectedRegister Finset.univ)
        layout.allSelectedBasisEquiv := by
  let : Unique (layout.ComplementBasis Finset.univ) :=
    { default := fun index => False.elim ((Finset.mem_compl.mp index.property)
        (Finset.mem_univ _))
      uniq := fun _ => Subsingleton.elim _ _ }
  apply DensityOperator.ext
  ext row column
  calc
    _ = ∑ reference : Reference.Index, ∑ complement : layout.ComplementBasis Finset.univ,
        state.matrix (layout.joinSelectedBasis Finset.univ row complement, reference)
          (layout.joinSelectedBasis Finset.univ column complement, reference) :=
      observeSelection_entry layout Finset.univ Reference state row column
    _ = ∑ reference : Reference.Index,
        state.matrix (layout.allSelectedBasisEquiv.symm row, reference)
          (layout.allSelectedBasisEquiv.symm column, reference) := by
      simp only [QuantumLayout.joinSelectedBasis_all, Finset.sum_const, Finset.card_univ,
        Fintype.card_unique, one_nsmul]
    _ = _ := (marginalLeft_matrix state (layout.allSelectedBasisEquiv.symm row)
      (layout.allSelectedBasisEquiv.symm column)).symm

end DensityOperator

end

end QuantumAlg
