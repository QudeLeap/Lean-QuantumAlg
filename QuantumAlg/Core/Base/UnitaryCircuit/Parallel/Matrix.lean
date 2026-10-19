/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Exact matrix of a complete disjoint parallel placement

Two disjoint embeddings whose selections partition the ambient layout give
an intrinsic product basis, even when that layout was not constructed with
`QuantumLayout.append`.  In those coordinates the actual parallel word has
the tensor product of the two source matrices.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {leftCount rightCount count : Nat}
variable {leftLayout : QuantumLayout leftCount}
  {rightLayout : QuantumLayout rightCount} {layout : QuantumLayout count}

/-- The right subsystem basis is the complement of the left selection. -/
@[expose] public def rightComplementEquiv
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ) :
    layout.ComplementBasis leftPlacement.selection ≃ rightLayout.Basis :=
  (rightPlacement.selectedBasisEquiv.trans
    (Equiv.cast (congrArg layout.SelectedBasis partition))).symm

/-- The ambient basis split induced by a complete pair of disjoint placements. -/
@[expose] public def parallelBasisEquiv
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ) :
    layout.Basis ≃ (Register.prod leftLayout.register rightLayout.register).Index :=
  leftPlacement.splitBasis.trans
    (Equiv.prodCongr (Equiv.refl leftLayout.Basis)
      (rightComplementEquiv leftPlacement rightPlacement partition))

/-- The first intrinsic product coordinate is the left physical restriction. -/
@[simp] public lemma parallelBasisEquiv_left
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ)
    (basis : layout.Basis) :
    (parallelBasisEquiv leftPlacement rightPlacement partition basis).1 =
      (leftPlacement.splitBasis basis).1 := rfl

private lemma leftSelection_eq_rightComplement
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ) :
    leftPlacement.selection = rightPlacement.selectionᶜ := by
  have complement := congrArg (fun selection : Finset (Fin count) => selectionᶜ) partition
  simpa only [compl_compl] using complement.symm

private lemma castSelectedBasis_apply_val
    {first second : Finset (Fin count)} (same : first = second)
    (basis : layout.SelectedBasis first)
    (index : QuantumLayout.SelectedPosition second) :
    ((Equiv.cast (congrArg layout.SelectedBasis same)) basis index).val =
      (basis ⟨index.val, same.symm ▸ index.property⟩).val := by
  subst second
  rfl

private def leftComplementEquiv
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ) :
    leftLayout.Basis ≃ layout.ComplementBasis rightPlacement.selection :=
  leftPlacement.selectedBasisEquiv.trans (Equiv.cast
    (congrArg layout.SelectedBasis
      (leftSelection_eq_rightComplement leftPlacement rightPlacement partition)))

private lemma leftComplementEquiv_restrict
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ)
    (basis : layout.Basis) :
    leftComplementEquiv leftPlacement rightPlacement partition
        (leftPlacement.splitBasis basis).1 =
      (rightPlacement.splitBasis basis).2 := by
  funext index
  apply Fin.ext
  let same := leftSelection_eq_rightComplement leftPlacement rightPlacement partition
  let selectedIndex : QuantumLayout.SelectedPosition leftPlacement.selection :=
    ⟨index.val, by simpa only [same] using index.property⟩
  obtain ⟨source, equality⟩ := leftPlacement.positionEquiv.surjective
    selectedIndex
  unfold leftComplementEquiv
  rw [Equiv.trans_apply]
  rw [castSelectedBasis_apply_val (layout := layout) same
    (leftPlacement.selectedBasisEquiv (leftPlacement.splitBasis basis).1) index]
  rw [rightPlacement.embedding_splitBasis_complement_value]
  change (leftPlacement.selectedBasisEquiv
      (leftPlacement.splitBasis basis).1 selectedIndex).val = (basis index.val).val
  rw [← equality, leftPlacement.embedding_selectedBasisEquiv_val,
    leftPlacement.embedding_splitBasis_selected_value]
  exact congrArg (fun position => (basis position).val)
    (congrArg Subtype.val equality)

private lemma rightComplementEquiv_restrict
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ)
    (basis : layout.Basis) :
    rightComplementEquiv leftPlacement rightPlacement partition
        (leftPlacement.splitBasis basis).2 =
      (rightPlacement.splitBasis basis).1 := by
  apply (rightPlacement.selectedBasisEquiv.trans
    (Equiv.cast (congrArg layout.SelectedBasis partition))).injective
  simp only [rightComplementEquiv, Equiv.apply_symm_apply]
  funext index
  apply Fin.ext
  let selectedIndex : QuantumLayout.SelectedPosition rightPlacement.selection :=
    ⟨index.val, by simpa only [partition] using index.property⟩
  obtain ⟨source, equality⟩ := rightPlacement.positionEquiv.surjective
    selectedIndex
  rw [leftPlacement.embedding_splitBasis_complement_value, Equiv.trans_apply]
  rw [castSelectedBasis_apply_val (layout := layout) partition
    (rightPlacement.selectedBasisEquiv (rightPlacement.splitBasis basis).1) index]
  change (basis index.val).val =
    (rightPlacement.selectedBasisEquiv
      (rightPlacement.splitBasis basis).1 selectedIndex).val
  rw [← equality, rightPlacement.embedding_selectedBasisEquiv_val,
    rightPlacement.embedding_splitBasis_selected_value]
  exact congrArg (fun position => (basis position).val)
    (congrArg Subtype.val equality).symm

/-- The second intrinsic product coordinate is the right physical restriction. -/
@[simp] public lemma parallelBasisEquiv_right
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ)
    (basis : layout.Basis) :
    (parallelBasisEquiv leftPlacement rightPlacement partition basis).2 =
      (rightPlacement.splitBasis basis).1 :=
  rightComplementEquiv_restrict leftPlacement rightPlacement partition basis

private lemma left_lift_entry
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ)
    (operator : UnitaryOperator leftLayout.register) (row column : layout.Basis) :
    leftPlacement.liftOperator operator row column =
      operator (parallelBasisEquiv leftPlacement rightPlacement partition row).1
          (parallelBasisEquiv leftPlacement rightPlacement partition column).1 *
        (if (parallelBasisEquiv leftPlacement rightPlacement partition row).2 =
          (parallelBasisEquiv leftPlacement rightPlacement partition column).2 then 1 else 0) := by
  rw [QuantumLayout.Embedding.liftOperator_entry]
  simp only [parallelBasisEquiv_left, parallelBasisEquiv_right]
  have selectedRow := rightComplementEquiv_restrict
    leftPlacement rightPlacement partition row
  have selectedColumn := rightComplementEquiv_restrict
    leftPlacement rightPlacement partition column
  have complementEq :
      (leftPlacement.splitBasis row).2 = (leftPlacement.splitBasis column).2 ↔
        (rightPlacement.splitBasis row).1 = (rightPlacement.splitBasis column).1 := by
    rw [← selectedRow, ← selectedColumn]
    exact (rightComplementEquiv leftPlacement rightPlacement partition).apply_eq_iff_eq.symm
  rw [parallelBasisEquiv_right leftPlacement rightPlacement partition row,
    parallelBasisEquiv_right leftPlacement rightPlacement partition column]
  rw [if_congr complementEq rfl rfl]

private lemma right_lift_entry
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ)
    (operator : UnitaryOperator rightLayout.register) (row column : layout.Basis) :
    rightPlacement.liftOperator operator row column =
      operator (parallelBasisEquiv leftPlacement rightPlacement partition row).2
          (parallelBasisEquiv leftPlacement rightPlacement partition column).2 *
        (if (parallelBasisEquiv leftPlacement rightPlacement partition row).1 =
          (parallelBasisEquiv leftPlacement rightPlacement partition column).1 then 1 else 0) := by
  rw [QuantumLayout.Embedding.liftOperator_entry]
  have selectedRow := rightComplementEquiv_restrict
    leftPlacement rightPlacement partition row
  have selectedColumn := rightComplementEquiv_restrict
    leftPlacement rightPlacement partition column
  have complementRow := leftComplementEquiv_restrict
    leftPlacement rightPlacement partition row
  have complementColumn := leftComplementEquiv_restrict
    leftPlacement rightPlacement partition column
  change operator (rightPlacement.splitBasis row).1
      (rightPlacement.splitBasis column).1 *
      (if (rightPlacement.splitBasis row).2 =
        (rightPlacement.splitBasis column).2 then 1 else 0) = _
  rw [parallelBasisEquiv_left leftPlacement rightPlacement partition row,
    parallelBasisEquiv_left leftPlacement rightPlacement partition column,
    parallelBasisEquiv_right leftPlacement rightPlacement partition row,
    parallelBasisEquiv_right leftPlacement rightPlacement partition column]
  rw [← selectedRow, ← selectedColumn]
  have complementEq :
      (rightPlacement.splitBasis row).2 = (rightPlacement.splitBasis column).2 ↔
        (leftPlacement.splitBasis row).1 = (leftPlacement.splitBasis column).1 := by
    rw [← complementRow, ← complementColumn]
    exact (leftComplementEquiv leftPlacement rightPlacement partition).apply_eq_iff_eq
  rw [if_congr complementEq rfl rfl]

/-- A complete disjoint parallel placement has the exact tensor matrix in its
intrinsic product basis. -/
public lemma parallel_matrix
    (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection)
    (partition : rightPlacement.selection = leftPlacement.selectionᶜ) (environment :
      oracles.Interpretation) :
    ((parallel left right leftPlacement rightPlacement disjoint).matrix environment) =
      UnitaryOperator.reindex
        (parallelBasisEquiv leftPlacement rightPlacement partition).symm
        (UnitaryOperator.prodTensor (left.matrix environment) (right.matrix environment)) := by
  apply Subtype.ext
  funext row column
  rw [parallel_matrix_raw]
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, UnitaryOperator.unitaryOperator_prodTensor_apply]
  let summand : layout.Basis → ℂ := fun index =>
    rightPlacement.liftOperator (right.matrix environment) row index *
      leftPlacement.liftOperator (left.matrix environment) index column
  change (∑ index : layout.Basis, summand index) =
    (left.matrix environment)
        (parallelBasisEquiv leftPlacement rightPlacement partition row).1
        (parallelBasisEquiv leftPlacement rightPlacement partition column).1 *
      (right.matrix environment)
        (parallelBasisEquiv leftPlacement rightPlacement partition row).2
        (parallelBasisEquiv leftPlacement rightPlacement partition column).2
  rw [← Equiv.sum_comp
    (parallelBasisEquiv leftPlacement rightPlacement partition).symm summand]
  change (∑ index : leftLayout.Basis × rightLayout.Basis,
      summand
        ((parallelBasisEquiv leftPlacement rightPlacement partition).symm index)) = _
  have rightEntryPair (index : leftLayout.Basis × rightLayout.Basis) :
      rightPlacement.liftOperator (right.matrix environment) row
          ((parallelBasisEquiv leftPlacement rightPlacement partition).symm index) =
        (right.matrix environment)
            (parallelBasisEquiv leftPlacement rightPlacement partition row).2 index.2 *
          (if (parallelBasisEquiv leftPlacement rightPlacement partition row).1 = index.1
            then 1 else 0) := by
    rw [right_lift_entry leftPlacement rightPlacement partition]
    simp only [Equiv.apply_symm_apply]
  have leftEntryPair (index : leftLayout.Basis × rightLayout.Basis) :
      leftPlacement.liftOperator (left.matrix environment)
          ((parallelBasisEquiv leftPlacement rightPlacement partition).symm index) column =
        (left.matrix environment) index.1
            (parallelBasisEquiv leftPlacement rightPlacement partition column).1 *
          (if index.2 =
            (parallelBasisEquiv leftPlacement rightPlacement partition column).2
            then 1 else 0) := by
    rw [left_lift_entry leftPlacement rightPlacement partition]
    simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [summand, rightEntryPair, leftEntryPair,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm
    ((right.matrix environment)
      (parallelBasisEquiv leftPlacement rightPlacement partition row).2
      (parallelBasisEquiv leftPlacement rightPlacement partition column).2)
    ((left.matrix environment)
      (parallelBasisEquiv leftPlacement rightPlacement partition row).1
      (parallelBasisEquiv leftPlacement rightPlacement partition column).1)

end

end QuantumAlg.UnitaryCircuit
