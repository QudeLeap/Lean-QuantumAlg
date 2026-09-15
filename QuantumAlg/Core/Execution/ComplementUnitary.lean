/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Local.Marginals

/-!
# Joint restoration of selected wires under complementary unitaries

A unitary acting only on the complementary wires preserves every matrix
entry of the selected subsystem together with an arbitrary external reference.
The proof uses the actual physical selection and partial trace
[dW19, qcnotes.tex:5381,5405]. It allocates no runtime system.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def complementReferenceEquiv {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (Reference : Register) :
    (Register.prod layout.register Reference).Index ≃
      (Register.prod (layout.complementRegister selection)
        (Register.prod (layout.selectedRegister selection) Reference)).Index where
  toFun basis :=
    ((layout.selectionBasisEquiv selection basis.1).2,
      ((layout.selectionBasisEquiv selection basis.1).1, basis.2))
  invFun basis := (layout.joinSelectedBasis selection basis.2.1 basis.1, basis.2.2)
  left_inv basis := by
    exact Prod.ext (layout.joinSelectedBasis_restrict selection basis.1) rfl
  right_inv basis := by
    rcases basis with ⟨complement, selected, reference⟩
    simp only [layout.selectionBasisEquiv_join]

private theorem complementReference_operator {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (Reference : Register)
    (operator : UnitaryOperator layout.register)
    (complement : UnitaryOperator (layout.complementRegister selection))
    (factorization : UnitaryOperator.reindex (layout.selectionBasisEquiv selection) operator =
      UnitaryOperator.prodTensor (1 : UnitaryOperator (layout.selectedRegister selection))
        complement) :
    UnitaryOperator.reindex (complementReferenceEquiv layout selection Reference)
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) =
    UnitaryOperator.prodTensor complement
      (1 : UnitaryOperator (Register.prod (layout.selectedRegister selection) Reference)) := by
  apply Subtype.ext
  ext row column
  have entries := congrArg
    (fun value : UnitaryOperator
      (Register.prod (layout.selectedRegister selection) (layout.complementRegister selection)) =>
        value (row.2.1, row.1) (column.2.1, column.1)) factorization
  change operator (layout.joinSelectedBasis selection row.2.1 row.1)
      (layout.joinSelectedBasis selection column.2.1 column.1) =
    (1 : HilbertOperator (layout.selectedRegister selection)) row.2.1 column.2.1 *
      complement row.1 column.1 at entries
  change operator (layout.joinSelectedBasis selection row.2.1 row.1)
      (layout.joinSelectedBasis selection column.2.1 column.1) *
        (1 : HilbertOperator Reference) row.2.2 column.2.2 = _
  rw [entries, UnitaryOperator.prodTensor_apply]
  change (if row.2.1 = column.2.1 then (1 : ℂ) else 0) * complement row.1 column.1 *
      (if row.2.2 = column.2.2 then 1 else 0) =
    complement row.1 column.1 * (if row.2 = column.2 then 1 else 0)
  have pairEquality : row.2 = column.2 ↔
      row.2.1 = column.2.1 ∧ row.2.2 = column.2.2 := Prod.ext_iff
  by_cases sameSelected : row.2.1 = column.2.1
  · by_cases sameReference : row.2.2 = column.2.2
    · have same := pairEquality.mpr ⟨sameSelected, sameReference⟩
      simp only [if_pos sameSelected, if_pos sameReference, if_pos same, one_mul, mul_one]
    · have different : row.2 ≠ column.2 := fun same => sameReference (pairEquality.mp same).2
      simp only [if_pos sameSelected, if_neg sameReference, if_neg different, mul_zero]
  · have different : row.2 ≠ column.2 := fun same => sameSelected (pairEquality.mp same).1
    simp only [if_neg sameSelected, if_neg different, zero_mul, mul_zero]

namespace DensityOperator

/-- Exact complementary action preserves the selected wires and their full reference jointly. -/
theorem observeSelectionWithReference_applyUnitary_complement {count : Nat}
    (layout : QuantumLayout count) (selection : Finset (Fin count))
    (operator : UnitaryOperator layout.register)
    (complement : UnitaryOperator (layout.complementRegister selection))
    (factorization : UnitaryOperator.reindex (layout.selectionBasisEquiv selection) operator =
      UnitaryOperator.prodTensor (1 : UnitaryOperator (layout.selectedRegister selection))
        complement)
    (Reference : Register) (state : DensityOperator (Register.prod layout.register Reference)) :
    observeSelectionWithReference layout selection Reference
      (applyUnitary (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) state) =
    observeSelectionWithReference layout selection Reference state := by
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨selectedRow, refRow⟩
  rcases column with ⟨selectedColumn, refColumn⟩
  rw [observeSelectionWithReference_entry, observeSelectionWithReference_entry]
  have transformed := applyUnitary_reindex
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) state
    (complementReferenceEquiv layout selection Reference)
  rw [complementReference_operator layout selection Reference operator complement factorization]
    at transformed
  have entries (basis : layout.ComplementBasis selection) := congrArg
    (fun density : DensityOperator
      (Register.prod (layout.complementRegister selection)
        (Register.prod (layout.selectedRegister selection) Reference)) =>
      density.matrix (basis, (selectedRow, refRow))
        (basis, (selectedColumn, refColumn))) transformed
  calc
    _ = ∑ basis : layout.ComplementBasis selection,
        (applyUnitary (UnitaryOperator.prodTensor complement
          (1 : UnitaryOperator (Register.prod (layout.selectedRegister selection) Reference)))
          (state.reindex (complementReferenceEquiv layout selection Reference))).matrix
            (basis, (selectedRow, refRow)) (basis, (selectedColumn, refColumn)) :=
      Finset.sum_congr rfl fun basis _ => entries basis
    _ = _ := localUnitary_reference_entry complement
      (state.reindex (complementReferenceEquiv layout selection Reference))
      (selectedRow, refRow) (selectedColumn, refColumn)

end DensityOperator

end

end QuantumAlg
