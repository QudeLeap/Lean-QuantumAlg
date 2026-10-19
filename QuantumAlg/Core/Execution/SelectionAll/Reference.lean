/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.State.Promise

/-!
# Complete-layout observations retain the external reference

Selecting every actual wire sums a singleton complement and only relabels
the original density coordinates. Both external reference coordinates stay
unchanged. The existing mass-weighted mixed promise is invariant under that
exact relabeling, so full output requirements can use a proved joint density
without expanding its entries again in each algorithm.
-/

namespace QuantumAlg

noncomputable section

namespace DensityOperator

/-- Full wire selection keeps the same density and reference through an exact basis relabeling. -/
lemma observeSelectionWithReference_all {count : Nat} (layout : QuantumLayout count)
    (Reference : Register) (state : DensityOperator (Register.prod layout.register Reference)) :
    observeSelectionWithReference layout Finset.univ Reference state =
      state.reindex (S := Register.prod (layout.selectedRegister Finset.univ) Reference)
        (layout.allSelectedBasisEquiv.prodCongr (Equiv.refl Reference.Index)) := by
  let : Unique (layout.ComplementBasis Finset.univ) :=
    { default := fun index => False.elim ((Finset.mem_compl.mp index.property)
        (Finset.mem_univ _))
      uniq := fun _ => Subsingleton.elim _ _ }
  apply DensityOperator.ext
  ext ⟨row, leftRef⟩ ⟨column, rightRef⟩
  refine (observeSelectionWithReference_entry layout Finset.univ Reference state
    row column leftRef rightRef).trans ?_
  simp only [QuantumLayout.joinSelectedBasis_all, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_nsmul]
  rfl

end DensityOperator

namespace StatePromise

/-- Exact relabeling preserves the existing mixed promise with the same actual block mass. -/
lemma mixed_reindex {R S : Register} (target : DensityOperator R)
    (normalized : target.IsNormalized) (state : DensityOperator R)
    (basis : R.Index ≃ S.Index) (holds : (StatePromise.mixed target normalized).Holds state) :
    (StatePromise.mixed (target.reindex (S := S) basis)
      ((DensityOperator.reindex_mass target basis).trans normalized)).Holds
        (state.reindex (S := S) basis) := by
  change (state.reindex basis).matrix =
    (state.reindex basis).mass • (target.reindex basis).matrix
  rw [DensityOperator.reindex_mass]
  ext row column
  exact congrArg
    (fun matrix : HilbertOperator R => matrix (basis.symm row) (basis.symm column)) holds

/-- A complete-layout observation transports the joint promise
without tracing its reference. -/
lemma mixed_fullSelection {count : Nat} (layout : QuantumLayout count)
    (Reference : Register) (target : DensityOperator (Register.prod layout.register Reference))
    (normalized : target.IsNormalized)
    (state : DensityOperator (Register.prod layout.register Reference))
    (holds : (StatePromise.mixed target normalized).Holds state) :
    (StatePromise.mixed
      (DensityOperator.observeSelectionWithReference layout Finset.univ Reference target)
      ((DensityOperator.observeSelectionWithReference_mass
        layout Finset.univ Reference target).trans normalized)).Holds
      (DensityOperator.observeSelectionWithReference layout Finset.univ Reference state) := by
  change (DensityOperator.observeSelectionWithReference
      layout Finset.univ Reference state).matrix =
    (DensityOperator.observeSelectionWithReference layout Finset.univ Reference state).mass •
      (DensityOperator.observeSelectionWithReference layout Finset.univ Reference target).matrix
  rw [DensityOperator.observeSelectionWithReference_all,
    DensityOperator.observeSelectionWithReference_all]
  exact mixed_reindex (S := Register.prod (layout.selectedRegister Finset.univ) Reference)
    target normalized state
    (layout.allSelectedBasisEquiv.prodCongr (Equiv.refl Reference.Index)) holds

end StatePromise

end

end QuantumAlg
