/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.SelectionAll

/-!
# A fixed local basis state on the selection of every physical wire

An all-wire observation is an exact coordinate relabeling of the same local
marginal. Its pure basis promise therefore retains the original block mass
and arbitrary external reference, including impossible complete records.
-/

namespace QuantumAlg.StatePromise

noncomputable section

/-- Observing every owned wire transports a full local ket without tracing out any system. -/
lemma pureKet_fullSelection_of_localMarginal {count : Nat}
    (layout : QuantumLayout count) {Reference : Register}
    (state : DensityOperator (layout.register.prod Reference)) (seed : layout.Basis)
    (promised : (StatePromise.pure (NormalizedVector.ket seed)).Holds state.marginalLeft) :
    (StatePromise.pure (NormalizedVector.ket
      (R := layout.selectedRegister Finset.univ)
      (layout.restrictSelectedBasis Finset.univ seed))).Holds
        (DensityOperator.observeSelection layout Finset.univ Reference state) := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  have originalDifferent : layout.allSelectedBasisEquiv.symm row ≠ seed := by
    intro same
    apply different
    exact (layout.allSelectedBasisEquiv.apply_symm_apply row).symm.trans
      (congrArg layout.allSelectedBasisEquiv same)
  rw [DensityOperator.observeSelection_all, DensityOperator.reindex_entry]
  change state.marginalLeft.matrix = state.marginalLeft.mass •
    (DensityOperator.ofPure (NormalizedVector.ket seed)).matrix at promised
  rw [promised, Matrix.smul_apply, DensityOperator.ofPure_matrix]
  simp only [NormalizedVector.ket_apply, if_neg originalDifferent, zero_mul, smul_zero]

end

end QuantumAlg.StatePromise
