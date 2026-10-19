/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Promise
public import QuantumAlg.Core.Execution.Reindex
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Reindex

/-!
# State promises under exact physical basis transport

An injective wire placement induces a bijection between the original selected
basis and the placed selected basis. Relabeling a promise through this bijection
preserves both its information and the actual block's probability weight
[dW19, qcnotes.tex:5381,5394].
-/

namespace QuantumAlg.StatePromise

noncomputable section

variable {R S : Register}

/-- Transport the same pure, mixed or dirty target to its placed basis. -/
public def reindex (basis : R.Index ≃ S.Index) : StatePromise R → StatePromise S
  | .dirty => .dirty
  | .pure target => .pure (target.reindex basis)
  | .mixed target normalized =>
      .mixed (target.reindex basis) ((DensityOperator.reindex_mass target basis).trans normalized)

/-- Exact basis transport preserves and reflects the complete mass-weighted promise. -/
public lemma statePromise_reindex_holds_iff (basis : R.Index ≃ S.Index)
    (promise : StatePromise R) (state : DensityOperator R) :
    (promise.reindex basis).Holds (state.reindex basis) ↔ promise.Holds state := by
  cases promise with
  | dirty => rfl
  | pure target =>
      change (state.reindex basis).matrix =
          (state.reindex basis).mass • (DensityOperator.ofPure (target.reindex basis)).matrix ↔ _
      rw [DensityOperator.reindex_mass]
      constructor
      · intro same
        ext row column
        simpa only [DensityOperator.reindex_entry, DensityOperator.ofPure_matrix,
          NormalizedVector.reindex_apply, Equiv.symm_apply_apply, Matrix.smul_apply] using
          congrArg (fun matrix => matrix (basis row) (basis column)) same
      · intro same
        ext row column
        simpa only [DensityOperator.reindex_entry, DensityOperator.ofPure_matrix,
          NormalizedVector.reindex_apply, Matrix.smul_apply] using
          congrArg (fun matrix => matrix (basis.symm row) (basis.symm column)) same
  | mixed target normalized =>
      change (state.reindex basis).matrix =
          (state.reindex basis).mass • (target.reindex basis).matrix ↔ _
      rw [DensityOperator.reindex_mass]
      constructor
      · intro same
        ext row column
        simpa only [DensityOperator.reindex_entry, Equiv.symm_apply_apply,
          Matrix.smul_apply] using
          congrArg (fun matrix => matrix (basis row) (basis column)) same
      · intro same
        ext row column
        simpa only [DensityOperator.reindex_entry, Matrix.smul_apply] using
          congrArg (fun matrix => matrix (basis.symm row) (basis.symm column)) same

end

end QuantumAlg.StatePromise
