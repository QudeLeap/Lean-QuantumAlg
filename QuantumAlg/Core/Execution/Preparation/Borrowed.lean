/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Borrowed.Empty

/-!
# Borrowed restoration for fresh owned preparation

When the initial borrowed classical interface has one possible value and no
quantum system is borrowed, preparation still has to restore the complete
external reference. The proof below uses the actual preparation instruction's
joint matrix equation [dW19, qcnotes.tex:5381,6827], retaining the real borrowed
entries and the newly allocated owned systems in their original contexts.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Fresh owned preparation restores the uniquely valued borrowed interface
and every entry of its external reference. -/
theorem borrowedRestored_prepare_noBorrowedQuantum {ctx : RuntimeCtx .quantum}
    [Subsingleton ctx.borrowedClassicalShape.Value]
    (noQuantum : ctx.borrowedQuantumWires = []) {Reference : Register}
    {H : Type} [Fintype H] (state : Execution.State ctx Reference H)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) :
    (Circuit.prepare ctx key layout fresh disjoint preparation).BorrowedRestored Reference state
      ((Circuit.prepare ctx key layout fresh disjoint preparation).execute Reference state) := by
  let : Subsingleton
      (ctx.addOwnedLayout key layout fresh disjoint).borrowedClassicalShape.Value := by
    change Subsingleton ctx.borrowedClassicalShape.Value
    infer_instance
  change Execution.observeBorrowed Reference
    ((Circuit.prepare ctx key layout fresh disjoint preparation).execute Reference state) =
      Execution.observeBorrowed Reference state
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [Execution.observeBorrowed_empty_entry_of_subsingleton
    (ctx := ctx.addOwnedLayout key layout fresh disjoint) noQuantum,
    Execution.observeBorrowed_empty_entry_of_subsingleton noQuantum]
  exact prepare_reference_entry state key layout fresh disjoint preparation refLeft refRight

end

end QuantumAlg.Circuit
