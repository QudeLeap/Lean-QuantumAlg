/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Full density action determined by exact basis permutation columns

A unitary whose basis columns are the prescribed permuted kets transports
every density entry by that same permutation. In particular, the statement
retains off-diagonal coherence and arbitrary reference coordinates already
included in the register. No actual execution instruction is introduced.
-/

namespace QuantumAlg.DensityOperator

noncomputable section

variable {R : Register}

/-- Unitary conjugation by the forward basis permutation transports both density indices. -/
theorem applyUnitary_ofPerm (state : DensityOperator R) (permutation : Equiv.Perm R.Index) :
    applyUnitary (UnitaryOperator.ofPerm permutation.symm) state =
      state.reindex permutation := by
  classical
  apply DensityOperator.ext
  change (permutation⁻¹ : Equiv.Perm R.Index).permMatrix ℂ * state.matrix *
    ((permutation⁻¹ : Equiv.Perm R.Index).permMatrix ℂ).conjTranspose =
      state.matrix.submatrix permutation.symm permutation.symm
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- Exact permutation action on all kets fixes the action on the complete mixed density. -/
theorem applyUnitary_eq_reindex_of_kets (state : DensityOperator R)
    (operator : UnitaryOperator R) (permutation : Equiv.Perm R.Index)
    (action : ∀ input, operator.applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket (permutation input)).vec) :
    applyUnitary operator state = state.reindex permutation := by
  classical
  have same : operator = UnitaryOperator.ofPerm permutation.symm := by
    apply Subtype.ext
    ext row column
    have actual := action column
    have prescribed := UnitaryOperator.ofPerm_applyVec_ket permutation.symm column
    have vectors := actual.trans prescribed.symm
    have entry := congrArg (fun vector : HilbertVector R => vector row) vectors
    simpa only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using entry
  rw [same, applyUnitary_ofPerm]

/-- A basis-permuting unitary carries the full density support through the same permutation. -/
theorem applyUnitary_support_of_kets (state : DensityOperator R)
    (operator : UnitaryOperator R) (permutation : Equiv.Perm R.Index)
    (action : ∀ input, operator.applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket (permutation input)).vec)
    (before after : R.Index → Prop)
    (preserves : ∀ input, before input → after (permutation input))
    (support : ∀ input, ¬before input → state.matrix input input = 0) :
    ∀ output, ¬after output → (applyUnitary operator state).matrix output output = 0 := by
  intro output outside
  rw [applyUnitary_eq_reindex_of_kets state operator permutation action, reindex_entry]
  apply support
  intro allowed
  have reached := preserves (permutation.symm output) allowed
  rw [Equiv.apply_symm_apply] at reached
  exact outside reached

end

end QuantumAlg.DensityOperator
