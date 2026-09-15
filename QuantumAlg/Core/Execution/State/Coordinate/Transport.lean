/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Coordinates

/-!
# Combined exact classical and quantum coordinates

The two bijections together retain every complete classical block and quantum
matrix entry [dW19, qcnotes.tex:5381,5394]. The statements keep both register
carriers explicit, so context-dependent users can instantiate these identities
without unfolding the representation of a physical runtime register.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
  {R S : Register}

/-- The combined coordinate transformation and its inverse restore the complete state. -/
theorem coordinate_transport_inverse [DecidableEq C] (state : ExecutionState C R) (labels : C ≃ D)
    (basis : R.Index ≃ S.Index) :
    (((state.mapClassical labels).reindex basis).mapClassical labels.symm).reindex basis.symm =
      state := by
  rw [coordinate_reindex_mapClassical, coordinate_mapClassical_inverse,
    coordinate_reindex_inverse]

/-- Each combined coordinate entry is the corresponding original complete block entry. -/
theorem coordinate_transport_entry (state : ExecutionState C R) (labels : C ≃ D)
    (basis : R.Index ≃ S.Index) (value : D) (row column : S.Index) :
    (((state.mapClassical labels).reindex basis).block value).matrix row column =
      (state.block (labels.symm value)).matrix (basis.symm row) (basis.symm column) :=
  congrArg (fun density : DensityOperator R =>
    density.matrix (basis.symm row) (basis.symm column))
      (coordinate_mapClassical_block state labels value)

end

end QuantumAlg.ExecutionState
