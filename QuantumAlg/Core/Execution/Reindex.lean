/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Internal state transport along an actual basis equivalence

Register transport relabels matrix rows and columns by one explicit equivalence
of their basis types. It preserves every entry, probability mass, and classical
label. The equivalence is supplied by the actual register construction; equal
Hilbert dimensions alone do not determine a correspondence of physical systems.

This is a coordinate change for the density-matrix representation
[dW19, qcnotes.tex:5381], with no additional physical operation or event.
-/

section

namespace QuantumAlg

open scoped ComplexOrder

noncomputable section

namespace DensityOperator

variable {R S T : Register}

private theorem reindexMatrix_trace (state : DensityOperator R)
    (basisEquiv : R.Index ≃ S.Index) :
    (state.matrix.submatrix basisEquiv.symm basisEquiv.symm).trace = state.matrix.trace :=
  basisEquiv.symm.sum_comp (fun basis : R.Index => state.matrix basis basis)

/-- Relabel both matrix indices through the same exact basis equivalence. -/
def reindex (state : DensityOperator R) (basisEquiv : R.Index ≃ S.Index) :
    DensityOperator S where
  matrix := state.matrix.submatrix basisEquiv.symm basisEquiv.symm
  positive := state.positive.submatrix basisEquiv.symm
  trace_le_one :=
    (congrArg Complex.re (reindexMatrix_trace (S := S) state basisEquiv)).le.trans
      state.trace_le_one

/-- Matrix entries are transported without changing their complex values. -/
theorem reindex_entry (state : DensityOperator R) (basisEquiv : R.Index ≃ S.Index)
    (row column : S.Index) :
    (reindex (S := S) state basisEquiv).matrix row column =
      state.matrix (basisEquiv.symm row) (basisEquiv.symm column) := rfl

/-- Exact basis relabeling preserves the complete branch probability. -/
theorem reindex_mass (state : DensityOperator R) (basisEquiv : R.Index ≃ S.Index) :
    (reindex (S := S) state basisEquiv).mass = state.mass :=
  congrArg Complex.re (reindexMatrix_trace (S := S) state basisEquiv)

/-- The identity basis equivalence leaves the density operator unchanged. -/
theorem reindex_refl (state : DensityOperator R) :
    reindex (S := R) state (Equiv.refl R.Index) = state := by
  apply DensityOperator.ext
  rfl

/-- Sequential relabeling agrees exactly with composition of the equivalences. -/
theorem reindex_trans (state : DensityOperator R) (first : R.Index ≃ S.Index)
    (second : S.Index ≃ T.Index) :
    reindex (S := T) (reindex (S := S) state first) second =
      reindex (S := T) state (first.trans second) := by
  apply DensityOperator.ext
  rfl

end DensityOperator

namespace ExecutionState

variable {Classical : Type} [Fintype Classical] {R S T : Register}

/-- Relabel the full quantum register in every unchanged classical block. -/
def reindex (state : ExecutionState Classical R) (basisEquiv : R.Index ≃ S.Index) :
    ExecutionState Classical S where
  block value := DensityOperator.reindex (S := S) (state.block value) basisEquiv
  total_le_one := by
    simp only [DensityOperator.reindex_mass]
    exact state.total_le_one

/-- The same exact index correspondence is used in each classical block. -/
theorem reindex_block_entry (state : ExecutionState Classical R)
    (basisEquiv : R.Index ≃ S.Index) (value : Classical) (row column : S.Index) :
    ((reindex (S := S) state basisEquiv).block value).matrix row column =
      (state.block value).matrix (basisEquiv.symm row) (basisEquiv.symm column) := rfl

/-- Relabeling preserves each classical block's probability. -/
theorem reindex_block_mass (state : ExecutionState Classical R)
    (basisEquiv : R.Index ≃ S.Index) (value : Classical) :
    ((reindex (S := S) state basisEquiv).block value).mass = (state.block value).mass :=
  DensityOperator.reindex_mass (S := S) (state.block value) basisEquiv

/-- Relabeling preserves the complete execution mass. -/
theorem reindex_mass (state : ExecutionState Classical R)
    (basisEquiv : R.Index ≃ S.Index) :
    (reindex (S := S) state basisEquiv).mass = state.mass := by
  simp only [mass, reindex_block_mass]

/-- Identity transport leaves every quantum and classical component unchanged. -/
theorem reindex_refl (state : ExecutionState Classical R) :
    reindex (S := R) state (Equiv.refl R.Index) = state := by
  apply ExecutionState.ext
  intro value
  exact DensityOperator.reindex_refl (state.block value)

/-- Execution-state transport follows composition of the actual equivalences. -/
theorem reindex_trans (state : ExecutionState Classical R) (first : R.Index ≃ S.Index)
    (second : S.Index ≃ T.Index) :
    reindex (S := T) (reindex (S := S) state first) second =
      reindex (S := T) state (first.trans second) := by
  apply ExecutionState.ext
  intro value
  exact DensityOperator.reindex_trans (S := S) (T := T) (state.block value) first second

end ExecutionState

end

end QuantumAlg

end
