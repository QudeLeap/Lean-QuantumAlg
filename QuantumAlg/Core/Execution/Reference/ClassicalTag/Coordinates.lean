/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.ClassicalTag
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Diagonal reference tags under classical coordinates and finite sums

These equalities retain the selected tag as a separate classical label.
The original classical maps may be noninjective and the input may contain
arbitrary coherences between distinct tag values.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {C D : Type} [Fintype C] [Fintype D] {Tag R S : Register}

/-- A classical record map never changes the independent external tag coordinate. -/
lemma decodeClassicalTag_mapClassical (state : ExecutionState C (Tag.prod R))
    (update : C → D) :
    decodeClassicalTag (state.mapClassical update) =
      (decodeClassicalTag state).mapClassical (fun record => (update record.1, record.2)) := by
  apply ExecutionState.ext
  rintro ⟨label, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeClassicalTag_entry]
  simp only [mapClassical_block_matrix, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    Fintype.sum_prod_type, Prod.mk.injEq, decodeClassicalTag_entry]
  apply Finset.sum_congr rfl
  intro original _
  by_cases same : update original = label <;> simp [same]

/-- Reindexing the old register commutes with every diagonal tag slice. -/
lemma decodeClassicalTag_reindex (state : ExecutionState C (Tag.prod R))
    (basis : R.Index ≃ S.Index) :
    decodeClassicalTag
        (state.reindex (S := Tag.prod S) ((Equiv.refl Tag.Index).prodCongr basis)) =
      (decodeClassicalTag state).reindex (S := S) basis := by
  apply ExecutionState.ext
  rintro ⟨label, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeClassicalTag_entry, reindex_block_entry, reindex_block_entry,
    decodeClassicalTag_entry]
  rfl

omit [Fintype D] in
/-- Selecting an original classical fiber retains all of its external tag slices. -/
lemma decodeClassicalTag_selectClassical (state : ExecutionState C (Tag.prod R))
    (read : C → D) (value : D) :
    decodeClassicalTag (state.selectClassical read value) =
      (decodeClassicalTag state).selectClassical (fun record => read record.1) value := by
  apply ExecutionState.ext
  rintro ⟨label, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeClassicalTag_entry]
  by_cases selected : read label = value
  · simp only [selectClassical_block, selected, if_true, decodeClassicalTag_entry]
  · simp only [selectClassical_block, selected, if_false, DensityOperator.zero_matrix,
      Matrix.zero_apply]

/-- A finite sum of complete input blocks has exactly the sum of the same tag slices. -/
lemma decodeClassicalTag_finiteSum {I : Type} [Fintype I]
    (states : I → ExecutionState C (Tag.prod R))
    (bounded : ∑ index, (states index).mass ≤ 1) :
    decodeClassicalTag (finiteSum states bounded) =
      finiteSum (fun index => decodeClassicalTag (states index))
        (by simpa only [decodeClassicalTag_mass] using bounded) := by
  apply ExecutionState.ext
  rintro ⟨label, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeClassicalTag_entry]
  simp only [finiteSum_block_matrix, Matrix.sum_apply, decodeClassicalTag_entry]

end

end QuantumAlg.ExecutionState
