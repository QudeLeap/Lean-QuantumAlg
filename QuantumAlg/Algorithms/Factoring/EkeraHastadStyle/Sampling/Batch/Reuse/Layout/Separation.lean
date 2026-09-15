/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Layout
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Existing measurement cells are separate from the new retained source

Both new sampler cells are fresh relative to the old measurement cells.
Lifting preserves the cells' identities and distinctness. Earlier operands
that avoid the reused measurement cells remain separate after sampling,
which is the precise frame needed by the joint repeated-outcome law.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse

noncomputable section

open Execution

private theorem oldKey_ne_fresh {ctx : RuntimeCtx .quantum} {shape : CShape}
    (input : CWriteRef ctx shape) : input.key ≠ ctx.canonicalFreshKey := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  rw [← same]
  exact List.mem_map_of_mem input.toCStorageRef.present

variable (base : RuntimeCtx .quantum) (N : Nat)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- Real source allocation preserves the identities of all original measurement cells. -/
theorem nativeBatchReuse_cells_key (index : Fin (measurementBits N)) :
    (cells base N originalCells index).key = (originalCells index).key := rfl

/-- Distinct original measurement identities remain distinct after actual source allocation. -/
theorem nativeBatchReuse_cells_distinct
    (distinct : Function.Injective (fun index => (originalCells index).key)) :
    Function.Injective (fun index => (cells base N originalCells index).key) := distinct

/-- No original measurement cell aliases the genuinely fresh retained source sample. -/
theorem nativeBatchReuse_cells_sample_separate (index : Fin (measurementBits N)) :
    (cells base N originalCells index).key ∉
      (CInputRef.storage
        (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef).storageKeys := by
  change (originalCells index).key ∉ [base.canonicalFreshKey]
  exact fun present => oldKey_ne_fresh (originalCells index) (List.mem_singleton.mp present)

/-- No reused measurement write can change the fresh complete dispatch parameter. -/
theorem nativeBatchReuse_cells_parameter_separate (index : Fin (measurementBits N)) :
    (cells base N originalCells index).key ∉ (parameter base N).storageKeys := by
  let prior := (originalCells index).underRetained base.canonicalFreshKey
    (.bits (residueSamplingBits N)) base.canonicalFreshKey_fresh
  change prior.key ∉
    [(ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey]
  exact fun present => oldKey_ne_fresh prior (List.mem_singleton.mp present)

/-- An earlier operand avoids the same measurement identities after the two source allocations. -/
theorem nativeBatchReuse_cells_previous_separate {shape : CShape} (previous : CInputRef base shape)
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    (index : Fin (measurementBits N)) :
    (cells base N originalCells index).key ∉
      (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) previous).storageKeys := by
  change (originalCells index).key ∉ _
  let prior := previous.underRetained base.canonicalFreshKey (.bits (residueSamplingBits N))
    base.canonicalFreshKey_fresh
  have outer := CInputRef.storageKeys_underRetained
    (ctx := ShorStyle.Canonical.Sampler.Retained.sampleContext base N) prior
    (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey
    (ParameterShape N)
    (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey_fresh
  have inner := CInputRef.storageKeys_underRetained previous base.canonicalFreshKey
    (.bits (residueSamplingBits N)) base.canonicalFreshKey_fresh
  exact (congrArg (fun keys : List StorageKey => (originalCells index).key ∉ keys)
    (outer.trans inner)).mpr (separate index)

/-- Parameter, source sample and the protected earlier operand can be observed jointly. -/
theorem nativeBatchReuse_cells_joint_separate {shape : CShape} (previous : CInputRef base shape)
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    (index : Fin (measurementBits N)) :
    (cells base N originalCells index).key ∉
      (CInputRef.product (parameter base N)
        (.product
          (.storage (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef)
          (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) previous))).storageKeys := by
  intro present
  rcases List.mem_append.mp present with parameterKey | later
  · exact nativeBatchReuse_cells_parameter_separate base N originalCells index parameterKey
  · rcases List.mem_append.mp later with sampleKey | previousKey
    · exact nativeBatchReuse_cells_sample_separate base N originalCells index sampleKey
    · exact nativeBatchReuse_cells_previous_separate base N originalCells previous separate
        index previousKey

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse
