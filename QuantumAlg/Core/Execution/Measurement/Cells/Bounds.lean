/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Live-space bounds for actual finite-cell allocation

Every context visited by the retain sequence is its original context plus
some initial number of the requested finite cells. Their actual resident and
auxiliary capacities increase monotonically. The resulting peak bounds can
be compared with an independent problem budget; no resource witness or extra
runtime execution is introduced.
-/

namespace QuantumAlg.Execution.MeasurementCells

variable {kind : ProblemKind}

/-- Every visited frame contains exactly an already allocated number of the requested cells. -/
theorem allocate_visitedContexts (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (path : (allocate ctx dimension count).Path) (frame : RuntimeCtx kind)
    (present : frame ∈ (allocate ctx dimension count).visitedContexts path) :
    ∃ used, used ≤ count ∧ frame = context ctx dimension used := by
  induction count with
  | zero =>
      have same : frame = ctx := List.mem_singleton.mp present
      exact ⟨0, le_rfl, same⟩
  | succ count ih =>
      change frame ∈ (allocate ctx dimension count).visitedContexts path.1 ++
        [context ctx dimension count, context ctx dimension (count + 1)] at present
      rcases List.mem_append.mp present with previous | current
      · obtain ⟨used, bounded, same⟩ := ih path.1 previous
        exact ⟨used, Nat.le_succ_of_le bounded, same⟩
      · rcases List.mem_cons.mp current with same | last
        · exact ⟨count, Nat.le_succ count, same⟩
        · exact ⟨count + 1, le_rfl, List.mem_singleton.mp last⟩

/-- Every added finite cell contributes its nonnegative actual resident capacity. -/
theorem context_residentSpace_mono (ctx : RuntimeCtx kind) (dimension : ℕ+)
    {used count : Nat} (bounded : used ≤ count) :
    (context ctx dimension used).residentSpace ≤ (context ctx dimension count).residentSpace := by
  rw [context_residentSpace, context_residentSpace]
  intro axis
  change used • SpacePool.ofShape (.finite dimension) axis + ctx.residentSpace axis ≤
    count • SpacePool.ofShape (.finite dimension) axis + ctx.residentSpace axis
  rw [nsmul_eq_mul, nsmul_eq_mul]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ bounded) _

/-- All retained finite cells contribute the same actual auxiliary capacity. -/
theorem context_auxiliarySpace_mono (ctx : RuntimeCtx kind) (dimension : ℕ+)
    {used count : Nat} (bounded : used ≤ count) :
    (context ctx dimension used).auxiliarySpace ≤ (context ctx dimension count).auxiliarySpace := by
  rw [context_auxiliarySpace, context_auxiliarySpace]
  intro axis
  change used • SpacePool.ofShape (.finite dimension) axis + ctx.auxiliarySpace axis ≤
    count • SpacePool.ofShape (.finite dimension) axis + ctx.auxiliarySpace axis
  rw [nsmul_eq_mul, nsmul_eq_mul]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ bounded) _

/-- Actual resident peak is bounded by the complete final retained-cell frame. -/
theorem allocate_peakResidentSpace (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (path : (allocate ctx dimension count).Path) :
    (allocate ctx dimension count).peakResidentSpace path ≤
      (context ctx dimension count).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  obtain ⟨used, bounded, rfl⟩ := allocate_visitedContexts ctx dimension count path frame present
  exact context_residentSpace_mono ctx dimension bounded

/-- Auxiliary peak counts the same retained cells throughout their actual allocation. -/
theorem allocate_peakAuxiliarySpace (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (path : (allocate ctx dimension count).Path) :
    (allocate ctx dimension count).peakAuxiliarySpace path ≤
      (context ctx dimension count).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  obtain ⟨used, bounded, rfl⟩ := allocate_visitedContexts ctx dimension count path frame present
  exact context_auxiliarySpace_mono ctx dimension bounded

end QuantumAlg.Execution.MeasurementCells
