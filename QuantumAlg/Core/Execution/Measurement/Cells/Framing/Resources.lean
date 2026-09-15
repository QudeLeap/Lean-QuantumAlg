/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Framing
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual live space of framed measurement-cell allocation

Every visited context contains the entire original frame and a prefix of the
same retained cells. The final context is reached on every path, so its full
resident and auxiliary capacities are the exact actual peaks.
-/

namespace QuantumAlg.Execution.MeasurementCells

variable {kind : ProblemKind}

/-- Actual visited contexts contain the complete frame beside an original allocation prefix. -/
theorem allocateFramed_visitedContexts (ctx frame : RuntimeCtx kind) (dimension : ℕ+)
    (count : Nat) (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (path : (allocateFramed ctx frame dimension count separate).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (allocateFramed ctx frame dimension count separate).visitedContexts path) :
    ∃ used, used ≤ count ∧
      ∃ prefixSeparate : RuntimeCtx.StorageDisjoint (context ctx dimension used) frame,
        visited = (context ctx dimension used).disjointUnion frame prefixSeparate := by
  induction count with
  | zero => exact ⟨0, le_rfl, separate, List.mem_singleton.mp present⟩
  | succ count ih =>
      let middle := context ctx dimension count
      let prefixSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      change visited ∈ (allocateFramed ctx frame dimension count prefixSeparate).visitedContexts
        path.1 ++ [middle.disjointUnion frame prefixSeparate,
          (context ctx dimension (count + 1)).disjointUnion frame separate] at present
      rcases List.mem_append.mp present with earlier | current
      · obtain ⟨used, bounded, prefixProof, equal⟩ := ih prefixSeparate path.1 earlier
        exact ⟨used, Nat.le_succ_of_le bounded, prefixProof, equal⟩
      · rcases List.mem_cons.mp current with equal | last
        · exact ⟨count, Nat.le_succ count, prefixSeparate, equal⟩
        · exact ⟨count + 1, le_rfl, separate, List.mem_singleton.mp last⟩

private theorem final_visited (ctx frame : RuntimeCtx kind) (dimension : ℕ+)
    (count : Nat) (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (path : (allocateFramed ctx frame dimension count separate).Path) :
    (context ctx dimension count).disjointUnion frame separate ∈
      (allocateFramed ctx frame dimension count separate).visitedContexts path := by
  cases count with
  | zero => exact List.mem_singleton_self _
  | succ count =>
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- All retained cells and the entire supplied frame contribute to the exact resident peak. -/
theorem allocateFramed_peakResidentSpace (ctx frame : RuntimeCtx kind) (dimension : ℕ+)
    (count : Nat) (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (path : (allocateFramed ctx frame dimension count separate).Path) :
    (allocateFramed ctx frame dimension count separate).peakResidentSpace path =
      (context ctx dimension count).residentSpace + frame.residentSpace := by
  let code := allocateFramed ctx frame dimension count separate
  have upper := code.peakResidentSpace_le_of_visited path
    ((context ctx dimension count).residentSpace + frame.residentSpace) (by
      intro visited present
      obtain ⟨used, bounded, prefixProof, rfl⟩ :=
        allocateFramed_visitedContexts ctx frame dimension count separate path visited present
      rw [RuntimeCtx.residentSpace_disjointUnion]
      exact fun axis => Nat.add_le_add_right (context_residentSpace_mono ctx dimension bounded axis)
        (frame.residentSpace axis))
  have lower := code.residentSpace_le_peak_of_visited path _
    (final_visited ctx frame dimension count separate path)
  rw [RuntimeCtx.residentSpace_disjointUnion] at lower
  exact le_antisymm upper lower

/-- Fixed storage roles give the same exact auxiliary peak on every actual allocation path. -/
theorem allocateFramed_peakAuxiliarySpace (ctx frame : RuntimeCtx kind) (dimension : ℕ+)
    (count : Nat) (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (path : (allocateFramed ctx frame dimension count separate).Path) :
    (allocateFramed ctx frame dimension count separate).peakAuxiliarySpace path =
      (context ctx dimension count).auxiliarySpace + frame.auxiliarySpace := by
  let code := allocateFramed ctx frame dimension count separate
  have upper := code.peakAuxiliarySpace_le_of_visited path
    ((context ctx dimension count).auxiliarySpace + frame.auxiliarySpace) (by
      intro visited present
      obtain ⟨used, bounded, prefixProof, rfl⟩ :=
        allocateFramed_visitedContexts ctx frame dimension count separate path visited present
      rw [RuntimeCtx.auxiliarySpace_disjointUnion]
      exact fun axis => Nat.add_le_add_right
        (context_auxiliarySpace_mono ctx dimension bounded axis) (frame.auxiliarySpace axis))
  have lower := code.auxiliarySpace_le_peak_of_visited path _
    (final_visited ctx frame dimension count separate path)
  rw [RuntimeCtx.auxiliarySpace_disjointUnion] at lower
  exact le_antisymm upper lower

end QuantumAlg.Execution.MeasurementCells
