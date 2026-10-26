/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Retained.Cells
import all QuantumAlg.Core.Execution.Classical.Retained.Cells
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Live-space peaks for heterogeneous retained-cell allocation

The real `allocate` circuit retains every requested cell. Each intermediate
context is bounded by the complete post-context, separately for resident
and auxiliary space, with no replacement resource witness.
-/

namespace QuantumAlg.Execution.RetainedCells

/-- Every visited resident context fits the complete retained post-context. -/
public lemma allocate_peakResidentSpace {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) :
    ∀ (shapes : List CShape)
      (path : (allocate (model := model) ctx shapes).Path),
      (allocate (model := model) ctx shapes).peakResidentSpace path ≤
        (context ctx shapes).residentSpace := by
  intro shapes
  induction shapes with
  | nil =>
      intro path
      simpa only [allocate, context] using
        (Circuit.peakResidentSpace_id (model := model) (ctx := ctx) path).le
  | cons shape tail ih =>
      intro path
      let prior := context ctx tail
      let key := prior.canonicalFreshKey
      let fresh := prior.canonicalFreshKey_fresh
      change (Circuit.seq (allocate (model := model) ctx tail)
          (Circuit.retain (model := model) prior key shape fresh)).peakResidentSpace path ≤
        (prior.addRetained key shape fresh).residentSpace
      rw [Circuit.peakResidentSpace_seq]
      refine SpacePool.max_le ?_ ?_
      · exact (ih path.1).trans (by
          rw [RuntimeCtx.residentSpace_addRetained]
          exact le_add_of_nonneg_left zero_le)
      · exact (Circuit.peakResidentSpace_retain
          (model := model) (ctx := prior) key shape fresh path.2).le

/-- Every visited auxiliary context fits the complete retained post-context. -/
public lemma allocate_peakAuxiliarySpace {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) :
    ∀ (shapes : List CShape)
      (path : (allocate (model := model) ctx shapes).Path),
      (allocate (model := model) ctx shapes).peakAuxiliarySpace path ≤
        (context ctx shapes).auxiliarySpace := by
  intro shapes
  induction shapes with
  | nil =>
      intro path
      simpa only [allocate, context] using
        (Circuit.peakAuxiliarySpace_id (model := model) (ctx := ctx) path).le
  | cons shape tail ih =>
      intro path
      let prior := context ctx tail
      let key := prior.canonicalFreshKey
      let fresh := prior.canonicalFreshKey_fresh
      change (Circuit.seq (allocate (model := model) ctx tail)
          (Circuit.retain (model := model) prior key shape fresh)).peakAuxiliarySpace path ≤
        (prior.addRetained key shape fresh).auxiliarySpace
      rw [Circuit.peakAuxiliarySpace_seq]
      refine SpacePool.max_le ?_ ?_
      · exact (ih path.1).trans (by
          rw [RuntimeCtx.auxiliarySpace_addRetained]
          exact le_add_of_nonneg_left zero_le)
      · exact (Circuit.peakAuxiliarySpace_retain
          (model := model) (ctx := prior) key shape fresh path.2).le

end QuantumAlg.Execution.RetainedCells
