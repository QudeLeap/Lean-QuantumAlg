/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.Local
import all QuantumAlg.Core.Execution.Local.Framing.Resources

/-!
# Actual local execution beside an existing retained cell

A singleton retained frame describes storage already present at entry. The
existing local compiler first keeps that cell as its physical frame, then the
existing entry-permutation compiler identifies the result with the actual
head-cell context. Neither step emits an allocation or introduces another
interpreter. The cell's value is arbitrary and all its correlations remain
part of the complete execution state.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

def retainedLocalFrame {kind : ProblemKind} (key : StorageKey) (shape : CShape) :
    RuntimeCtx kind :=
  RuntimeCtx.empty.addRetained key shape (by simp [RuntimeCtx.keys])

private theorem retainedLocalDisjoint {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    RuntimeCtx.StorageDisjoint ctx (retainedLocalFrame key shape) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint ctx.keys [key]
    exact List.disjoint_singleton.mpr fresh
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint ctx.physicalIdx []
    exact List.disjoint_nil_right _

private theorem retainedLocalPermutation {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.disjointUnion (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh)).entries.Perm
        (ctx.addRetained key shape fresh).entries :=
  List.perm_append_comm

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
  (code : Circuit model ctx ctx) (supported : code.IsLocal)
  (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)

private def retainedFramed :=
  ContextUnion.frameLocal code supported (retainedLocalFrame key shape)
    (retainedLocalDisjoint ctx key shape fresh)

private theorem retainedFramed_isLocal : (retainedFramed code supported key shape fresh).IsLocal :=
  ContextUnion.frameLocal_isLocal code supported (retainedLocalFrame key shape)
    (retainedLocalDisjoint ctx key shape fresh)

/-- Run the same actual local instructions with one existing retained head cell left resident. -/
def underRetained :
    Circuit model (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh) :=
  ContextPermutation.localCircuit (retainedFramed code supported key shape fresh)
    (retainedFramed_isLocal code supported key shape fresh) (ctx.addRetained key shape fresh)
    (retainedLocalPermutation ctx key shape fresh)

/-- Actual outcomes and branch choices correspond exactly to the original local circuit path. -/
def underRetainedPathEquiv : code.Path ≃ (underRetained code supported key shape fresh).Path :=
  (ContextUnion.frameLocalPathEquiv code supported (retainedLocalFrame key shape)
    (retainedLocalDisjoint ctx key shape fresh)).trans
      (ContextPermutation.localPathEquiv (retainedFramed code supported key shape fresh)
        (retainedFramed_isLocal code supported key shape fresh)
        (ctx.addRetained key shape fresh) (retainedLocalPermutation ctx key shape fresh))

/-- The extension remains in the same allocation-free local fragment. -/
theorem underRetained_isLocal : (underRetained code supported key shape fresh).IsLocal :=
  ContextPermutation.localCircuit_isLocal (retainedFramed code supported key shape fresh)
    (retainedFramed_isLocal code supported key shape fresh) (ctx.addRetained key shape fresh)
    (retainedLocalPermutation ctx key shape fresh)

end

end QuantumAlg.Circuit
