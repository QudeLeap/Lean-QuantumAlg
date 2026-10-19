/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Store

/-!
# Coordinates of one existing retained head cell

The disjoint frame and entry permutation describe only the already resident
context. They do not construct or recompile any circuit.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

def retainedLocalFrame {kind : ProblemKind} (key : StorageKey) (shape : CShape) :
    RuntimeCtx kind :=
  RuntimeCtx.empty.addRetained key shape (by simp [RuntimeCtx.keys])

private lemma retainedLocalDisjoint {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    RuntimeCtx.StorageDisjoint ctx (retainedLocalFrame key shape) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint ctx.keys [key]
    exact List.disjoint_singleton.mpr fresh
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint ctx.physicalIdx []
    exact List.disjoint_nil_right _

private lemma retainedLocalPermutation {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.disjointUnion (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh)).entries.Perm
        (ctx.addRetained key shape fresh).entries :=
  List.perm_append_comm

end

end QuantumAlg.Circuit
