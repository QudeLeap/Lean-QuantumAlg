/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context.Embedding
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Context.Relabeling

/-!
# Canonical physical context embeddings

Identity placement, a real resident frame, entry permutation and injective
relabeling all use the same placement descriptor. None inspects or recompiles
a circuit, and all preserve the complete caller context.
-/

namespace QuantumAlg

private lemma entry_relabel_refl {kind : ProblemKind} (entry : RuntimeEntry kind) :
    entry.relabel (Function.Embedding.refl _) (Function.Embedding.refl _) = entry := by
  cases entry <;> rfl

/-- Identity placement retains every original entry and invariant certificate. -/
public lemma runtimeCtx_relabel_refl {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    ctx.relabel (Function.Embedding.refl _) (Function.Embedding.refl _) = ctx := by
  have identity : RuntimeEntry.relabel (kind := kind) (Function.Embedding.refl _)
      (Function.Embedding.refl _) = id := funext entry_relabel_refl
  cases ctx
  simp only [RuntimeCtx.relabel, identity, List.map_id, RuntimeCtx.ofEntries]

namespace ContextEmbedding

variable {kind : ProblemKind}

private lemma separate_empty (ctx : RuntimeCtx kind) :
    RuntimeCtx.StorageDisjoint ctx RuntimeCtx.empty := by
  constructor <;>
    simp [RuntimeCtx.KeysDisjoint, RuntimeCtx.PhysicallyDisjoint,
      RuntimeCtx.keys, RuntimeCtx.physicalIdx, RuntimeCtx.quantumWires]

/-- Embed the actual left context while keeping a separately allocated right frame resident. -/
@[expose] public def alongUnion (localCtx frame : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint localCtx frame) :
    ContextEmbedding localCtx (localCtx.disjointUnion frame separate) where
  keys := Function.Embedding.refl _
  physical := Function.Embedding.refl _
  frame := frame
  separate := by simpa only [runtimeCtx_relabel_refl] using separate
  covers := by
    change ((localCtx.relabel _ _).entries ++ frame.entries).Perm
      (localCtx.entries ++ frame.entries)
    rw [runtimeCtx_relabel_refl]

/-- Embed the right context in the same union while retaining the entire left frame. -/
@[expose] public def alongUnionRight (left right : RuntimeCtx kind)
    (separate : RuntimeCtx.StorageDisjoint left right) :
    ContextEmbedding right (left.disjointUnion right separate) where
  keys := Function.Embedding.refl _
  physical := Function.Embedding.refl _
  frame := left
  separate := by
    rw [runtimeCtx_relabel_refl]
    exact ⟨separate.1.symm, separate.2.symm⟩
  covers := by
    change ((right.relabel _ _).entries ++ left.entries).Perm
      (left.entries ++ right.entries)
    rw [runtimeCtx_relabel_refl]
    exact List.perm_append_comm

/-- Entry order alone changes neither a physical identity nor a storage role. -/
@[expose] public def alongPermutation {source target : RuntimeCtx kind}
    (same : source.entries.Perm target.entries) : ContextEmbedding source target where
  keys := Function.Embedding.refl _
  physical := Function.Embedding.refl _
  frame := RuntimeCtx.empty
  separate := by exact separate_empty _
  covers := by
    change ((source.relabel _ _).entries ++ []).Perm target.entries
    simpa only [runtimeCtx_relabel_refl, List.append_nil] using same

/-- Calling a context-preserving child in its own context needs no additional live storage. -/
@[expose] public def identity (ctx : RuntimeCtx kind) : ContextEmbedding ctx ctx :=
  alongPermutation (List.Perm.refl ctx.entries)

/-- Injectively place every original key and wire without allocating additional systems. -/
@[expose] public def alongRelabeling (ctx : RuntimeCtx kind)
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    ContextEmbedding ctx (ctx.relabel keys physical) where
  keys := keys
  physical := physical
  frame := RuntimeCtx.empty
  separate := by exact separate_empty _
  covers := by
    change ((ctx.relabel keys physical).entries ++ []).Perm
      (ctx.relabel keys physical).entries
    simp only [List.append_nil]
    exact List.Perm.refl _

end ContextEmbedding

end QuantumAlg
