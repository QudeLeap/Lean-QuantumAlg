/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Base.Accounting.Context.Relabeling
public import Mathlib.Logic.Embedding.Basic
import all QuantumAlg.Core.Base.Accounting.Context.Relabeling
public import Mathlib.Data.List.Perm.Basic

/-!
# Placement of a complete local context inside a caller

A placement maps storage keys and physical identities injectively, retains
every entry's role and dimension, and names the complete resident complement.
The caller differs from the placed local context followed by its complement
only by an entry permutation. In particular, no arbitrary change of quantum
basis or unaccounted state preparation is part of a placement.
-/

namespace QuantumAlg

/-- A physical and storage placement with an explicit, fully resident complement. -/
public structure ContextEmbedding {kind : ProblemKind} (localCtx caller : RuntimeCtx kind) where
  /-- Injective placement of the local storage keys. -/
  keys : StorageKey ↪ StorageKey
  /-- Injective placement of the local physical systems. -/
  physical : Nat ↪ Nat
  /-- Every caller entry not used by the local execution remains resident here. -/
  frame : RuntimeCtx kind
  /-- Local storage and systems cannot overlap the complement. -/
  separate : RuntimeCtx.StorageDisjoint (localCtx.relabel keys physical) frame
  /-- All caller entries, including their roles and shapes, are accounted for. -/
  covers : ((localCtx.relabel keys physical).disjointUnion frame separate).entries.Perm
    caller.entries

end QuantumAlg
