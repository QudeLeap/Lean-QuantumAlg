/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Layout
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Round.Frame
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Intrinsic separation of the actual square-root cells

The concrete six-cell workspace discharges all separation facts required
by the round's stored arithmetic. These facts describe actual storage
positions and do not become preconditions of the caller-facing routine.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The exact nonaliasing facts consumed when composing the actual round's reads. -/
structure Separated (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) : Prop where
  /-- No round destination overwrites the preserved original input. -/
  inputFree : ∀ key ∈ writeKeys refs, key ∉ input.storageKeys
  /-- The candidate addition preserves the root. -/
  candidateRoot : refs.candidate.key ≠ refs.root.key
  /-- The candidate addition preserves the increment. -/
  candidateHalf : refs.candidate.key ≠ refs.half.key
  /-- Full multiplication preserves the root. -/
  squareRoot : refs.square.key ≠ refs.root.key
  /-- Full multiplication preserves the increment. -/
  squareHalf : refs.square.key ≠ refs.half.key
  /-- Full multiplication preserves its tested operand. -/
  squareCandidate : refs.square.key ≠ refs.candidate.key
  /-- The comparison preserves the old root. -/
  decisionRoot : refs.tooLarge.key ≠ refs.root.key
  /-- The comparison preserves the next increment. -/
  decisionHalf : refs.tooLarge.key ≠ refs.half.key
  /-- The comparison preserves the candidate to be copied. -/
  decisionCandidate : refs.tooLarge.key ≠ refs.candidate.key
  /-- Selecting a root preserves the increment and shifting preserves the root. -/
  rootHalf : refs.root.key ≠ refs.half.key

/-- All actual internal cells, in their real context order. -/
def internalKeys (ctx : RuntimeCtx kind) (width : Nat) : List StorageKey :=
  [(tooLargeCell ctx width).key, (squareCell ctx width).key, (candidateCell ctx width).key,
    (halfCell ctx width).key, (rootCell ctx width).key, (wideCell ctx width).key]

/-- Actual context uniqueness supplies the six-cell separation proof. -/
lemma nativeSqrt_internalKeys_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    (internalKeys ctx width).Nodup := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeSqrt_context_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- Every original context key lies outside the six actual new cells. -/
lemma nativeSqrt_internalKeys_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint (internalKeys ctx width) ctx.keys := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeSqrt_context_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

private def cellKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 6) : StorageKey :=
  (internalKeys ctx width).get ⟨index.val, by change index.val < 6; exact index.isLt⟩

private lemma cellKey_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 6) (different : left ≠ right) :
    cellKey ctx width left ≠ cellKey ctx width right := by
  intro same
  have positions := (nativeSqrt_internalKeys_nodup ctx width).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- The actual generated references satisfy the entire internal arithmetic contract. -/
lemma nativeSqrt_round_separated (ctx : RuntimeCtx kind) (width : Nat) :
    Separated (.storage (wideCell ctx width).toCStorageRef) (roundRefs ctx width) where
  inputFree := by
    intro key present
    change key ∉ [(wideCell ctx width).key]
    rw [List.mem_singleton]
    change key ∈ [(candidateCell ctx width).key, (squareCell ctx width).key,
      (tooLargeCell ctx width).key, (rootCell ctx width).key, (halfCell ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl
    · exact cellKey_ne ctx width 2 5 (by decide)
    · exact cellKey_ne ctx width 1 5 (by decide)
    · exact cellKey_ne ctx width 0 5 (by decide)
    · exact cellKey_ne ctx width 4 5 (by decide)
    · exact cellKey_ne ctx width 3 5 (by decide)
  candidateRoot := cellKey_ne ctx width 2 4 (by decide)
  candidateHalf := cellKey_ne ctx width 2 3 (by decide)
  squareRoot := cellKey_ne ctx width 1 4 (by decide)
  squareHalf := cellKey_ne ctx width 1 3 (by decide)
  squareCandidate := cellKey_ne ctx width 1 2 (by decide)
  decisionRoot := cellKey_ne ctx width 0 4 (by decide)
  decisionHalf := cellKey_ne ctx width 0 3 (by decide)
  decisionCandidate := cellKey_ne ctx width 0 2 (by decide)
  rootHalf := cellKey_ne ctx width 4 3 (by decide)

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
