/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Selection.EarlyFactor
import all QuantumAlg.Core.Execution.Classical.Workspace
import Mathlib.Data.List.Nodup

/-!
# The actual four lexical first-factor cells

Recovery holds one modulus-width candidate latch and three Boolean cells.
Each cell is a genuine fresh workspace entry; all parameter and terminal
inputs remain the original structural reads beneath these entries. Global
context key uniqueness supplies every selector separation fact internally.
The owned quantum bank is unchanged by this classical layout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.SelectionLayout

open Execution
open ClassicalRoutines

variable {kind : ProblemKind}

/-- The persistent accepted flag is the first actual lexical cell. -/
def acceptedCtx (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- The selected factor is the one actual modulus-width lexical word. -/
def selectedCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (acceptedCtx ctx).addWorkspace (acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh

/-- Actual scratch cell storing the negated persistent acceptance latch. -/
def availableCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (selectedCtx ctx width).addWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh

/-- The final actual scratch cell stores the predicate consumed by the copy branch. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (availableCtx ctx width).addWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh

/-- Real accepted-cell position beneath the subsequent three entries. -/
def accepted (ctx : RuntimeCtx kind) (width : Nat) : CWriteRef (context ctx width) .bit where
  key := ctx.canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there .here))
  writable := by decide

/-- Real factor-word position beneath the two scratch bits. -/
def selected (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) where
  key := (acceptedCtx ctx).canonicalFreshKey
  role := .workspace
  slot := .there (.there .here)
  writable := by decide

/-- Real availability-bit position beneath the take bit. -/
def available (ctx : RuntimeCtx kind) (width : Nat) : CWriteRef (context ctx width) .bit where
  key := (selectedCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there .here
  writable := by decide

/-- Real take-bit position at the newest actual workspace entry. -/
def take (ctx : RuntimeCtx kind) (width : Nat) : CWriteRef (context ctx width) .bit where
  key := (availableCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .here
  writable := by decide

/-- The existing first-accepted component receives exactly these four physical cells. -/
def refs (ctx : RuntimeCtx kind) (width : Nat) : FirstAccepted.Refs (context ctx width) width where
  accepted := accepted ctx width
  selected := selected ctx width
  available := available ctx width
  take := take ctx width

/-- Lift a real original read through the four concrete workspace entries. -/
def underRead {ctx : RuntimeCtx kind} {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) : CInputRef (context ctx width) shape :=
  let first := input.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let second := first.underWorkspace (acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh
  let third := second.underWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  third.underWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh

/-- Recovery continues to consume the same stored parameter and chronological terminal vector. -/
def inputs {ctx : RuntimeCtx kind} {N : Nat} (original : Inputs ctx N) :
    Inputs (context ctx (modulusBits N)) N where
  parameter := underRead original.parameter (modulusBits N)
  outcomes := underRead original.outcomes (modulusBits N)

/-- The four actual internal keys in their final intrinsic stack order. -/
def internalKeys (ctx : RuntimeCtx kind) (width : Nat) : List StorageKey :=
  [(take ctx width).key, (available ctx width).key,
    (selected ctx width).key, (accepted ctx width).key]

/-- The final real context contains precisely these four new entries and the old entries. -/
lemma nativeRecovery_selection_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).keys = internalKeys ctx width ++ ctx.keys := rfl

/-- Actual context uniqueness proves that all four lexical cells differ. -/
lemma nativeRecovery_selection_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    (internalKeys ctx width).Nodup := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeRecovery_selection_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- Every actual new cell is outside every original caller entry. -/
lemma nativeRecovery_selection_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint (internalKeys ctx width) ctx.keys := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeRecovery_selection_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- Structural lifting does not invent, remove or rename any input storage identity. -/
lemma nativeRecovery_selection_underRead_keys {ctx : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (underRead input width).storageKeys = input.storageKeys := by
  let first : CInputRef (acceptedCtx ctx) shape :=
    input.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let second : CInputRef (selectedCtx ctx width) shape :=
    first.underWorkspace (acceptedCtx ctx).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh
  let third : CInputRef (availableCtx ctx width) shape :=
    second.underWorkspace (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  exact (CInputRef.storageKeys_underWorkspace third (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace second (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh).trans
      ((CInputRef.storageKeys_underWorkspace first (acceptedCtx ctx).canonicalFreshKey
        (.unsignedWord width) (acceptedCtx ctx).canonicalFreshKey_fresh).trans
        (CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey .bit
          ctx.canonicalFreshKey_fresh)))

private def cellKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 4) : StorageKey :=
  (internalKeys ctx width).get ⟨index.val, by change index.val < 4; exact index.isLt⟩

private lemma cellKey_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 4) (different : left ≠ right) :
    cellKey ctx width left ≠ cellKey ctx width right := by
  intro same
  have positions := (nativeRecovery_selection_nodup ctx width).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

private lemma original_free {ctx : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (index : Fin 4) :
    cellKey ctx width index ∉ (underRead input width).storageKeys := by
  rw [nativeRecovery_selection_underRead_keys]
  intro present
  exact List.disjoint_left.mp (nativeRecovery_selection_disjoint ctx width)
    (List.get_mem (internalKeys ctx width) _)
    (input.storageKeys_subset_context present)

/-- Actual fresh positions discharge the selector's entire nonaliasing contract internally. -/
lemma nativeRecovery_selection_early_separated {ctx : RuntimeCtx kind} {N : Nat}
    (original : Inputs ctx N) :
    FirstAccepted.Separated (earlyInputs (inputs original)) (refs ctx (modulusBits N)) where
  availableEligible := original_free (earlyFlag original) (modulusBits N) 1
  availableCandidate := original_free (earlyWord original) (modulusBits N) 1
  takeCandidate := original_free (earlyWord original) (modulusBits N) 0
  availableAccepted := cellKey_ne ctx (modulusBits N) 1 3 (by decide)
  takeAccepted := cellKey_ne ctx (modulusBits N) 0 3 (by decide)
  availableSelected := cellKey_ne ctx (modulusBits N) 1 2 (by decide)
  takeSelected := cellKey_ne ctx (modulusBits N) 0 2 (by decide)
  acceptedSelected := cellKey_ne ctx (modulusBits N) 3 2 (by decide)

/-- The layout does not prepare, discard or replace any physical quantum system. -/
lemma nativeRecovery_selection_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.SelectionLayout
