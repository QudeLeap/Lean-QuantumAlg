/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope
import all QuantumAlg.Core.Execution.Classical.Workspace
import Mathlib.Data.List.Nodup

/-!
# Actual complete factor-tail workspace key geometry

The real context contains exactly seven fresh heads before its original
frame. Its own context certificate supplies both their pairwise distinction
and their disjointness from every original structural operand.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The seven real scratch keys in their final live-context order. -/
def scratchKeys (ctx : RuntimeCtx kind) (N : Nat) : List StorageKey :=
  [(halfPowerRef ctx N).key, (positiveRef ctx N).key, (activeRef ctx N).key,
    (zeroRef ctx N).key, (expandedRef ctx N).key, (orderRef ctx N).key, (baseRef ctx N).key]

/-- The actual seven heads precede precisely the unchanged original frame. -/
theorem context_keys (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).keys = scratchKeys ctx N ++ ctx.keys := rfl

/-- Physical context well-formedness makes all actual scratch identities distinct. -/
theorem scratchKeys_nodup (ctx : RuntimeCtx kind) (N : Nat) :
    (scratchKeys ctx N).Nodup := by
  have actual : (scratchKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  exact (List.nodup_append.mp actual).1

/-- Distinct allocation positions designate distinct physical scratch keys. -/
theorem scratchKeys_ne (ctx : RuntimeCtx kind) (N : Nat) (first second : Fin 7)
    (different : first ≠ second) :
    (scratchKeys ctx N).get first ≠ (scratchKeys ctx N).get second :=
  fun same => different ((scratchKeys_nodup ctx N).injective_get same)

/-- Actual structural lifting preserves the original operand's exact support. -/
theorem liftInput_keys {shape : CShape} (input : CInputRef ctx shape) :
    (liftInput (N := N) input).storageKeys = input.storageKeys := by
  simp only [liftInput, CInputRef.storageKeys_underWorkspace]

/-- The output keeps its original physical identity through all seven real allocations. -/
theorem liftWrite_key {shape : CShape} (output : CWriteRef ctx shape) :
    (liftWrite (N := N) output).key = output.key := rfl

/-- No real scratch write can alter a pre-existing structural operand. -/
theorem scratchKeys_input_separate {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (scratch : key ∈ scratchKeys ctx N) :
    key ∉ (liftInput (N := N) input).storageKeys := by
  have actual : (scratchKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  rw [liftInput_keys]
  intro present
  exact actual.disjoint scratch (CInputRef.storageKeys_subset_context input present)

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
