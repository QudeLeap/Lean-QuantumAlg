/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope
import all QuantumAlg.Core.Execution.Classical.Workspace
import Mathlib.Data.List.Nodup

/-!
# Actual half-factor scope key geometry

The live context itself proves that the six genuine workspace keys are
pairwise distinct and disjoint from the original frame. No extra separation
assumption is imposed on the public input or its external reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The real scratch keys in their final live-context order. -/
def scratchKeys (ctx : RuntimeCtx kind) (N : Nat) : List StorageKey :=
  [(payloadRef ctx N).key, (upperRef ctx N).key, (lowerRef ctx N).key,
    (modulusRef ctx N).key, (oneRef ctx N).key, (candidateRef ctx N).key]

/-- Those six actual cells precede exactly the unchanged original frame. -/
lemma context_keys (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).keys = scratchKeys ctx N ++ ctx.keys := rfl

/-- The genuine context certificate proves all actual scratch identities distinct. -/
lemma scratchKeys_nodup (ctx : RuntimeCtx kind) (N : Nat) :
    (scratchKeys ctx N).Nodup := by
  have actual : (scratchKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  exact (List.nodup_append.mp actual).1

/-- Any two different positions name physically different scratch cells. -/
lemma scratchKeys_ne (ctx : RuntimeCtx kind) (N : Nat) (first second : Fin 6)
    (different : first ≠ second) :
    (scratchKeys ctx N).get first ≠ (scratchKeys ctx N).get second :=
  fun same => different ((scratchKeys_nodup ctx N).injective_get same)

/-- The actual structural lift leaves every original read support unchanged. -/
lemma liftInput_keys {shape : CShape} (input : CInputRef ctx shape) :
    (liftInput (N := N) input).storageKeys = input.storageKeys := by
  simp only [liftInput, CInputRef.storageKeys_underWorkspace]

/-- The original destination keeps the same physical key under all six true workspace heads. -/
lemma liftWrite_key {shape : CShape} (output : CWriteRef ctx shape) :
    (liftWrite (N := N) output).key = output.key := rfl

/-- Every scratch write is disjoint from every actual pre-existing structural operand. -/
lemma scratchKeys_input_separate {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (scratch : key ∈ scratchKeys ctx N) :
    key ∉ (liftInput (N := N) input).storageKeys := by
  have actual : (scratchKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  rw [liftInput_keys]
  intro present
  exact actual.disjoint scratch
    (CInputRef.storageKeys_subset_context input present)

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
