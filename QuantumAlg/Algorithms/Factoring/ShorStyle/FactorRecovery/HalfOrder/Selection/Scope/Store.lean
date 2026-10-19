/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual entry and release of the half-factor scratch cells

These store maps are exactly the six existing workspace pushes and their
matching reverse-order pops. The same structural lifts preserve every original
read across the actual allocation boundary; they do not reconstruct inputs
or replace their correlations with an external reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Initialize each actual scratch head in its real allocation order. -/
def enter (N : Nat) (store : Store ctx) : Store (context ctx N) :=
  let first := store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
  let second := first.pushWorkspace (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh
  let third := second.pushWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh
  let fourth := third.pushWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh
  let fifth := fourth.pushWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh
  fifth.pushWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh

/-- Release exactly those real scratch cells in reverse allocation order. -/
def leave (N : Nat) (store : Store (context ctx N)) : Store ctx :=
  let fifth := Store.popWorkspace (upperContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (upperContext ctx N).canonicalFreshKey_fresh store
  let fourth := Store.popWorkspace (lowerContext ctx N).canonicalFreshKey
    .bit (lowerContext ctx N).canonicalFreshKey_fresh fifth
  let third := Store.popWorkspace (modulusContext ctx N).canonicalFreshKey
    .bit (modulusContext ctx N).canonicalFreshKey_fresh fourth
  let second := Store.popWorkspace (oneContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (oneContext ctx N).canonicalFreshKey_fresh third
  let first := Store.popWorkspace (candidateContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (candidateContext ctx N).canonicalFreshKey_fresh second
  Store.popWorkspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh first

/-- Actual scope entry preserves each exact original structural read. -/
lemma enter_read {shape : CShape} (input : CInputRef ctx shape) (store : Store ctx) :
    (enter N store).read (liftInput input) = store.read input := by
  simp only [enter, liftInput, Store.read_pushWorkspace_underWorkspace]

/-- Actual scope release exposes the same surviving structural read of the true final store. -/
lemma leave_read {shape : CShape} (input : CInputRef ctx shape)
    (store : Store (context ctx N)) :
    (leave N store).read input = store.read (liftInput input) := by
  simp only [leave, liftInput, Store.read_popWorkspace_underWorkspace]

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
