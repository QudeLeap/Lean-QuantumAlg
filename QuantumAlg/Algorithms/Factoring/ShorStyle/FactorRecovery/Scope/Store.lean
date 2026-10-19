/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual complete factor-tail workspace entry and release

The seven genuine store pushes and matching reverse pops follow the circuit's
allocation order. Original operands survive as the same structural reads;
their values and correlations are not reconstructed from a semantic input.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Enter the exact seven real scratch heads in allocation order. -/
def enter (N : Nat) (store : Store ctx) : Store (context ctx N) :=
  let base := store.pushWorkspace ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh
  let order := base.pushWorkspace (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh
  let expanded := order.pushWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
  let zero := expanded.pushWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh
  let active := zero.pushWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh
  let positive := active.pushWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh
  positive.pushWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh

/-- Release those exact seven real heads in reverse allocation order. -/
def leave (N : Nat) (store : Store (context ctx N)) : Store ctx :=
  let positive := Store.popWorkspace (positiveContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh store
  let active := Store.popWorkspace (activeContext ctx N).canonicalFreshKey
    .bit (activeContext ctx N).canonicalFreshKey_fresh positive
  let zero := Store.popWorkspace (zeroContext ctx N).canonicalFreshKey
    .bit (zeroContext ctx N).canonicalFreshKey_fresh active
  let expanded := Store.popWorkspace (expandedContext ctx N).canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh zero
  let order := Store.popWorkspace (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1))) (orderContext ctx N).canonicalFreshKey_fresh
    expanded
  let base := Store.popWorkspace (baseContext ctx N).canonicalFreshKey
    (.option (.unsignedWord (phaseBits N + 1))) (baseContext ctx N).canonicalFreshKey_fresh order
  Store.popWorkspace ctx.canonicalFreshKey
    (.canonicalResidue (modulusBits N)) ctx.canonicalFreshKey_fresh base

/-- Every original operand keeps its exact value during real scope entry. -/
lemma enter_read {shape : CShape} (input : CInputRef ctx shape) (store : Store ctx) :
    (enter N store).read (liftInput input) = store.read input := by
  simp only [enter, liftInput, Store.read_pushWorkspace_underWorkspace]

/-- Scope exit reads each surviving original operand from the actual final inner store. -/
lemma leave_read {shape : CShape} (input : CInputRef ctx shape)
    (store : Store (context ctx N)) :
    (leave N store).read input = store.read (liftInput input) := by
  simp only [leave, liftInput, Store.read_popWorkspace_underWorkspace]

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
