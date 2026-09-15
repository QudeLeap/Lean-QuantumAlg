/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Layout
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Read and separation laws of the actual half-power GCD operand scopes

The adjacent and modulus words receive genuine fresh keys in successive
contexts. Every pre-existing destination is distinct from both words. Store
entry and release below are precisely the two existing workspace operations.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The two actual operand cells are distinct by the second allocation's freshness. -/
theorem adjacent_ne_modulus (ctx : RuntimeCtx kind) (N : Nat) :
    (adjacentRef ctx N).key ≠ (modulusRef ctx N).key := by
  intro same
  change ctx.canonicalFreshKey = (adjacentContext ctx N).canonicalFreshKey at same
  apply (adjacentContext ctx N).canonicalFreshKey_fresh
  rw [← same]
  exact List.mem_map_of_mem
    (CStorageRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
      ctx.canonicalFreshKey_fresh).present

/-- No original output cell is the first newly allocated operand. -/
theorem output_ne_adjacent {shape : CShape} (output : CWriteRef ctx shape) :
    (liftWrite (N := N) output).key ≠ (adjacentRef ctx N).key := by
  change output.key ≠ ctx.canonicalFreshKey
  intro same
  apply ctx.canonicalFreshKey_fresh
  rw [← same]
  exact List.mem_map_of_mem output.toCStorageRef.present

/-- No original output cell is the second newly allocated operand. -/
theorem output_ne_modulus {shape : CShape} (output : CWriteRef ctx shape) :
    (liftWrite (N := N) output).key ≠ (modulusRef ctx N).key := by
  change output.key ≠ (adjacentContext ctx N).canonicalFreshKey
  intro same
  apply (adjacentContext ctx N).canonicalFreshKey_fresh
  rw [← same]
  exact List.mem_map_of_mem
    (output.toCStorageRef.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh).present

/-- The real store extension performed by the two outer lexical scopes. -/
def pushStore (N : Nat) (store : Store ctx) : Store (context ctx N) :=
  (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh).pushWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh

/-- The matching real releases remove only the two actual operand cells. -/
def popStore (N : Nat) (store : Store (context ctx N)) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh store)

/-- Entering both operand scopes preserves each exact original structural read. -/
theorem pushStore_read {shape : CShape} (input : CInputRef ctx shape) (store : Store ctx) :
    (pushStore N store).read (liftInput input) = store.read input := by
  let first := input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
      ctx.canonicalFreshKey_fresh)
    (adjacentContext ctx N).canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    (adjacentContext ctx N).canonicalFreshKey_fresh first).trans
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh input)

/-- Releasing both operand scopes preserves each exact surviving structural read. -/
theorem popStore_read {shape : CShape} (input : CInputRef ctx shape)
    (store : Store (context ctx N)) :
    (popStore N store).read input = store.read (liftInput input) := by
  let first := input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh store)
    input).trans
    (Store.read_popWorkspace_underWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      store first)

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
