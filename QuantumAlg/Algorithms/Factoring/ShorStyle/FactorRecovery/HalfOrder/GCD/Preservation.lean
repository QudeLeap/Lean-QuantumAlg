/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Layout.Laws
import all
  QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Correctness
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Preservation

/-!
# Surviving structural reads of the actual half-power GCD

The two fresh operand cells are distinct from every original structural read.
The real adjacent calculation, constant load and expanded Euclidean circuit
therefore change only the original result cell after those scopes close.
This supplies the unchanged half-power and constants to the selected right
factor computation, without rebuilding any original input.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem input_keys {shape : CShape} (input : CInputRef ctx shape) :
    (liftInput (N := N) input).storageKeys = input.storageKeys := by
  simp only [liftInput, CInputRef.storageKeys_underWorkspace]

private theorem input_separation {shape : CShape} (input : CInputRef ctx shape) :
    (adjacentRef ctx N).key ∉ (liftInput (N := N) input).storageKeys ∧
      (modulusRef ctx N).key ∉ (liftInput (N := N) input).storageKeys := by
  constructor
  · rw [input_keys]
    exact fun present => ctx.canonicalFreshKey_fresh
      (CInputRef.storageKeys_subset_context input present)
  · let first := input.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    have keys : (liftInput (N := N) input).storageKeys = first.storageKeys :=
      CInputRef.storageKeys_underWorkspace first (adjacentContext ctx N).canonicalFreshKey
        (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
    rw [keys]
    exact fun present => (adjacentContext ctx N).canonicalFreshKey_fresh
      (CInputRef.storageKeys_subset_context first present)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private theorem gcdTail_read_other
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    {shape : CShape} (other : CInputRef (context ctx N) shape)
    (separate : (liftWrite (N := N) output).key ∉ other.storageKeys)
    (store : Store (context ctx N)) :
    (gcdTailStep (model := model) output store).1.read other = store.read other :=
  (NumberTheory.GCD.gcdLexical_read_other (model := model) (operands ctx N) (liftWrite output)
    other separate (store.applyOp (clearOp output))).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (clearOp output) other separate)

/-- Every pre-existing structural read outside the GCD destination survives its actual body. -/
theorem body_read_other (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store (context ctx N)) :
    (bodyStep (model := model) successor halfPower output store).1.read (liftInput other) =
      store.read (liftInput other) := by
  have separated := input_separation (N := N) other
  have resultFree : (liftWrite (N := N) output).key ∉
      (liftInput (N := N) other).storageKeys := by
    rw [input_keys]
    exact separate
  let adjacent := NativeAdjacentWord.step (model := model) successor (liftInput halfPower)
    (adjacentRef ctx N) store
  let loaded := ConstantWord.foldStep (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) adjacent.1
  exact (gcdTail_read_other (model := model) output (liftInput other) resultFree loaded.1).trans
    ((ConstantWord.constantWord_fold_read_other (modulusRef ctx N)
      (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N))
      (liftInput other) separated.2 adjacent.1).trans
      (NativeAdjacentWord.read_other successor (liftInput halfPower) (adjacentRef ctx N)
        (liftInput other) separated.1 store))

/-- Releasing the two genuine operand cells leaves all other original reads unchanged. -/
theorem read_other (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (step (model := model) successor halfPower output store).1.read other = store.read other :=
  (popStore_read other (bodyStep (model := model) successor halfPower output (pushStore N
    store)).1).trans
    ((body_read_other (model := model) successor halfPower output other separate (pushStore N
      store)).trans
      (pushStore_read other store))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
