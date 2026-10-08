/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Result
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Actual retained first-success storage before the quantum bank

Five real retention instructions allocate the optional result, decoded candidate,
accepted latch, selected word and shared selector scratch. The closed XOR clears
only the actual accepted bit. No initial latch or selected-value premise is used.
All five cells remain live across growing retained source outcomes; each complete
recovery visit keeps its existing nested lexical workspaces.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Persistent

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind}

/-- The real retained result head follows precisely the preceding allocations. -/
@[implicit_reducible]
def resultContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  ctx.addRetained ctx.canonicalFreshKey (.option (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh

/-- The real retained candidate head follows precisely the preceding allocations. -/
@[implicit_reducible]
def candidateContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (resultContext ctx N).addRetained (resultContext ctx N).canonicalFreshKey (.product .bit
    (.unsignedWord (modulusBits N))) (resultContext ctx N).canonicalFreshKey_fresh

/-- The real retained accepted head follows precisely the preceding allocations. -/
@[implicit_reducible]
def acceptedContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (candidateContext ctx N).addRetained (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh

/-- The real retained selected head follows precisely the preceding allocations. -/
@[implicit_reducible]
def selectedContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (acceptedContext ctx N).addRetained (acceptedContext ctx N).canonicalFreshKey (.unsignedWord
    (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh

/-- The real retained scratch head follows precisely the preceding allocations. -/
@[implicit_reducible]
def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (selectedContext ctx N).addRetained (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh

/-- The result reference keeps its actual allocation identity beneath later heads. -/
def resultRef (ctx : RuntimeCtx kind) (N : Nat) : CWriteRef (context ctx N) (.option (.unsignedWord
  (modulusBits N))) :=
  let cell0 := CWriteRef.retainedHead ctx ctx.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) ctx.canonicalFreshKey_fresh
  let cell1 := cell0.underRetained (resultContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) (resultContext ctx N).canonicalFreshKey_fresh
  let cell2 := cell1.underRetained (candidateContext ctx N).canonicalFreshKey
    .bit (candidateContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underRetained (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underRetained (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh
  cell4

/-- The candidate reference keeps its actual allocation identity beneath later heads. -/
def candidateRef (ctx : RuntimeCtx kind) (N : Nat) : CWriteRef (context ctx N) (.product .bit
  (.unsignedWord (modulusBits N))) :=
  let cell1 := CWriteRef.retainedHead (resultContext ctx N) (resultContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) (resultContext ctx N).canonicalFreshKey_fresh
  let cell2 := cell1.underRetained (candidateContext ctx N).canonicalFreshKey
    .bit (candidateContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underRetained (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underRetained (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh
  cell4

/-- The accepted reference keeps its actual allocation identity beneath later heads. -/
def acceptedRef (ctx : RuntimeCtx kind) (N : Nat) : CWriteRef (context ctx N) .bit :=
  let cell2 := CWriteRef.retainedHead (candidateContext ctx N) (candidateContext ctx
    N).canonicalFreshKey
    .bit (candidateContext ctx N).canonicalFreshKey_fresh
  let cell3 := cell2.underRetained (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underRetained (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh
  cell4

/-- The selected reference keeps its actual allocation identity beneath later heads. -/
def selectedRef (ctx : RuntimeCtx kind) (N : Nat) : CWriteRef (context ctx N) (.unsignedWord
  (modulusBits N)) :=
  let cell3 := CWriteRef.retainedHead (acceptedContext ctx N) (acceptedContext ctx
    N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  let cell4 := cell3.underRetained (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh
  cell4

/-- The scratch reference keeps its actual allocation identity beneath later heads. -/
def scratchRef (ctx : RuntimeCtx kind) (N : Nat) : CWriteRef (context ctx N) .bit :=
  let cell4 := CWriteRef.retainedHead (selectedContext ctx N) (selectedContext ctx
    N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh
  cell4

/-- Every selector operand is one of the producer's real retained cells. -/
def cells (ctx : RuntimeCtx kind) (N : Nat) : NativeFactorScan.Cells (context ctx N) N where
  candidate := candidateRef ctx N
  accepted := acceptedRef ctx N
  selected := selectedRef ctx N
  scratch := scratchRef ctx N

/-- The allocation does not create, remove or replace any quantum wire. -/
theorem quantumWires (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := rfl

/-- The true heads in their final live-manifest order. -/
def retainedKeys (ctx : RuntimeCtx kind) (N : Nat) : List StorageKey :=
  [(scratchRef ctx N).key, (selectedRef ctx N).key, (acceptedRef ctx N).key,
    (candidateRef ctx N).key, (resultRef ctx N).key]

/-- Every original live key survives the five actual allocations. -/
theorem context_keys (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).keys = retainedKeys ctx N ++ ctx.keys := rfl

/-- Actual context uniqueness distinguishes every fresh write destination. -/
theorem retainedKeys_nodup (ctx : RuntimeCtx kind) (N : Nat) :
    (retainedKeys ctx N).Nodup := by
  have actual : (retainedKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  exact (List.nodup_append.mp actual).1

/-- Different real allocation positions have different keys. -/
theorem retainedKeys_ne (ctx : RuntimeCtx kind) (N : Nat) (first second : Fin 5)
    (different : first ≠ second) :
    (retainedKeys ctx N).get first ≠ (retainedKeys ctx N).get second :=
  fun same => different ((retainedKeys_nodup ctx N).injective_get same)

/-- All selection conditions follow from the real allocation geometry. -/
theorem separated (ctx : RuntimeCtx kind) (N : Nat) :
    NativeFactorScan.Separated (cells ctx N) (resultRef ctx N) := by
  have scratchCandidate := retainedKeys_ne ctx N 0 3 (by decide)
  have scratchAccepted := retainedKeys_ne ctx N 0 2 (by decide)
  have scratchSelected := retainedKeys_ne ctx N 0 1 (by decide)
  have acceptedSelected := retainedKeys_ne ctx N 2 1 (by decide)
  have selector : FirstAccepted.Separated (NativeFactorScan.selectorInputs (cells ctx N))
      (NativeFactorScan.selectorRefs (cells ctx N)) := by
    refine ⟨?_, ?_, ?_, scratchAccepted, scratchAccepted,
      scratchSelected, scratchSelected, acceptedSelected⟩
    all_goals exact fun member => scratchCandidate (List.mem_singleton.mp member)
  exact ⟨selector, retainedKeys_ne ctx N 3 2 (by decide),
    retainedKeys_ne ctx N 3 1 (by decide), retainedKeys_ne ctx N 4 2 (by decide),
    retainedKeys_ne ctx N 4 1 (by decide)⟩

section Selected

variable {model : ExecutionModel} [BitWord.Selected model]

/-- Five genuine retention instructions establish the real persistent cells. -/
def allocation (ctx : RuntimeCtx model.kind) (N : Nat) : Circuit model ctx (context ctx N) :=
  (.seq (.retain ctx ctx.canonicalFreshKey (.option (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh)
    (.seq (.retain (resultContext ctx N) (resultContext ctx N).canonicalFreshKey (.product .bit
      (.unsignedWord (modulusBits N))) (resultContext ctx N).canonicalFreshKey_fresh)
    (.seq (.retain (candidateContext ctx N) (candidateContext ctx N).canonicalFreshKey .bit
      (candidateContext ctx N).canonicalFreshKey_fresh)
    (.seq (.retain (acceptedContext ctx N) (acceptedContext ctx N).canonicalFreshKey (.unsignedWord
      (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh)
    (.retain (selectedContext ctx N) (selectedContext ctx N).canonicalFreshKey .bit (selectedContext
      ctx N).canonicalFreshKey_fresh)))))

/-- Allocation and the real closed Boolean instruction clear the success tag once. -/
def initialization (ctx : RuntimeCtx model.kind) (N : Nat) : Circuit model ctx (context ctx N) :=
  (allocation (model := model) ctx N).seq
    (BitWord.instruction (execution := model) (NativeFactorScan.clearAcceptedOp (cells ctx N)))

end Selected

/-- The genuine clear operation makes the latch absent for every incoming store. -/
theorem cleared_latch (ctx : RuntimeCtx kind) (N : Nat) (store : Store (context ctx N)) :
    NativeFactorScan.latchValue (cells ctx N)
      (store.applyOp (NativeFactorScan.clearAcceptedOp (cells ctx N))) = .optionNone :=
  NativeFactorScan.clear_latchValue (cells ctx N) store

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Persistent
