/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics
import Mathlib.Data.List.Nodup

/-!
# The four actual first-success scan workspace cells

The decoded candidate, accepted latch, selected word and shared selector bit
are four genuine fresh heads. The original retained result is reused for each
optional recovery result and the final option pack. Every sampled tuple stays
in its original storage cell. The code retains every nested recovery scope;
these four cells account only for the outer scan's additional 2m+3 bits.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope

open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual decoded optional candidate has one bit and one modulus-width word. -/
@[implicit_reducible]
def candidateContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.product .bit (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh

/-- The persistent accepted latch is a real cell after the decoded candidate. -/
@[implicit_reducible]
def acceptedContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (candidateContext ctx N).addWorkspace (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh

/-- The actual selected word remains live throughout the whole finite scan. -/
@[implicit_reducible]
def selectedContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (acceptedContext ctx N).addWorkspace (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh

/-- The same real scratch bit serves both sequential selector scratch roles. -/
@[implicit_reducible]
def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (selectedContext ctx N).addWorkspace (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh

/-- The true first fresh cell, lifted through all three later allocations. -/
def candidateRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.product .bit (.unsignedWord (modulusBits N))) :=
  let first := CWriteRef.workspaceHead ctx ctx.canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) ctx.canonicalFreshKey_fresh
  let second := first.underWorkspace (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh
  let third := second.underWorkspace (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  third.underWorkspace (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh

/-- The accepted latch retains the identity of its real allocation. -/
def acceptedRef (ctx : RuntimeCtx kind) (N : Nat) : CWriteRef (context ctx N) .bit :=
  let first := CWriteRef.workspaceHead (candidateContext ctx N)
    (candidateContext ctx N).canonicalFreshKey .bit (candidateContext ctx N).canonicalFreshKey_fresh
  let second := first.underWorkspace (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  second.underWorkspace (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh

/-- The selected payload is exactly the third real fresh cell. -/
def selectedRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.unsignedWord (modulusBits N)) :=
  (CWriteRef.workspaceHead (acceptedContext ctx N) (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh).underWorkspace
    (selectedContext ctx N).canonicalFreshKey .bit (selectedContext ctx N).canonicalFreshKey_fresh

/-- The final physical head is the sole selector scratch bit. -/
def scratchRef (ctx : RuntimeCtx kind) (N : Nat) : CWriteRef (context ctx N) .bit :=
  CWriteRef.workspaceHead (selectedContext ctx N) (selectedContext ctx N).canonicalFreshKey
    .bit (selectedContext ctx N).canonicalFreshKey_fresh

/-- Original structural reads pass through precisely the four real workspace entries. -/
def liftInput {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (context ctx N) shape :=
  let first := input.underWorkspace ctx.canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) ctx.canonicalFreshKey_fresh
  let second := first.underWorkspace (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh
  let third := second.underWorkspace (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  third.underWorkspace (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh

/-- The surviving output keeps its original cell through all four allocations. -/
def liftWrite {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (context ctx N) shape :=
  let first := output.underWorkspace ctx.canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) ctx.canonicalFreshKey_fresh
  let second := first.underWorkspace (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh
  let third := second.underWorkspace (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  third.underWorkspace (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh

/-- Each original sampled input keeps its own physical parameter and phase references. -/
def liftInputs (inputs : Inputs ctx N) : Inputs (context ctx N) N where
  parameter := liftInput inputs.parameter
  phase := liftInput inputs.phase

/-- The selector consumes these exact four live cells. -/
def cells (ctx : RuntimeCtx kind) (N : Nat) : Cells (context ctx N) N where
  candidate := candidateRef ctx N
  accepted := acceptedRef ctx N
  selected := selectedRef ctx N
  scratch := scratchRef ctx N

/-- The real scan visits precisely the given original operands in order. -/
def body (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (context ctx N) (context ctx N) :=
  NativeFactorScan.code source (inputs.map liftInputs) (cells ctx N) (liftWrite result)

/-- Four genuine lexical entries enclose the whole scan and are then actually released. -/
def code (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.product .bit (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh
    (.workspace (candidateContext ctx N) (candidateContext ctx N).canonicalFreshKey .bit
      (candidateContext ctx N).canonicalFreshKey_fresh
      (.workspace (acceptedContext ctx N) (acceptedContext ctx N).canonicalFreshKey
        (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
        (.workspace (selectedContext ctx N) (selectedContext ctx N).canonicalFreshKey .bit
          (selectedContext ctx N).canonicalFreshKey_fresh (body source inputs result))))

/-- These four scopes preserve the original bank's exact physical wire list. -/
theorem quantumWires (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := rfl

/-- The actual fresh keys, in their final live-context order. -/
def scratchKeys (ctx : RuntimeCtx kind) (N : Nat) : List StorageKey :=
  [(scratchRef ctx N).key, (selectedRef ctx N).key,
    (acceptedRef ctx N).key, (candidateRef ctx N).key]

/-- No pre-existing entry was moved or replaced by the four genuine heads. -/
theorem context_keys (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).keys = scratchKeys ctx N ++ ctx.keys := rfl

/-- The actual context's certificate distinguishes all four scratch storage identities. -/
theorem scratchKeys_nodup (ctx : RuntimeCtx kind) (N : Nat) :
    (scratchKeys ctx N).Nodup := by
  have actual : (scratchKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  exact (List.nodup_append.mp actual).1

/-- Distinct real allocation positions are distinct write destinations. -/
theorem scratchKeys_ne (ctx : RuntimeCtx kind) (N : Nat) (first second : Fin 4)
    (different : first ≠ second) :
    (scratchKeys ctx N).get first ≠ (scratchKeys ctx N).get second :=
  fun same => different ((scratchKeys_nodup ctx N).injective_get same)

/-- Lifting preserves the exact original structural read support. -/
theorem liftInput_keys {shape : CShape} (input : CInputRef ctx shape) :
    (liftInput (N := N) input).storageKeys = input.storageKeys := by
  simp only [liftInput, CInputRef.storageKeys_underWorkspace]

/-- The real result write still designates its original physical cell. -/
theorem liftWrite_key {shape : CShape} (output : CWriteRef ctx shape) :
    (liftWrite (N := N) output).key = output.key := rfl

/-- All original structural operands avoid every actual selector workspace write. -/
theorem scratchKeys_input_separate {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (scratch : key ∈ scratchKeys ctx N) :
    key ∉ (liftInput (N := N) input).storageKeys := by
  have actual : (scratchKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  rw [liftInput_keys]
  intro present
  exact actual.disjoint scratch (CInputRef.storageKeys_subset_context input present)

/-- The physical cells satisfy the existing selector's entire internal separation contract. -/
theorem selector_separated (ctx : RuntimeCtx kind) (N : Nat) :
    FirstAccepted.Separated (selectorInputs (cells ctx N)) (selectorRefs (cells ctx N)) := by
  have scratchCandidate := scratchKeys_ne ctx N 0 3 (by decide)
  have scratchAccepted := scratchKeys_ne ctx N 0 2 (by decide)
  have scratchSelected := scratchKeys_ne ctx N 0 1 (by decide)
  have acceptedSelected := scratchKeys_ne ctx N 2 1 (by decide)
  refine ⟨?_, ?_, ?_, scratchAccepted, scratchAccepted,
    scratchSelected, scratchSelected, acceptedSelected⟩
  all_goals exact fun member => scratchCandidate (List.mem_singleton.mp member)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope
