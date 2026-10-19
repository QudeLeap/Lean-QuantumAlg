/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Encoding
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual lexical cells of the Euclidean state

Each internal key is generated from the preceding real context. The current
word, previous word and active bit occupy three distinct lexical cells. All
older references are lifted structurally; they do not acquire new values or
compute an encoded result. The quotient/remainder pair is allocated later,
only by a selected active iteration.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

variable {kind : ProblemKind}

/-- Add the current-divisor cell using the next actual fresh storage identity. -/
def currentCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh

/-- Add the previous-divisor cell after the current-divisor cell. -/
def previousCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (currentCtx ctx width).addWorkspace (currentCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh

/-- Add the real branch bit after both Euclidean words. -/
def loopCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (previousCtx ctx width).addWorkspace (previousCtx ctx width).canonicalFreshKey
    .bit (previousCtx ctx width).canonicalFreshKey_fresh

/-- The current-divisor reference beneath the two later lexical cells. -/
def currentCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (loopCtx ctx width) (.unsignedWord width) :=
  ((CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (previousCtx ctx width).canonicalFreshKey .bit
        (previousCtx ctx width).canonicalFreshKey_fresh

/-- The previous-divisor reference beneath the later branch bit. -/
def previousCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (loopCtx ctx width) (.unsignedWord width) :=
  (CWriteRef.workspaceHead (currentCtx ctx width) (currentCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh).underWorkspace
      (previousCtx ctx width).canonicalFreshKey .bit
      (previousCtx ctx width).canonicalFreshKey_fresh

/-- The head cell holding the actual next-iteration condition. -/
def conditionCell (ctx : RuntimeCtx kind) (width : Nat) : CWriteRef (loopCtx ctx width) .bit :=
  CWriteRef.workspaceHead (previousCtx ctx width) (previousCtx ctx width).canonicalFreshKey
    .bit (previousCtx ctx width).canonicalFreshKey_fresh

/-- Lift an existing operand beneath precisely the three lexical state cells. -/
def underLoop {ctx : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) : CInputRef (loopCtx ctx width) shape :=
  ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (previousCtx ctx width).canonicalFreshKey .bit
        (previousCtx ctx width).canonicalFreshKey_fresh

/-- Lift an existing writable result beneath those same three cells. -/
def writeUnderLoop {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) : CWriteRef (loopCtx ctx width) shape :=
  ((output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (previousCtx ctx width).canonicalFreshKey .bit
        (previousCtx ctx width).canonicalFreshKey_fresh

/-- The three live state cells have their actual generated identities. -/
lemma gcdState_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (loopCtx ctx width).keys =
      [(conditionCell ctx width).key, (previousCell ctx width).key,
        (currentCell ctx width).key] ++ ctx.keys := rfl

/-- Global context uniqueness proves internal separation without a caller hypothesis. -/
lemma gcdState_keys_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    [(conditionCell ctx width).key, (previousCell ctx width).key,
      (currentCell ctx width).key].Nodup := by
  have unique := (loopCtx ctx width).keysNodup
  change (loopCtx ctx width).keys.Nodup at unique
  rw [gcdState_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- Actual old storage identities are distinct from all three new cells. -/
lemma gcdState_keys_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint
      [(conditionCell ctx width).key, (previousCell ctx width).key,
        (currentCell ctx width).key] ctx.keys := by
  have unique := (loopCtx ctx width).keysNodup
  change (loopCtx ctx width).keys.Nodup at unique
  rw [gcdState_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- Lexical classical state does not allocate or discard any physical quantum wire. -/
lemma gcdState_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (loopCtx ctx width).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
