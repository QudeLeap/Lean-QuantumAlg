/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.Read

/-!
# Original integer-square-root round cells and numerical contract
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt

open Execution

noncomputable section

/-- The six cells updated by one binary-refinement round. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Current lower square-root estimate. -/
  root : CWriteRef ctx (.unsignedWord width)
  rootRole : root.toCStorageRef.role = .workspace
  /-- Current half-step increment. -/
  half : CWriteRef ctx (.unsignedWord width)
  halfRole : half.toCStorageRef.role = .workspace
  /-- Candidate midpoint together with its carry bit. -/
  midCarry : CWriteRef ctx (.product (.unsignedWord width) .bit)
  midCarryRole : midCarry.toCStorageRef.role = .workspace
  /-- Squared candidate midpoint. -/
  square : CWriteRef ctx (.unsignedWord (width + width))
  squareRole : square.toCStorageRef.role = .workspace
  /-- Comparison flag indicating that the candidate square is too large. -/
  tooLarge : CWriteRef ctx .bit
  tooLargeRole : tooLarge.toCStorageRef.role = .workspace
  /-- Branch flag selecting whether to retain the candidate midpoint. -/
  take : CWriteRef ctx .bit
  takeRole : take.toCStorageRef.role = .workspace

/-- Named writable cells of one binary-refinement round. -/
inductive Cell | root | half | midCarry | square | tooLarge | take

/-- Storage key of the writable cell selected by its round-local name. -/
def writeKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Cell → StorageKey
  | .root => refs.root.toCStorageRef.key | .half => refs.half.toCStorageRef.key
  | .midCarry => refs.midCarry.toCStorageRef.key | .square => refs.square.toCStorageRef.key
  | .tooLarge => refs.tooLarge.toCStorageRef.key | .take => refs.take.toCStorageRef.key

/-- Input/cell separation and pairwise distinctness required by one round. -/
def Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width) : Prop :=
  (∀ cell, writeKey refs cell ∉ input.storageKeys) ∧ Function.Injective (writeKey refs)

/-- Read view of a writable reference for subsequent round operations. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- The original numerical capacity and bracketing assumptions of a refinement round. -/
def RoundArithmetic (width low half input : Nat) : Prop :=
  low + half < CShape.wordModulus width ∧ low * low ≤ input ∧
    input < (low + half + half) * (low + half + half)

/-- The original mathematical candidate obeys the next lower and upper bounds. -/
lemma roundArithmetic_bounds {width low half input : Nat}
    (initial : RoundArithmetic width low half input) :
    let next := if (low + half) * (low + half) ≤ input then low + half else low
    next * next ≤ input ∧ input < (next + half) * (next + half) := by
  dsimp only
  split_ifs with selected
  · exact ⟨selected, initial.2.2⟩
  · exact ⟨initial.2.1, Nat.lt_of_not_ge selected⟩

/-- The original capacity and search interval read from the actual incoming cells. -/
def RoundInitial {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width)
    (before : Store ctx) : Prop :=
  RoundArithmetic width (before.read (writeInput refs.root)).toNat
    (before.read (writeInput refs.half)).toNat (before.read input).toNat

/-- The exact sum of the original root estimate and half-step increment. -/
def midpoint {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (before : Store ctx) : Nat :=
  (before.read (writeInput refs.root)).toNat + (before.read (writeInput refs.half)).toNat

/-- The independent mathematical binary choice from the original actual input. -/
def selectedRoot {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width)
    (before : Store ctx) : Nat :=
  if midpoint refs before * midpoint refs before ≤ (before.read input).toNat then
    midpoint refs before
  else
    (before.read (writeInput refs.root)).toNat

/-- Every actual read outside the original six write identities survives the round. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ cell, writeKey refs cell ∉ other.storageKeys) → after.read other = before.read other

/-- The exact binary choice, right shift, original search bounds and complete caller frame. -/
structure RoundOutcome {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width)
    (before after : Store ctx) : Prop where
  root : (after.read (writeInput refs.root)).toNat = selectedRoot input refs before
  half : (after.read (writeInput refs.half)).toNat =
    (before.read (writeInput refs.half)).toNat / 2
  lower : (after.read (writeInput refs.root)).toNat *
    (after.read (writeInput refs.root)).toNat ≤ (before.read input).toNat
  upper : (before.read input).toNat <
    ((after.read (writeInput refs.root)).toNat + (before.read (writeInput refs.half)).toNat) *
      ((after.read (writeInput refs.root)).toNat + (before.read (writeInput refs.half)).toNat)
  callerFrame : CallerFrame refs before after

end

end QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt
