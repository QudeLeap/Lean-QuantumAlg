/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Layout
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Layout

/-!
# Actual quadratic-prefix cells and original numerical contract
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

/-- Read the actual typed cell used by a subsequent native operation. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Local center width helper for the factoring construction. -/
def centerWidth (shortWidth : Nat) : Nat := shortWidth + 1
/-- Local discriminant width helper for the factoring construction. -/
def discriminantWidth (shortWidth : Nat) : Nat := centerWidth shortWidth + centerWidth shortWidth

/-- Typed record for the local refs data. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- Input reference for the short log value. -/
  shortLog : CInputRef ctx (.unsignedWord shortWidth)
  /-- Input reference for the modulus value. -/
  modulus : CInputRef ctx (.unsignedWord (discriminantWidth shortWidth))
  /-- Writable cell for the center value. -/
  center : CWriteRef ctx (.unsignedWord (centerWidth shortWidth))
  centerRole : center.toCStorageRef.role = .workspace
  /-- Writable cell for the center square value. -/
  centerSquare : CWriteRef ctx (.unsignedWord (discriminantWidth shortWidth))
  centerSquareRole : centerSquare.toCStorageRef.role = .workspace
  /-- Nested references for the subtract stage. -/
  subtract : NatSub.Refs ctx (discriminantWidth shortWidth)
  subtractLeft : subtract.left = writeInput centerSquare
  subtractRight : subtract.right = modulus
  /-- Nested references for the sqrt stage. -/
  sqrt : NatSqrt.Refs ctx (discriminantWidth shortWidth)
  sqrtInput : sqrt.input = writeInput subtract.output

/-- Avoidance of every cell written before the square-root routine. -/
structure PrefixFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  center : refs.center.toCStorageRef.key ∉ other.storageKeys
  centerSquare : refs.centerSquare.toCStorageRef.key ∉ other.storageKeys
  subtractLessThan : refs.subtract.lessThan.toCStorageRef.key ∉ other.storageKeys
  subtractOutput : refs.subtract.output.toCStorageRef.key ∉ other.storageKeys

/-- Avoidance of every cell written by the square-root routine. -/
structure SqrtFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  wideInput : refs.sqrt.wideInput.toCStorageRef.key ∉ other.storageKeys
  round : ∀ cell, (IntegerSqrt.writeKey refs.sqrt.round cell) ∉ other.storageKeys
  output : refs.sqrt.output.toCStorageRef.key ∉ other.storageKeys

/-- Typed record for the local separation data. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) : Prop where
  shortLogAvoidsCenter : refs.center.toCStorageRef.key ∉ refs.shortLog.storageKeys
  modulusAvoidsCenter : refs.center.toCStorageRef.key ∉ refs.modulus.storageKeys
  modulusAvoidsSquare : refs.centerSquare.toCStorageRef.key ∉ refs.modulus.storageKeys
  centerAvoidsSquare :
    refs.centerSquare.toCStorageRef.key ∉ (writeInput refs.center).storageKeys
  centerAvoidsSubtractLessThan :
    refs.subtract.lessThan.toCStorageRef.key ∉ (writeInput refs.center).storageKeys
  centerAvoidsSubtractOutput :
    refs.subtract.output.toCStorageRef.key ∉ (writeInput refs.center).storageKeys
  squareAvoidsSubtractOutput :
    refs.subtract.output.toCStorageRef.key ∉ (writeInput refs.centerSquare).storageKeys
  subtract : NatSub.Separation refs.subtract
  sqrt : NatSqrt.Separation refs.sqrt
  sqrtWideInputAvoidsPrefix : PrefixFrameAvoids refs (NatSqrt.wideInput refs.sqrt)
  sqrtRootAvoidsPrefix : PrefixFrameAvoids refs (writeInput refs.sqrt.round.root)
  sqrtHalfAvoidsPrefix : PrefixFrameAvoids refs (writeInput refs.sqrt.round.half)
  sqrtOutputAvoidsPrefix : PrefixFrameAvoids refs (writeInput refs.sqrt.output)
  centerAvoidsSqrt : SqrtFrameAvoids refs (writeInput refs.center)
  squareAvoidsSqrt : SqrtFrameAvoids refs (writeInput refs.centerSquare)
  discriminantAvoidsSqrt :
    SqrtFrameAvoids refs (writeInput refs.subtract.output)

/-- The full discriminant has at least two bits, so the square-root driver width is positive. -/
theorem discriminantWidth_two_le (shortWidth : Nat) : 2 ≤ discriminantWidth shortWidth := by
  unfold discriminantWidth centerWidth
  omega

/-- The original short-word width already guarantees space for its incremented center. -/
theorem center_capacity {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (store : Store ctx) :
    (store.read refs.shortLog).toNat + 1 < CShape.wordModulus (centerWidth shortWidth) := by
  have sourceFits := (store.read refs.shortLog).toNat_lt
  have positive := Nat.two_pow_pos shortWidth
  change (store.read refs.shortLog).toNat + 1 < 2 ^ (shortWidth + 1)
  rw [pow_succ]
  change (store.read refs.shortLog).toNat < 2 ^ shortWidth at sourceFits
  omega

/-- Exact original center, full square and natural truncated discriminant before square root. -/
structure DiscriminantOutcome {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  center : (after.read (writeInput refs.center)).toNat = (before.read refs.shortLog).toNat + 1
  square : (after.read (writeInput refs.centerSquare)).toNat =
    ((before.read refs.shortLog).toNat + 1) ^ 2
  discriminant : (after.read (writeInput refs.subtract.output)).toNat =
    ((before.read refs.shortLog).toNat + 1) ^ 2 - (before.read refs.modulus).toNat
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    PrefixFrameAvoids refs other → after.read other = before.read other

/-- Original center, square, truncated discriminant, exact square root and full caller frame. -/
structure Outcome {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  center : (after.read (writeInput refs.center)).toNat = (before.read refs.shortLog).toNat + 1
  square : (after.read (writeInput refs.centerSquare)).toNat =
    ((before.read refs.shortLog).toNat + 1) ^ 2
  discriminant : (after.read (writeInput refs.subtract.output)).toNat =
    ((before.read refs.shortLog).toNat + 1) ^ 2 - (before.read refs.modulus).toNat
  root : (after.read (writeInput refs.sqrt.output)).toNat =
    Nat.sqrt (((before.read refs.shortLog).toNat + 1) ^ 2 - (before.read refs.modulus).toNat)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    PrefixFrameAvoids refs other → SqrtFrameAvoids refs other →
      after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix
