/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Layout

/-!
# Actual cells of the finite natural-square-root driver

The initialization writes all required starting values. No incoming workspace
or output value is assumed to be zero.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open IntegerSqrt (writeInput)

/-- The driver retains the input width as its exact refinement work width. -/
def workWidth (inputWidth : Nat) : Nat := inputWidth

/-- Actual input, refinement workspaces and caller-visible square-root output. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (inputWidth : Nat) where
  /-- Input word whose natural square root is computed. -/
  input : CInputRef ctx (.unsignedWord inputWidth)
  /-- Workspace containing the widened input for binary refinement. -/
  wideInput : CWriteRef ctx (.unsignedWord (workWidth inputWidth + workWidth inputWidth))
  wideInputRole : wideInput.toCStorageRef.role = .workspace
  /-- Workspace bundle used by the binary-refinement round. -/
  round : IntegerSqrt.Refs ctx (workWidth inputWidth)
  /-- Caller-visible square-root output word. -/
  output : CWriteRef ctx (.unsignedWord (workWidth inputWidth))
  outputRole : output.toCStorageRef.role = .workspace ∨
    output.toCStorageRef.role = .retained

/-- The widened input read consumed by subsequent binary-refinement rounds. -/
def wideInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}
    (refs : Refs ctx inputWidth) :
    CInputRef ctx (.unsignedWord (workWidth inputWidth + workWidth inputWidth)) :=
  writeInput refs.wideInput

/-- The small separation footprint needed by the initialization prefix. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}
    (refs : Refs ctx inputWidth) : Prop where
  inputAvoidsWideInput : refs.wideInput.toCStorageRef.key ∉ refs.input.storageKeys
  inputAvoidsRoot : refs.round.root.toCStorageRef.key ∉ refs.input.storageKeys
  inputAvoidsHalf : refs.round.half.toCStorageRef.key ∉ refs.input.storageKeys
  wideInputAvoidsRoot : refs.round.root.toCStorageRef.key ∉ (wideInput refs).storageKeys
  wideInputAvoidsHalf : refs.round.half.toCStorageRef.key ∉ (wideInput refs).storageKeys
  rootAvoidsHalf : refs.round.half.toCStorageRef.key ∉ (writeInput refs.round.root).storageKeys
  halfAvoidsRoot : refs.round.root.toCStorageRef.key ∉ (writeInput refs.round.half).storageKeys
  outputAvoidsWideInput : refs.wideInput.toCStorageRef.key ∉ (writeInput refs.output).storageKeys
  outputAvoidsRoot : refs.round.root.toCStorageRef.key ∉ (writeInput refs.output).storageKeys
  outputAvoidsHalf : refs.round.half.toCStorageRef.key ∉ (writeInput refs.output).storageKeys
  round : IntegerSqrt.Separation (wideInput refs) refs.round

/-- All caller reads outside the three initialization writes are preserved. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}
    (refs : Refs ctx inputWidth) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.wideInput.toCStorageRef.key ∉ other.storageKeys →
      refs.round.root.toCStorageRef.key ∉ other.storageKeys →
        refs.round.half.toCStorageRef.key ∉ other.storageKeys → after.read other = before.read other

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
