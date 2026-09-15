/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual caller storage for the variable-width natural remainder check

The zero word remains a caller-supplied input. Only the division pair and
acceptance bit are written, with arbitrary incoming values in those cells.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck

open Execution

/-- Read a writable cell through its actual structural storage reference. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Original caller-owned references for a variable-width remainder-zero check. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (numeratorWidth divisorWidth : Nat) where
  /-- Dividend word supplied by the caller. -/
  numerator : CInputRef ctx (.unsignedWord numeratorWidth)
  /-- Nonzero divisor word supplied by the caller. -/
  divisor : CInputRef ctx (.unsignedWord divisorWidth)
  /-- Workspace holding quotient and remainder from the division operation. -/
  division : CWriteRef ctx
    (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))
  divisionRole : division.toCStorageRef.role = .workspace
  /-- Caller-owned zero word used for the remainder comparison. -/
  zero : CInputRef ctx (.unsignedWord divisorWidth)
  /-- Workspace bit recording that the remainder is zero. -/
  accepted : CWriteRef ctx .bit
  acceptedRole : accepted.toCStorageRef.role = .workspace

/-- The remainder projection stored by the actual division instruction. -/
def remainderInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {numeratorWidth divisorWidth : Nat} (refs : Refs ctx numeratorWidth divisorWidth) :
    CInputRef ctx (.unsignedWord divisorWidth) :=
  .second (writeInput refs.division)

/-- Original separation footprint across division and the subsequent equality comparison. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {numeratorWidth divisorWidth : Nat} (refs : Refs ctx numeratorWidth divisorWidth) : Prop where
  numeratorAvoidsDivision : refs.division.key ∉ refs.numerator.storageKeys
  divisorAvoidsDivision : refs.division.key ∉ refs.divisor.storageKeys
  zeroAvoidsDivision : refs.division.key ∉ refs.zero.storageKeys
  divisionAvoidsAccepted : refs.accepted.key ∉ (writeInput refs.division).storageKeys
  zeroAvoidsAccepted : refs.accepted.key ∉ refs.zero.storageKeys

/-- The original nonzero divisor and supplied-zero numerical domain on the incoming store. -/
def InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {numeratorWidth divisorWidth : Nat} (before : Store ctx)
    (refs : Refs ctx numeratorWidth divisorWidth) : Prop :=
  0 < (before.read refs.divisor).toNat ∧ (before.read refs.zero).toNat = 0

/-- Complete structural caller reads outside the actual division and acceptance writes. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {numeratorWidth divisorWidth : Nat} (refs : Refs ctx numeratorWidth divisorWidth)
    (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.division.key ∉ other.storageKeys → refs.accepted.key ∉ other.storageKeys →
      after.read other = before.read other

/-- Exact natural remainder, divisibility flag and full structural caller frame. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {numeratorWidth divisorWidth : Nat} (refs : Refs ctx numeratorWidth divisorWidth)
    (before after : Store ctx) : Prop where
  remainder : (after.read (remainderInput refs)).toNat =
    (before.read refs.numerator).toNat % (before.read refs.divisor).toNat
  accepted : (after.read (writeInput refs.accepted)).toBool =
    decide ((before.read refs.numerator).toNat % (before.read refs.divisor).toNat = 0)
  callerFrame : CallerFrame refs before after

end QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck
