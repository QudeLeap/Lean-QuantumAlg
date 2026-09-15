/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.Read

/-!
# Caller-owned signed-division cells

The six writable cells and their original separation contract specify real
storage. No execution or resource projection is attached to these references.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

/-- Caller-provided inputs and mutable cells for one rounded signed division. -/
structure BodyRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Raw two's-complement numerator. -/
  numerator : CInputRef ctx (.unsignedWord width)
  /-- Strictly positive unsigned denominator. -/
  denominator : CInputRef ctx (.unsignedWord width)
  /-- Raw two's-complement rounded quotient. -/
  output : CWriteRef ctx (.unsignedWord width)
  /-- Width-`width` unsigned magnitude scratch. -/
  magnitude : CWriteRef ctx (.unsignedWord width)
  /-- Stored sign bit of the raw numerator. -/
  negative : CWriteRef ctx .bit
  /-- Wide numerator used for the doubled and corrected dividend. -/
  wideNumerator : CWriteRef ctx (.unsignedWord (width + 1))
  /-- Wide denominator used for the doubled divisor. -/
  wideDenominator : CWriteRef ctx (.unsignedWord (width + 1))
  /-- Quotient and remainder product written by the real division instruction. -/
  division : CWriteRef ctx
    (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
  magnitudeRole : magnitude.toCStorageRef.role = .workspace
  negativeRole : negative.toCStorageRef.role = .workspace
  wideNumeratorRole : wideNumerator.toCStorageRef.role = .workspace
  wideDenominatorRole : wideDenominator.toCStorageRef.role = .workspace
  divisionRole : division.toCStorageRef.role = .workspace
  outputWritable : output.toCStorageRef.role = .workspace ∨
    output.toCStorageRef.role = .retained

/-- All mutable storage keys touched by the caller-owned rounded-division body. -/
def mutableKeys {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : BodyRefs ctx width) : List StorageKey :=
  [refs.magnitude.toCStorageRef.key,
    refs.negative.toCStorageRef.key,
    refs.wideNumerator.toCStorageRef.key,
    refs.wideDenominator.toCStorageRef.key,
    refs.division.toCStorageRef.key,
    refs.output.toCStorageRef.key]

/-- The caller separates both inputs from every mutable cell and every pair of
mutable cells.  Named fields keep machine proofs independent of list order. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : BodyRefs ctx width) : Prop where
  numeratorAvoidsMagnitude :
    refs.magnitude.toCStorageRef.key ∉ refs.numerator.storageKeys
  numeratorAvoidsNegative :
    refs.negative.toCStorageRef.key ∉ refs.numerator.storageKeys
  numeratorAvoidsWideNumerator :
    refs.wideNumerator.toCStorageRef.key ∉ refs.numerator.storageKeys
  numeratorAvoidsWideDenominator :
    refs.wideDenominator.toCStorageRef.key ∉ refs.numerator.storageKeys
  numeratorAvoidsDivision :
    refs.division.toCStorageRef.key ∉ refs.numerator.storageKeys
  numeratorAvoidsOutput :
    refs.output.toCStorageRef.key ∉ refs.numerator.storageKeys
  denominatorAvoidsMagnitude :
    refs.magnitude.toCStorageRef.key ∉ refs.denominator.storageKeys
  denominatorAvoidsNegative :
    refs.negative.toCStorageRef.key ∉ refs.denominator.storageKeys
  denominatorAvoidsWideNumerator :
    refs.wideNumerator.toCStorageRef.key ∉ refs.denominator.storageKeys
  denominatorAvoidsWideDenominator :
    refs.wideDenominator.toCStorageRef.key ∉ refs.denominator.storageKeys
  denominatorAvoidsDivision :
    refs.division.toCStorageRef.key ∉ refs.denominator.storageKeys
  denominatorAvoidsOutput :
    refs.output.toCStorageRef.key ∉ refs.denominator.storageKeys
  magnitudeNeNegative :
    refs.magnitude.toCStorageRef.key ≠ refs.negative.toCStorageRef.key
  magnitudeNeWideNumerator :
    refs.magnitude.toCStorageRef.key ≠ refs.wideNumerator.toCStorageRef.key
  magnitudeNeWideDenominator :
    refs.magnitude.toCStorageRef.key ≠ refs.wideDenominator.toCStorageRef.key
  magnitudeNeDivision :
    refs.magnitude.toCStorageRef.key ≠ refs.division.toCStorageRef.key
  magnitudeNeOutput :
    refs.magnitude.toCStorageRef.key ≠ refs.output.toCStorageRef.key
  negativeNeWideNumerator :
    refs.negative.toCStorageRef.key ≠ refs.wideNumerator.toCStorageRef.key
  negativeNeWideDenominator :
    refs.negative.toCStorageRef.key ≠ refs.wideDenominator.toCStorageRef.key
  negativeNeDivision :
    refs.negative.toCStorageRef.key ≠ refs.division.toCStorageRef.key
  negativeNeOutput :
    refs.negative.toCStorageRef.key ≠ refs.output.toCStorageRef.key
  wideNumeratorNeWideDenominator :
    refs.wideNumerator.toCStorageRef.key ≠ refs.wideDenominator.toCStorageRef.key
  wideNumeratorNeDivision :
    refs.wideNumerator.toCStorageRef.key ≠ refs.division.toCStorageRef.key
  wideNumeratorNeOutput :
    refs.wideNumerator.toCStorageRef.key ≠ refs.output.toCStorageRef.key
  wideDenominatorNeDivision :
    refs.wideDenominator.toCStorageRef.key ≠ refs.division.toCStorageRef.key
  wideDenominatorNeOutput :
    refs.wideDenominator.toCStorageRef.key ≠ refs.output.toCStorageRef.key
  divisionNeOutput :
    refs.division.toCStorageRef.key ≠ refs.output.toCStorageRef.key

/-- Frame relation for every caller read avoiding all cells mutable by the body. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : BodyRefs ctx width)
    (before after : Execution.Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ key ∈ mutableKeys refs, key ∉ other.storageKeys) → after.read other = before.read other

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
