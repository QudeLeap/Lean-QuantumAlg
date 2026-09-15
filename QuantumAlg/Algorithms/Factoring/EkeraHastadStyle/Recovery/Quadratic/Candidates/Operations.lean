/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.Quadratic.Bounds
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Circuit
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Construction

/-!
# Actual native quadratic candidate instructions

The source center, square, truncated discriminant and square root are
computed in existing word cells. The discriminant cell is reused for its
square root, and the two source candidates are materialized afterwards.
Both subsequent divisor checks remain separate work; this candidate circuit
does not select or accept a factor. Every operation is existing native syntax,
with the real saturating-subtraction and square-root scopes as its subprograms.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual word cells used by the quadratic candidate calculation. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Widened source logarithm, incremented to the source quadratic center. -/
  center : CWriteRef ctx (.unsignedWord (RSA.quadraticWordWidth width))
  /-- Actual square, then truncated discriminant, then its exact square root. -/
  root : CWriteRef ctx (.unsignedWord (RSA.quadraticWordWidth width))
  /-- Materialized lower candidate, checked first by the original recovery rule. -/
  first : CWriteRef ctx (.unsignedWord (RSA.quadraticWordWidth width))
  /-- Materialized upper candidate, also checked even if the first one succeeds. -/
  second : CWriteRef ctx (.unsignedWord (RSA.quadraticWordWidth width))

/-- Actual resizing preserves the source logarithm before any candidate arithmetic. -/
def widenOp (input : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (RSA.quadraticWordWidth width)) ctx ctx :=
  .wordResize width (RSA.quadraticWordWidth width) ctx input refs.center

/-- The source center uses the actual increment instruction, with no stored constant oracle. -/
def centerOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord (RSA.quadraticWordWidth width))
      (.unsignedWord (RSA.quadraticWordWidth width)) ctx ctx :=
  .wordUnary .increment (RSA.quadraticWordWidth width) ctx
    (.storage refs.center.toCStorageRef) refs.center

/-- The complete square fits the actual word capacity established by the source bounds. -/
def squareOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord (RSA.quadraticWordWidth width))
      (.unsignedWord (RSA.quadraticWordWidth width)))
      (.unsignedWord (RSA.quadraticWordWidth width)) ctx ctx :=
  .wordBinary .mulLow (RSA.quadraticWordWidth width) ctx
    (.product (.storage refs.center.toCStorageRef) (.storage refs.center.toCStorageRef)) refs.root

/-- The actual discriminant uses source natural subtraction, including its underflow-to-zero arm. -/
def discriminant (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) : Circuit ctx ctx :=
  NativeSub.into (.storage refs.root.toCStorageRef) modulus refs.root

/-- The actual square-root component reuses the discriminant cell and owns its own scratch. -/
def squareRoot (refs : Refs ctx width) : Circuit ctx ctx :=
  NativeSqrt.into (.storage refs.root.toCStorageRef) refs.root

/-- The source lower candidate uses actual natural subtraction on the center and computed root. -/
def firstCandidate (refs : Refs ctx width) : Circuit ctx ctx :=
  NativeSub.into (.storage refs.center.toCStorageRef) (.storage refs.root.toCStorageRef) refs.first

/-- The source upper candidate is the actual native addition of the same two stored words. -/
def secondOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord (RSA.quadraticWordWidth width))
      (.unsignedWord (RSA.quadraticWordWidth width)))
      (.unsignedWord (RSA.quadraticWordWidth width)) ctx ctx :=
  .wordBinary .add (RSA.quadraticWordWidth width) ctx
    (.product (.storage refs.center.toCStorageRef) (.storage refs.root.toCStorageRef)) refs.second

/-- Actual chronological arithmetic materializes both original source candidate factors. -/
def candidates (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (widenOp input refs))
    (.seq (.classical (centerOp refs))
      (.seq (.classical (squareOp refs))
        (.seq (discriminant modulus refs)
          (.seq (squareRoot refs)
            (.seq (firstCandidate refs) (.classical (secondOp refs)))))))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
