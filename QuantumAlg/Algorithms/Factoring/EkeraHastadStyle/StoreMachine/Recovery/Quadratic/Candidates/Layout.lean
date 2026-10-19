/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Layout

/-!
# Actual quadratic-candidate references and original width bounds
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates

open Execution
open ClassicalRoutines.NumberTheory
open QuadraticPrefix (writeInput)

noncomputable section

/-- Local candidate width helper for the factoring construction. -/
def candidateWidth (shortWidth : Nat) : Nat := QuadraticPrefix.centerWidth shortWidth + 1

/-- Typed record for the local refs data. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (shortWidth : Nat) where
  /-- Nested references for the quadratic prefix stage. -/
  quadraticPrefix : QuadraticPrefix.Refs ctx shortWidth
  /-- Writable cell for the center wide value. -/
  centerWide : CWriteRef ctx (.unsignedWord (candidateWidth shortWidth))
  centerWideRole : centerWide.toCStorageRef.role = .workspace
  /-- Writable cell for the root wide value. -/
  rootWide : CWriteRef ctx (.unsignedWord (candidateWidth shortWidth))
  rootWideRole : rootWide.toCStorageRef.role = .workspace
  /-- Nested references for the first stage. -/
  first : NatSub.Refs ctx (candidateWidth shortWidth)
  firstLeft : first.left = writeInput centerWide
  firstRight : first.right = writeInput rootWide
  /-- Writable cell for the second value. -/
  second : CWriteRef ctx (.product (.unsignedWord (candidateWidth shortWidth)) .bit)
  secondRole : second.toCStorageRef.role = .workspace

/-- Local first candidate helper for the factoring construction. -/
def firstCandidate {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) := writeInput refs.first.output
/-- Local second candidate helper for the factoring construction. -/
def secondCandidate {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) := CInputRef.first (writeInput refs.second)

/-- Typed record for the local separation data. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) : Prop where
  prefixSeparation : QuadraticPrefix.Separation refs.quadraticPrefix
  sqrtAvoidsCenterWide :
    refs.centerWide.key ∉ (writeInput refs.quadraticPrefix.sqrt.output).storageKeys
  centerAvoidsRootWide :
    refs.rootWide.toCStorageRef.key ∉ (writeInput refs.quadraticPrefix.center).storageKeys
  centerWideAvoidsRootWide :
    refs.rootWide.toCStorageRef.key ∉ (writeInput refs.centerWide).storageKeys
  centerWideAvoidsFirstOutput :
    refs.first.output.toCStorageRef.key ∉ (writeInput refs.centerWide).storageKeys
  rootWideAvoidsFirstOutput :
    refs.first.output.toCStorageRef.key ∉ (writeInput refs.rootWide).storageKeys
  centerWideAvoidsSecond : refs.second.toCStorageRef.key ∉ (writeInput refs.centerWide).storageKeys
  rootWideAvoidsSecond : refs.second.toCStorageRef.key ∉ (writeInput refs.rootWide).storageKeys
  firstOutputAvoidsSecond :
    refs.second.toCStorageRef.key ∉ (writeInput refs.first.output).storageKeys
  first : NatSub.Separation refs.first

/-- Avoidance of every cell written by the complete candidate routine. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shortWidth : Nat} (refs : Refs ctx shortWidth) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  prefixAvoids : QuadraticPrefix.PrefixFrameAvoids refs.quadraticPrefix other
  sqrt : QuadraticPrefix.SqrtFrameAvoids refs.quadraticPrefix other
  centerWide : refs.centerWide.toCStorageRef.key ∉ other.storageKeys
  rootWide : refs.rootWide.toCStorageRef.key ∉ other.storageKeys
  firstLessThan : refs.first.lessThan.toCStorageRef.key ∉ other.storageKeys
  firstOutput : refs.first.output.toCStorageRef.key ∉ other.storageKeys
  second : refs.second.toCStorageRef.key ∉ other.storageKeys

/-- Truncating the discriminant cannot make its square root exceed the original center. -/
lemma root_le_center (center modulus : Nat) : Nat.sqrt (center ^ 2 - modulus) ≤ center := by
  calc
    Nat.sqrt (center ^ 2 - modulus) ≤ Nat.sqrt (center ^ 2) :=
      Nat.sqrt_le_sqrt (Nat.sub_le _ _)
    _ = center := Nat.sqrt_eq' _

/-- The extra candidate bit holds the sum using only the original short-input word bound. -/
lemma candidate_capacity {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (store : Store ctx) :
    (store.read refs.quadraticPrefix.shortLog).toNat + 1 +
        Nat.sqrt (((store.read refs.quadraticPrefix.shortLog).toNat + 1) ^ 2 -
          (store.read refs.quadraticPrefix.modulus).toNat) <
      CShape.wordModulus (candidateWidth shortWidth) := by
  have centerFits := QuadraticPrefix.center_capacity refs.quadraticPrefix store
  calc
    _ ≤ ((store.read refs.quadraticPrefix.shortLog).toNat + 1) +
        ((store.read refs.quadraticPrefix.shortLog).toNat + 1) :=
      Nat.add_le_add_left (root_le_center _ _) _
    _ < CShape.wordModulus (QuadraticPrefix.centerWidth shortWidth) +
        CShape.wordModulus (QuadraticPrefix.centerWidth shortWidth) :=
      Nat.add_lt_add centerFits centerFits
    _ = CShape.wordModulus (candidateWidth shortWidth) := by
      simp [candidateWidth, CShape.wordModulus, pow_succ, Nat.mul_two]

/-- Exact original natural candidates, nonoverflow flag and complete actual caller frame. -/
structure Outcome {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}
    (refs : Refs ctx shortWidth) (before after : Store ctx) : Prop where
  first : (after.read (firstCandidate refs)).toNat =
    ((before.read refs.quadraticPrefix.shortLog).toNat + 1) -
      Nat.sqrt (((before.read refs.quadraticPrefix.shortLog).toNat + 1) ^ 2 -
        (before.read refs.quadraticPrefix.modulus).toNat)
  second : (after.read (secondCandidate refs)).toNat =
    ((before.read refs.quadraticPrefix.shortLog).toNat + 1) +
      Nat.sqrt (((before.read refs.quadraticPrefix.shortLog).toNat + 1) ^ 2 -
        (before.read refs.quadraticPrefix.modulus).toNat)
  carry : (after.read (CInputRef.second (writeInput refs.second))).toBool = false
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates
