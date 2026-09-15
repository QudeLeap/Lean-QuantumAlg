/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Power
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure

/-!
# Actual single group-power recovery attempt

The six original attempt cells are allocated in their original chronological
order. Actual raw recovery exposes inverse status, candidate and reconstruction
through its three original copies. Every result, including failure, proceeds
through the fresh group-power scan, literal word equality and both conjunctions.
The caller continuation runs before the accumulator and six attempt cells leave
scope, retaining the original location of the subsequent first-success selector.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

/-- Actual writable destinations of the original three raw observations and three tests. -/
structure AttemptRefs (ctx : RuntimeCtx .quantum) (width : Nat) where
  /-- Actual checked-inverse status. -/
  inverseSuccess : CWriteRef ctx .bit
  /-- Actual raw recovered word. -/
  candidate : CWriteRef ctx (.unsignedWord width)
  /-- Actual reconstruction flag. -/
  reconstruction : CWriteRef ctx .bit
  /-- Result of the powered-word equality. -/
  powerEqualsTarget : CWriteRef ctx .bit
  /-- Conjunction of the two original raw flags. -/
  rawAccepted : CWriteRef ctx .bit
  /-- Conjunction of raw acceptance with power equality. -/
  acceptedCandidate : CWriteRef ctx .bit

/-- The stack lists the last allocated cell first, preserving the six original allocations. -/
def attemptShapes (width : Nat) : List CShape :=
  [.bit, .bit, .bit, .bit, .unsignedWord width, .bit]

/-- Name the actual six cells in their original semantic roles. -/
def attemptRefs (cells : Cells ctx (attemptShapes width)) : AttemptRefs ctx width where
  inverseSuccess := cells.tail.tail.tail.tail.tail.head.ref
  candidate := cells.tail.tail.tail.tail.head.ref
  reconstruction := cells.tail.tail.tail.head.ref
  powerEqualsTarget := cells.tail.tail.head.ref
  rawAccepted := cells.tail.head.ref
  acceptedCandidate := cells.head.ref

/-- All six writable references retain their physical identities through the power scope. -/
def AttemptRefs.lift {inner : RuntimeCtx .quantum} (refs : AttemptRefs ctx width)
    (transport : Transport ctx inner) : AttemptRefs inner width where
  inverseSuccess := transport.liftWrite refs.inverseSuccess
  candidate := transport.liftWrite refs.candidate
  reconstruction := transport.liftWrite refs.reconstruction
  powerEqualsTarget := transport.liftWrite refs.powerEqualsTarget
  rawAccepted := transport.liftWrite refs.rawAccepted
  acceptedCandidate := transport.liftWrite refs.acceptedCandidate

/-- The original literal comparison consumes the actual accumulator and actual target word. -/
def powerEqualityOp (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product powered target) refs.powerEqualsTarget

/-- The original first conjunction combines both raw flags. -/
def rawAcceptanceOp (refs : AttemptRefs ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (.storage refs.inverseSuccess.toCStorageRef)
    (.storage refs.reconstruction.toCStorageRef)) refs.rawAccepted

/-- The original second conjunction adds the actual powered-word equality. -/
def candidateAcceptanceOp (refs : AttemptRefs ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (.storage refs.rawAccepted.toCStorageRef)
    (.storage refs.powerEqualsTarget.toCStorageRef)) refs.acceptedCandidate

/-- The same three real instructions always follow the complete power scan. -/
def acceptanceSuffix (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical (powerEqualityOp powered target refs))
    (.seq (.classical (rawAcceptanceOp refs)) (.classical (candidateAcceptanceOp refs)))

/-- Raw exposure precedes every power scan, including a failed checked inversion. -/
def attemptBody (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : AttemptRefs ctx P.width)
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      CInputRef inner .bit → Transport ctx inner → Circuit inner inner) : Circuit ctx ctx :=
  .seq (RawRecovery.Native.singleIntoCells P.spec input refs.inverseSuccess refs.candidate
      refs.reconstruction)
    (withPowerAccumulator P.access P.generator (.storage refs.candidate.toCStorageRef)
      fun powered transport =>
        let lifted := refs.lift transport
        .seq (acceptanceSuffix powered (transport.liftInput target) lifted)
          (body (.storage lifted.candidate.toCStorageRef)
            (.storage lifted.acceptedCandidate.toCStorageRef) transport))

/-- Six real attempt cells and one nested power accumulator remain live through the caller. -/
def withAttempt (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width))
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord P.width) →
      CInputRef inner .bit → Transport ctx inner → Circuit inner inner) : Circuit ctx ctx :=
  withCells ctx (attemptShapes P.width) fun cells _ transport _ =>
    attemptBody P (transport.liftInput input) (transport.liftInput target) (attemptRefs cells)
      (fun candidate accepted innerTransport =>
        body candidate accepted (transport.compose innerTransport))

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
