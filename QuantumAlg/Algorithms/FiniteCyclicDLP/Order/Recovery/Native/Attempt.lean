/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Resources.Modulus
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure
public import QuantumAlg.Components.Classical.Model.BitWord.Execution
public import QuantumAlg.Core.Execution.Classical.Workspace.Allocate
public import QuantumAlg.Util.Classical.Modular.Basic
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure

/-!
# One representation-independent recovery attempt

Raw integer recovery exposes its actual candidate and two validity flags. The
stateful group service is explicitly reset, evaluates the generator power in
hidden state and returns only the target-comparison bit.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- Writable observations and tests of one actual recovery attempt. -/
public structure AttemptRefs (ctx : RuntimeCtx .quantum) (width : Nat) where
  /-- Whether modular inversion succeeded for the sampled denominator. -/
  inverseSuccess : CWriteRef ctx .bit
  /-- Candidate discrete logarithm reconstructed by the attempt. -/
  candidate : CWriteRef ctx (.unsignedWord width)
  /-- Whether the reconstructed congruence passes its arithmetic check. -/
  reconstruction : CWriteRef ctx .bit
  /-- Whether the candidate's declared group power equals the target. -/
  powerEqualsTarget : CWriteRef ctx .bit
  /-- Conjunction of the two mathematical raw-recovery checks. -/
  rawAccepted : CWriteRef ctx .bit
  /-- Final acceptance bit after the abstract group comparison. -/
  acceptedCandidate : CWriteRef ctx .bit

/-- The stack lists the deepest cells first while retaining semantic names. -/
public def attemptShapes (width : Nat) : List CShape :=
  [.bit, .bit, .bit, .bit, .unsignedWord width, .bit]

/-- Name the six actual attempt cells. -/
public def attemptRefs {width : Nat} (cells : Cells ctx (attemptShapes width)) :
    AttemptRefs ctx width where
  inverseSuccess := cells.tail.tail.tail.tail.tail.head.ref
  candidate := cells.tail.tail.tail.tail.head.ref
  reconstruction := cells.tail.tail.tail.head.ref
  powerEqualsTarget := cells.tail.tail.head.ref
  rawAccepted := cells.tail.head.ref
  acceptedCandidate := cells.head.ref

/-- Preserve all attempt destinations through a surrounding lexical scope. -/
public def AttemptRefs.lift {width : Nat} {inner : RuntimeCtx .quantum}
    (refs : AttemptRefs ctx width) (transport : Transport ctx inner) :
    AttemptRefs inner width where
  inverseSuccess := transport.liftWrite refs.inverseSuccess
  candidate := transport.liftWrite refs.candidate
  reconstruction := transport.liftWrite refs.reconstruction
  powerEqualsTarget := transport.liftWrite refs.powerEqualsTarget
  rawAccepted := transport.liftWrite refs.rawAccepted
  acceptedCandidate := transport.liftWrite refs.acceptedCandidate

/-- Both mathematical raw-recovery checks must hold. -/
@[expose] public def rawAcceptanceOp {width : Nat} (refs : AttemptRefs ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx
    (.product (.storage refs.inverseSuccess.toCStorageRef)
      (.storage refs.reconstruction.toCStorageRef))
    refs.rawAccepted

/-- A candidate is accepted only when raw recovery and the abstract group
comparison both succeed. -/
@[expose] public def candidateAcceptanceOp {width : Nat} (refs : AttemptRefs ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx
    (.product (.storage refs.rawAccepted.toCStorageRef)
      (.storage refs.powerEqualsTarget.toCStorageRef))
    refs.acceptedCandidate

/-- Both actual conjunctions follow the declared group-power check. -/
@[expose] public def acceptanceSuffix {width : Nat} (refs : AttemptRefs ctx width) :
    Circuit (OrderExecution.model P) ctx ctx :=
  .seq (BitWord.instruction (execution := OrderExecution.model P) (rawAcceptanceOp refs))
    (BitWord.instruction (execution := OrderExecution.model P) (candidateAcceptanceOp refs))

/-- Raw recovery, group verification and a caller continuation share the same
lexical attempt cells. -/
@[expose] public def attemptBody (spec : ClassicalAlgorithms.Modular.ModulusSpec
      (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : AttemptRefs ctx (OrderPreparation.width P))
    (body : CInputRef ctx (.unsignedWord (OrderPreparation.width P)) →
      CInputRef ctx .bit → Circuit (OrderExecution.model P) ctx ctx) :
    Circuit (OrderExecution.model P) ctx ctx :=
  .seq (RawRecovery.Native.singleIntoCells spec input refs.inverseSuccess refs.candidate
      refs.reconstruction)
    (.seq (powerCheck P (.storage refs.candidate.toCStorageRef) refs.powerEqualsTarget)
      (.seq (acceptanceSuffix P refs)
        (body (.storage refs.candidate.toCStorageRef)
          (.storage refs.acceptedCandidate.toCStorageRef))))

/-- Allocate the six attempt cells around one complete checked candidate. -/
@[expose] public def withAttempt
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (body : ∀ {inner : RuntimeCtx .quantum},
      CInputRef inner (.unsignedWord (OrderPreparation.width P)) →
      CInputRef inner .bit → Transport ctx inner →
        Circuit (OrderExecution.model P) inner inner) :
    Circuit (OrderExecution.model P) ctx ctx :=
  withCells (model := OrderExecution.model P) ctx
      (attemptShapes (OrderPreparation.width P)) fun cells _ transport _ =>
    attemptBody P spec (transport.liftInput input) (attemptRefs cells)
      (fun candidate accepted => body candidate accepted transport)

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
