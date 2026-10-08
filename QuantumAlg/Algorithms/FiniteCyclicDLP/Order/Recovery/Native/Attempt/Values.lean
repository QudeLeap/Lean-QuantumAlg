/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Semantics
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Candidate and acceptance values of one checked recovery attempt

The raw modular routine determines a bounded candidate and two validity flags.
Acceptance additionally requires the declared group-power check against the
problem target.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalRoutines.FiniteCyclicDLP

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum} {width : Nat}

/-- The raw model determines the candidate, including its zero failure value. -/
@[expose] public def attemptCandidateValue
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (input : CShape.Value (.fixedVector (width + width) (.finite 2))) :
    CShape.Value (.unsignedWord width) :=
  (RawRecovery.outputCells spec (RawRecovery.Native.preparationInput input)).second.first

/-- The two raw flags and exact group equation determine acceptance. -/
@[expose] public def attemptAcceptedValue
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CShape.Value
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2))) : Bool :=
  let raw := RawRecovery.outputCells spec (RawRecovery.Native.preparationInput input)
  (raw.first.toBool && raw.second.second.toBool) &&
    decide (P.generator ^ (attemptCandidateValue spec input).toNat = P.target)

/-- The raw candidate always fits the supplied modulus, on success and failure. -/
public theorem attemptCandidateValue_lt
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (input : CShape.Value (.fixedVector (width + width) (.finite 2))) :
    (attemptCandidateValue spec input).toNat < spec.modulus := by
  cases result : RawRecovery.outputOf spec (RawRecovery.Native.preparationInput input) with
  | none =>
      simpa only [attemptCandidateValue, RawRecovery.outputCells, result,
        CShape.Value.second, CShape.Value.first, CShape.wordOfNat_val, Nat.zero_mod] using
          ClassicalAlgorithms.Modular.modulusSpec_modulus_pos spec
  | some output =>
      have fits : output.candidate.val < 2 ^ width :=
        output.candidate.isLt.trans_le spec.le_capacity
      have reduced : output.candidate.val % 2 ^ width = output.candidate.val :=
        Nat.mod_eq_of_lt fits
      simp only [attemptCandidateValue, RawRecovery.outputCells, result,
        CShape.Value.second, CShape.Value.first, CShape.wordOfNat_val,
        CShape.wordModulus, reduced]
      exact output.candidate.isLt

private theorem raw_store (refs : AttemptRefs ctx width) (store : Store ctx) :
    store.applyOp (rawAcceptanceOp refs) =
      store.write refs.rawAccepted
        (.bit ((store.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
          (store.read (.storage refs.reconstruction.toCStorageRef)).toBool)) := by
  change store.write refs.rawAccepted (Resource.BitOpcode.eval .and
    (.product (store.read (.storage refs.inverseSuccess.toCStorageRef))
      (store.read (.storage refs.reconstruction.toCStorageRef)))) = _
  cases store.read (.storage refs.inverseSuccess.toCStorageRef) with
  | bit inverse =>
      cases store.read (.storage refs.reconstruction.toCStorageRef) with
      | bit reconstructed => rfl

private theorem accepted_store (refs : AttemptRefs ctx width) (store : Store ctx) :
    store.applyOp (candidateAcceptanceOp refs) =
      store.write refs.acceptedCandidate
        (.bit ((store.read (.storage refs.rawAccepted.toCStorageRef)).toBool &&
          (store.read (.storage refs.powerEqualsTarget.toCStorageRef)).toBool)) := by
  change store.write refs.acceptedCandidate (Resource.BitOpcode.eval .and
    (.product (store.read (.storage refs.rawAccepted.toCStorageRef))
      (store.read (.storage refs.powerEqualsTarget.toCStorageRef)))) = _
  cases store.read (.storage refs.rawAccepted.toCStorageRef) with
  | bit raw =>
      cases store.read (.storage refs.powerEqualsTarget.toCStorageRef) with
      | bit equal => rfl

/-- The two conjunctions combine their three actual Boolean inputs. -/
public theorem acceptanceRecord_value
    (refs : AttemptRefs ctx width)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    (rawEquality : refs.rawAccepted.key ≠ refs.powerEqualsTarget.key) :
    (acceptanceRecord P refs entry).1.1.read
        (.storage refs.acceptedCandidate.toCStorageRef) =
      .bit (((entry.1.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
        (entry.1.read (.storage refs.reconstruction.toCStorageRef)).toBool) &&
          (entry.1.read (.storage refs.powerEqualsTarget.toCStorageRef)).toBool) := by
  rw [acceptanceRecord_store, raw_store, accepted_store]
  rw [Store.read_write_other entry.1 refs.rawAccepted refs.powerEqualsTarget.toCStorageRef
    _ rawEquality]
  rw [Store.read_write_same, Store.read_write_same]
  rfl

/-- The actual power check followed by both conjunctions. -/
@[expose] public def verificationRecord
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : AttemptRefs ctx width)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      ((powerCheck P candidate refs.powerEqualsTarget).seq
        (acceptanceSuffix P refs)).Path :=
  Circuit.sequenceRecord (model := OrderExecution.model P) _ _
    (powerCheckRecord P candidate refs.powerEqualsTarget)
    (acceptanceRecord P refs) entry

/-- The hidden group service and conjunctions compute the exact checked value. -/
public theorem verificationRecord_value
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : AttemptRefs ctx width)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    (candidateSeparate : refs.powerEqualsTarget.key ∉ candidate.storageKeys)
    (inverseSeparate : refs.powerEqualsTarget.key ∉
      (CInputRef.storage refs.inverseSuccess.toCStorageRef).storageKeys)
    (reconstructionSeparate : refs.powerEqualsTarget.key ∉
      (CInputRef.storage refs.reconstruction.toCStorageRef).storageKeys)
    (rawEquality : refs.rawAccepted.key ≠ refs.powerEqualsTarget.key) :
    (verificationRecord P candidate refs entry).1.1.read
        (.storage refs.acceptedCandidate.toCStorageRef) =
      .bit (((entry.1.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
        (entry.1.read (.storage refs.reconstruction.toCStorageRef)).toBool) &&
          decide (P.generator ^ (entry.1.read candidate).toNat = P.target)) := by
  let checked := powerCheckRecord P candidate refs.powerEqualsTarget entry
  have accepted := acceptanceRecord_value P refs checked.1 rawEquality
  have inverse := powerCheckRecord_preserves_read P candidate refs.powerEqualsTarget entry
    (.storage refs.inverseSuccess.toCStorageRef) inverseSeparate
  have reconstructed := powerCheckRecord_preserves_read P candidate refs.powerEqualsTarget entry
    (.storage refs.reconstruction.toCStorageRef) reconstructionSeparate
  have equality := powerCheckRecord_value P candidate refs.powerEqualsTarget entry candidateSeparate
  change (acceptanceRecord P refs checked.1).1.1.read
    (.storage refs.acceptedCandidate.toCStorageRef) = _
  rw [accepted, inverse, reconstructed, equality]
  rfl

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
