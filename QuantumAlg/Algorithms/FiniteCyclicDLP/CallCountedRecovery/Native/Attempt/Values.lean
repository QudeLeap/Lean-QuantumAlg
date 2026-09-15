/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt.Semantics

/-!
# Exact candidate and acceptance values of the original recovery attempt

The original raw model supplies a bounded candidate on both inverse outcomes.
The real word equality and two conjunctions write precisely their original
Boolean expression. Internal layout conditions mention only actual write
identities; the enclosing six-cell allocation discharges them.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalRoutines.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

/-- The original raw model determines the candidate, including the zero failure value. -/
def attemptCandidateValue (P : Parameters G)
    (input : CShape.Value (.fixedVector (P.width + P.width) (.finite 2))) :
    CShape.Value (.unsignedWord P.width) :=
  (RawRecovery.outputCells P.spec (RawRecovery.Native.preparationInput input)).second.first

/-- Both original raw flags and the original encoded-power equality determine acceptance. -/
def attemptAcceptedValue (P : Parameters G)
    (input : CShape.Value (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CShape.Value (.unsignedWord P.width)) : Bool :=
  let raw := RawRecovery.outputCells P.spec (RawRecovery.Native.preparationInput input)
  (raw.first.toBool && raw.second.second.toBool) &&
    decide ((P.access.encode (P.generator ^ (attemptCandidateValue P input).toNat)).toNat =
      target.toNat)

/-- The actual raw candidate always fits the original modulus, on success and failure. -/
theorem groupAttempt_candidate_lt (P : Parameters G)
    (input : CShape.Value (.fixedVector (P.width + P.width) (.finite 2))) :
    (attemptCandidateValue P input).toNat < P.spec.modulus := by
  cases result : RawRecovery.outputOf P.spec (RawRecovery.Native.preparationInput input) with
  | none =>
      simpa only [attemptCandidateValue, RawRecovery.outputCells, result, CShape.Value.second,
        CShape.Value.first, CShape.wordOfNat_val, Nat.zero_mod] using P.order_pos
  | some output =>
      simpa only [attemptCandidateValue, RawRecovery.outputCells, result, CShape.Value.second,
        CShape.Value.first, CShape.wordOfNat_val, CShape.wordModulus,
        Nat.mod_eq_of_lt (output.candidate.isLt.trans P.modulus_lt_twoPow)] using
          output.candidate.isLt

private theorem equality_store (powered target : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width) (store : Store ctx) :
    store.applyOp (powerEqualityOp powered target refs) =
      store.write refs.powerEqualsTarget
        (.bit (decide ((store.read powered).toNat = (store.read target).toNat))) := rfl

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

/-- Three actual instructions write exactly the comparison and both original flag conjunctions. -/
theorem groupAttempt_acceptanceRecord_store
    (powered target : CInputRef ctx (.unsignedWord width)) (refs : AttemptRefs ctx width)
    (store : Store ctx)
    (equalityInverse : refs.powerEqualsTarget.key ≠ refs.inverseSuccess.key)
    (equalityReconstruction : refs.powerEqualsTarget.key ≠ refs.reconstruction.key)
    (rawEquality : refs.rawAccepted.key ≠ refs.powerEqualsTarget.key) :
    (acceptanceRecord powered target refs store).1 =
      let equal := decide ((store.read powered).toNat = (store.read target).toNat)
      let raw := (store.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
        (store.read (.storage refs.reconstruction.toCStorageRef)).toBool
      ((store.write refs.powerEqualsTarget (.bit equal)).write refs.rawAccepted (.bit raw)).write
        refs.acceptedCandidate (.bit (raw && equal)) := by
  rw [acceptanceRecord_store, equality_store, raw_store, accepted_store]
  rw [Store.read_write_other _ refs.powerEqualsTarget refs.inverseSuccess.toCStorageRef
    _ equalityInverse]
  rw [Store.read_write_other _ refs.powerEqualsTarget refs.reconstruction.toCStorageRef
    _ equalityReconstruction]
  rw [Store.read_write_same]
  rw [Store.read_write_other _ refs.rawAccepted refs.powerEqualsTarget.toCStorageRef _ rawEquality]
  rw [Store.read_write_same]
  rfl

/-- The final actual acceptance bit is the two original raw flags and the original word equality. -/
theorem groupAttempt_acceptanceRecord_value
    (powered target : CInputRef ctx (.unsignedWord width)) (refs : AttemptRefs ctx width)
    (store : Store ctx)
    (equalityInverse : refs.powerEqualsTarget.key ≠ refs.inverseSuccess.key)
    (equalityReconstruction : refs.powerEqualsTarget.key ≠ refs.reconstruction.key)
    (rawEquality : refs.rawAccepted.key ≠ refs.powerEqualsTarget.key) :
    (acceptanceRecord powered target refs store).1.read
        (.storage refs.acceptedCandidate.toCStorageRef) =
      .bit (((store.read (.storage refs.inverseSuccess.toCStorageRef)).toBool &&
        (store.read (.storage refs.reconstruction.toCStorageRef)).toBool) &&
          decide ((store.read powered).toNat = (store.read target).toNat)) := by
  rw [groupAttempt_acceptanceRecord_store powered target refs store
    equalityInverse equalityReconstruction rawEquality]
  exact Store.read_write_same _ _ _

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
