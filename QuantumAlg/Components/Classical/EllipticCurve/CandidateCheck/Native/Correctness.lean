/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Correctness

/-!
# Original candidate acceptance from actual scalar and target comparison

The stored candidate is interpreted by the original natural scalar action.
The real comparator accepts precisely that point's equality with the target.
Both original success conjunctions retain their incoming flags. Structural
separation here concerns the low-level caller cells; fresh placement supplies
it when assembling the complete recovery endpoint.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

private theorem candidateBits_separate (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (key : StorageKey) (separate : key ∉ candidate.storageKeys) :
    key ∉ (candidateBits candidate).storageKeys := by
  change key ∉ (List.ofFn (fun _index : Fin scalarWidth => candidate.storageKeys)).flatten
  intro present
  obtain ⟨keys, member, contained⟩ := List.mem_flatten.mp present
  obtain ⟨_index, rfl⟩ := List.mem_ofFn.mp member
  exact separate contained

private theorem conjunction_read (flag : CInputRef ctx .bit) (accepted : CWriteRef ctx .bit)
    (store : Store ctx) :
    (store.applyOp (conjunctionOp flag accepted)).read (.storage accepted.toCStorageRef) =
      .bit ((store.read (.storage accepted.toCStorageRef)).toBool &&
        (store.read flag).toBool) := by
  change (store.applyOp (conjunctionOp flag accepted)).read
    (.storage (conjunctionOp flag accepted).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change Resource.BitOpcode.and.eval
    (.product (store.read (.storage accepted.toCStorageRef)) (store.read flag)) = _
  cases store.read (.storage accepted.toCStorageRef)
  cases store.read flag
  rfl

private theorem bit_true_iff (value : CShape.Value .bit) :
    value.toBool = true ↔ value = .bit true := by
  cases value
  simp only [CShape.Value.toBool, CShape.Value.bit.injEq]

/-- Actual acceptance is exactly the original target equation and both original success flags. -/
theorem verifyStep_accepts_iff {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (store : Store ctx) (hidden : model.HiddenState)
    (scalar : ClassicalAlgorithms.Word scalarWidth)
    (basePoint targetPoint : Pure.Point spec)
    (candidateValue : store.read candidate = .unsignedWord scalar)
    (baseRep : PointRepresents spec (store.read base) basePoint)
    (targetRep : PointRepresents spec (store.read target) targetPoint)
    (scalarCandidate : scalarResult.key ∉ candidate.storageKeys)
    (scalarBase : scalarResult.key ∉ base.storageKeys)
    (scalarTarget : scalarResult.key ∉ target.storageKeys)
    (scalarInverse : scalarResult.key ∉ inverseSuccess.storageKeys)
    (scalarReconstruction : scalarResult.key ∉ reconstruction.storageKeys)
    (acceptedInverse : accepted.key ∉ inverseSuccess.storageKeys)
    (acceptedReconstruction : accepted.key ∉ reconstruction.storageKeys) :
    ((verifyStep spec candidate base target inverseSuccess reconstruction
      scalarResult accepted (store, hidden)).1.1.read
        (.storage accepted.toCStorageRef)).toBool = true ↔
      scalar.val • basePoint = targetPoint ∧
        (store.read inverseSuccess).toBool = true ∧
        (store.read reconstruction).toBool = true := by
  let afterScalar := (ScalarMul.Native.scalarStep spec (candidateBits candidate)
    base scalarResult (store, hidden)).1
  let afterComparison := (PointEquality.Native.compareStep
    (.storage scalarResult.toCStorageRef) target accepted afterScalar.1).1
  let afterInverse := afterComparison.applyOp (conjunctionOp inverseSuccess accepted)
  have scalarRep : PointRepresents spec
      (afterScalar.1.read (.storage scalarResult.toCStorageRef))
      (scalar.val • basePoint) := by
    apply ScalarMul.Native.scalarStep_represents_eval spec (candidateBits candidate)
      base scalarResult (store, hidden) ⟨scalar, basePoint⟩
      (candidateBits_separate candidate scalarResult.key scalarCandidate) scalarBase
    · intro index
      change ((store.read candidate).wordBitGet index).toBool = _
      rw [candidateValue]
      rfl
    · exact baseRep
  have targetAfter : PointRepresents spec (afterScalar.1.read target) targetPoint := by
    rw [ScalarMul.Native.scalarStep_preserves_read spec (candidateBits candidate)
      base scalarResult (store, hidden) target scalarTarget]
    exact targetRep
  have comparison : (afterComparison.read (.storage accepted.toCStorageRef)).toBool = true ↔
      scalar.val • basePoint = targetPoint :=
    (bit_true_iff _).trans (PointEquality.Native.compareInto_accepts_iff spec
      (.storage scalarResult.toCStorageRef) target accepted afterScalar.1
      (scalar.val • basePoint) targetPoint scalarRep targetAfter)
  have inverseAfter : afterComparison.read inverseSuccess = store.read inverseSuccess :=
    (PointEquality.Native.compareInto_preserves_read _ _ accepted afterScalar.1
      inverseSuccess acceptedInverse).trans
      (ScalarMul.Native.scalarStep_preserves_read spec (candidateBits candidate)
        base scalarResult (store, hidden) inverseSuccess scalarInverse)
  have reconstructionAfter : afterInverse.read reconstruction = store.read reconstruction :=
    (Store.read_applyOp_of_not_mem_storageKeys afterComparison
      (conjunctionOp inverseSuccess accepted) reconstruction acceptedReconstruction).trans
      ((PointEquality.Native.compareInto_preserves_read _ _ accepted afterScalar.1
        reconstruction acceptedReconstruction).trans
        (ScalarMul.Native.scalarStep_preserves_read spec (candidateBits candidate)
          base scalarResult (store, hidden) reconstruction scalarReconstruction))
  rw [verifyStep_store]
  change ((afterInverse.applyOp (conjunctionOp reconstruction accepted)).read
    (.storage accepted.toCStorageRef)).toBool = true ↔ _
  rw [conjunction_read, reconstructionAfter]
  change ((afterInverse.read (.storage accepted.toCStorageRef)).toBool &&
    (store.read reconstruction).toBool) = true ↔ _
  change (((afterComparison.applyOp (conjunctionOp inverseSuccess accepted)).read
    (.storage accepted.toCStorageRef)).toBool && (store.read reconstruction).toBool) = true ↔ _
  rw [conjunction_read, inverseAfter]
  change (((afterComparison.read (.storage accepted.toCStorageRef)).toBool &&
    (store.read inverseSuccess).toBool) && (store.read reconstruction).toBool) = true ↔ _
  simp only [Bool.and_eq_true, comparison, and_assoc]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
