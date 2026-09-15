/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Execution

/-!
# The actual comparison tag and nominal factor result

The actual three comparison writes leave the candidate word unchanged when
their physical bit cells are separate. The following two representation
instructions then write exactly that candidate or the canonical absent
option, as determined by the same stored comparison bit.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open ClassicalRoutines.NumberTheory

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The real option instruction retains precisely the stored tag and candidate's natural value. -/
theorem pack_result_numeric (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (separate : cells.payload.key ≠ cells.lower.key) :
    (packStep cells output store).1.read (.storage output.toCStorageRef) =
      if (store.read (.storage cells.lower.toCStorageRef)).toBool then
        .optionSome (CShape.wordOfNat (modulusBits N)
          (store.read (.storage cells.candidate.toCStorageRef)).toNat)
      else .optionNone := by
  rw [pack_result cells output store separate]
  cases store.read (.storage cells.lower.toCStorageRef) with
  | bit value => cases value <;> rfl

/-- The actual comparisons and packaging return the same tested original candidate. -/
theorem checkedPack_result (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (lowerFree : cells.lower.key ∉
      (CInputRef.product (.storage cells.candidate.toCStorageRef) cells.modulus).storageKeys)
    (upperLower : cells.upper.key ≠ cells.lower.key)
    (upperCandidate : cells.upper.key ≠ cells.candidate.key)
    (payloadLower : cells.payload.key ≠ cells.lower.key) :
    (checkedPackStep cells output store).1.read (.storage output.toCStorageRef) =
      if decide ((store.read cells.one).toNat <
          (store.read (.storage cells.candidate.toCStorageRef)).toNat) &&
          decide ((store.read (.storage cells.candidate.toCStorageRef)).toNat <
            (store.read cells.modulus).toNat) then
        .optionSome (CShape.wordOfNat (modulusBits N)
          (store.read (.storage cells.candidate.toCStorageRef)).toNat)
      else .optionNone := by
  let compared := FactorRange.storeStep (checkRefs cells) store
  have tag : (compared.read (.storage cells.lower.toCStorageRef)).toBool =
      (decide ((store.read cells.one).toNat <
          (store.read (.storage cells.candidate.toCStorageRef)).toNat) &&
        decide ((store.read (.storage cells.candidate.toCStorageRef)).toNat <
          (store.read cells.modulus).toNat)) :=
    FactorRange.result (checkRefs cells) store lowerFree upperLower
  have lowerCandidate : cells.lower.key ∉
      (CInputRef.storage cells.candidate.toCStorageRef).storageKeys :=
    fun member => lowerFree (List.mem_append_left _ member)
  have candidateSame : compared.read (.storage cells.candidate.toCStorageRef) =
      store.read (.storage cells.candidate.toCStorageRef) :=
    FactorRange.read_other (checkRefs cells) (.storage cells.candidate.toCStorageRef) lowerCandidate
      (fun member => upperCandidate (List.mem_singleton.mp member)) store
  refine (pack_result_numeric cells output compared payloadLower).trans ?_
  rw [tag, candidateSame]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
