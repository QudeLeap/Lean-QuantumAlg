/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Resources

/-!
# Fixed storage for declared retry primitives

The accepted bit, selected word and candidate product precede the sole bank.
First and reused batches share the same source, sample and factor cells.
Their resident and auxiliary bounds retain the original caller roles and
bound sequential scratch by its actual maximum. The pure storage allowance
is independent of the number of completed batches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

/-- Exactly the three persistent selector shapes are allocated before the real sampler. -/
def selectorSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.product .bit (.unsignedWord (modulusBits N))) +
    (SpacePool.ofShape (.unsignedWord (modulusBits N)) + SpacePool.ofShape .bit)

/-- The complete fixed sampler/recovery allowance is accompanied by one actual selector. -/
def additionalSpace (N : Nat) : SpacePool .quantum :=
  Batch.Recovery.additionalSpace N + selectorSpace N

/-- The three real selector cells contribute precisely their binary encoded capacity. -/
lemma declaredRetry_selectorSpace (N : Nat) :
    selectorSpace N = SpacePool.ofShape (.bits (2 * modulusBits N + 2)) := by
  ext axis
  cases axis <;> simp [selectorSpace, SpacePool.ofShape]
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma slots_resident :
    (callerContext base N).residentSpace = selectorSpace N + base.residentSpace := by
  simp only [callerContext, Native.Retry.Slots.context, Native.Retry.Slots.selectedContext,
    Native.Retry.Slots.acceptedContext, RuntimeCtx.residentSpace_addRetained]
  unfold selectorSpace
  ac_rfl

private lemma slots_peak_resident
    (path : (Native.Retry.Slots.allocate (model := model N) base (modulusBits N)).Path) :
    (Native.Retry.Slots.allocate (model := model N) base (modulusBits N)).peakResidentSpace
        path ≤
      (callerContext base N).residentSpace := by
  have first : base.residentSpace ≤ (Native.Retry.Slots.acceptedContext base).residentSpace :=
    fun _ => Nat.le_add_left _ _
  have second : (Native.Retry.Slots.acceptedContext base).residentSpace ≤
      (Native.Retry.Slots.selectedContext base (modulusBits N)).residentSpace :=
    fun _ => Nat.le_add_left _ _
  have third : (Native.Retry.Slots.selectedContext base (modulusBits N)).residentSpace ≤
      (callerContext base N).residentSpace := fun _ => Nat.le_add_left _ _
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · intro axis
    change max (base.residentSpace axis)
      (max ((Native.Retry.Slots.acceptedContext base).residentSpace axis) 0) ≤ _
    exact max_le ((first axis).trans ((second axis).trans (third axis)))
      (max_le ((second axis).trans (third axis)) (Nat.zero_le _))
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · intro axis
      change max ((Native.Retry.Slots.acceptedContext base).residentSpace axis)
        (max ((Native.Retry.Slots.selectedContext base (modulusBits N)).residentSpace axis) 0) ≤ _
      exact max_le ((second axis).trans (third axis)) (max_le (third axis) (Nat.zero_le _))
    · intro axis
      change max ((Native.Retry.Slots.selectedContext base (modulusBits N)).residentSpace axis)
        (max ((callerContext base N).residentSpace axis) 0) ≤ _
      exact max_le (third axis) (max_le le_rfl (Nat.zero_le _))

/-- The original bank and all retained results include exactly one persistent selector. -/
lemma declaredRetry_context_residentSpace :
    (context base noQuantum N).residentSpace =
      (Batch.retainedSpace N + selectorSpace N) + base.residentSpace := by
  change (Batch.context (callerContext base N)
    (caller_empty base noQuantum N) N).residentSpace = _
  rw [Batch.declaredBatch_context_residentSpace, slots_resident, add_assoc]

private lemma recovery_resident_allowance :
    Batch.Recovery.additionalSpace N + (callerContext base N).residentSpace =
      additionalSpace N + base.residentSpace := by
  rw [slots_resident]
  exact (add_assoc _ _ _).symm

private lemma caller_resident_allowance :
    (callerContext base N).residentSpace ≤
      additionalSpace N + base.residentSpace := by
  rw [slots_resident]
  intro axis
  change selectorSpace N axis + base.residentSpace axis ≤
    (Batch.Recovery.additionalSpace N axis + selectorSpace N axis) + base.residentSpace axis
  omega

private lemma context_resident_allowance :
    (context base noQuantum N).residentSpace ≤
      additionalSpace N + base.residentSpace := by
  rw [declaredRetry_context_residentSpace]
  intro axis
  change (Batch.retainedSpace N axis + selectorSpace N axis) + base.residentSpace axis ≤
    ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) + selectorSpace N axis) +
      base.residentSpace axis
  omega

private lemma first_resident (input : Input N) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (slots_peak_resident base N path.1).trans (caller_resident_allowance base N)
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (Batch.Recovery.declaredRecovery_first_peakResidentSpace_le (callerContext base N)
        (caller_empty base noQuantum N) N input path.2.1).trans_eq
          (recovery_resident_allowance base N)
    · exact (Optional.into_resident_le (model := model N)
        (.storage (factorRef base noQuantum N).toCStorageRef)
        (selectionRefs base noQuantum N) path.2.2).trans
          (context_resident_allowance base noQuantum N)

lemma next_resident (input : Input N) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (Batch.Recovery.declaredRecovery_next_peakResidentSpace_le (callerContext base N)
      (caller_empty base noQuantum N) N input path.1).trans_eq
        (recovery_resident_allowance base N)
  · exact (Optional.into_resident_le (model := model N)
      (.storage (factorRef base noQuantum N).toCStorageRef)
      (selectionRefs base noQuantum N) path.2).trans
        (context_resident_allowance base noQuantum N)

private lemma slots_auxiliary :
    (callerContext base N).auxiliarySpace = selectorSpace N + base.auxiliarySpace := by
  simp only [callerContext, Native.Retry.Slots.context, Native.Retry.Slots.selectedContext,
    Native.Retry.Slots.acceptedContext, RuntimeCtx.auxiliarySpace_addRetained]
  unfold selectorSpace
  ac_rfl

private lemma slots_peak_auxiliary
    (path : (Native.Retry.Slots.allocate (model := model N) base (modulusBits N)).Path) :
    (Native.Retry.Slots.allocate (model := model N) base (modulusBits N)).peakAuxiliarySpace
        path ≤
      (callerContext base N).auxiliarySpace := by
  have first : base.auxiliarySpace ≤ (Native.Retry.Slots.acceptedContext base).auxiliarySpace :=
    fun _ => Nat.le_add_left _ _
  have second : (Native.Retry.Slots.acceptedContext base).auxiliarySpace ≤
      (Native.Retry.Slots.selectedContext base (modulusBits N)).auxiliarySpace :=
    fun _ => Nat.le_add_left _ _
  have third : (Native.Retry.Slots.selectedContext base (modulusBits N)).auxiliarySpace ≤
      (callerContext base N).auxiliarySpace := fun _ => Nat.le_add_left _ _
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · intro axis
    change max (base.auxiliarySpace axis)
      (max ((Native.Retry.Slots.acceptedContext base).auxiliarySpace axis) 0) ≤ _
    exact max_le ((first axis).trans ((second axis).trans (third axis)))
      (max_le ((second axis).trans (third axis)) (Nat.zero_le _))
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · intro axis
      change max ((Native.Retry.Slots.acceptedContext base).auxiliarySpace axis)
        (max ((Native.Retry.Slots.selectedContext base (modulusBits N)).auxiliarySpace axis) 0) ≤ _
      exact max_le ((second axis).trans (third axis)) (max_le (third axis) (Nat.zero_le _))
    · intro axis
      change max ((Native.Retry.Slots.selectedContext base (modulusBits N)).auxiliarySpace axis)
        (max ((callerContext base N).auxiliarySpace axis) 0) ≤ _
      exact max_le (third axis) (max_le le_rfl (Nat.zero_le _))

/-- The original bank and all retained results include exactly one persistent selector. -/
lemma declaredRetry_context_auxiliarySpace :
    (context base noQuantum N).auxiliarySpace =
      (Batch.retainedSpace N + selectorSpace N) + base.auxiliarySpace := by
  change (Batch.context (callerContext base N)
    (caller_empty base noQuantum N) N).auxiliarySpace = _
  rw [Batch.declaredBatch_context_auxiliarySpace, slots_auxiliary, add_assoc]

private lemma recovery_auxiliary_allowance :
    Batch.Recovery.additionalSpace N + (callerContext base N).auxiliarySpace =
      additionalSpace N + base.auxiliarySpace := by
  rw [slots_auxiliary]
  exact (add_assoc _ _ _).symm

private lemma caller_auxiliary_allowance :
    (callerContext base N).auxiliarySpace ≤
      additionalSpace N + base.auxiliarySpace := by
  rw [slots_auxiliary]
  intro axis
  change selectorSpace N axis + base.auxiliarySpace axis ≤
    (Batch.Recovery.additionalSpace N axis + selectorSpace N axis) + base.auxiliarySpace axis
  omega

private lemma context_auxiliary_allowance :
    (context base noQuantum N).auxiliarySpace ≤
      additionalSpace N + base.auxiliarySpace := by
  rw [declaredRetry_context_auxiliarySpace]
  intro axis
  change (Batch.retainedSpace N axis + selectorSpace N axis) + base.auxiliarySpace axis ≤
    ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) + selectorSpace N axis) +
      base.auxiliarySpace axis
  omega

private lemma first_auxiliary (input : Input N) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (slots_peak_auxiliary base N path.1).trans (caller_auxiliary_allowance base N)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (Batch.Recovery.declaredRecovery_first_peakAuxiliarySpace_le (callerContext base N)
        (caller_empty base noQuantum N) N input path.2.1).trans_eq
          (recovery_auxiliary_allowance base N)
    · exact (Optional.into_auxiliary_le (model := model N)
        (.storage (factorRef base noQuantum N).toCStorageRef)
        (selectionRefs base noQuantum N) path.2.2).trans
          (context_auxiliary_allowance base noQuantum N)

lemma next_auxiliary (input : Input N) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (Batch.Recovery.declaredRecovery_next_peakAuxiliarySpace_le (callerContext base N)
      (caller_empty base noQuantum N) N input path.1).trans_eq
        (recovery_auxiliary_allowance base N)
  · exact (Optional.into_auxiliary_le (model := model N)
      (.storage (factorRef base noQuantum N).toCStorageRef)
      (selectionRefs base noQuantum N) path.2).trans
        (context_auxiliary_allowance base noQuantum N)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
