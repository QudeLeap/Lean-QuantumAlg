/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Recovery.Resources

/-!
# Actual fixed storage throughout the positive oracle retry

The accepted bit, selected word and unpacked candidate product are retained
once before the sole bank. Every later batch uses these same cells, source,
sixteen samples and factor output. Sequential source, reset and recovery
scratch is bounded by its actual maximum. Selection and the final paid pack
use existing destinations. No space term grows with the retry count.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry

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
theorem nativeOracle_retry_selectorSpace (N : Nat) :
    selectorSpace N = SpacePool.ofShape (.bits (2 * modulusBits N + 2)) := by
  ext axis
  cases axis <;> simp [selectorSpace, SpacePool.ofShape]
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem slots_resident :
    (callerContext base N).residentSpace = selectorSpace N + base.residentSpace := by
  simp only [callerContext, Slots.context, Slots.selectedContext, Slots.acceptedContext,
    RuntimeCtx.residentSpace_addRetained]
  unfold selectorSpace
  ac_rfl

private theorem slots_peak_resident (path : (Slots.allocate base (modulusBits N)).Path) :
    (Slots.allocate base (modulusBits N)).peakResidentSpace path ≤
      (callerContext base N).residentSpace := by
  have first : base.residentSpace ≤ (Slots.acceptedContext base).residentSpace :=
    fun _ => Nat.le_add_left _ _
  have second : (Slots.acceptedContext base).residentSpace ≤
      (Slots.selectedContext base (modulusBits N)).residentSpace := fun _ => Nat.le_add_left _ _
  have third : (Slots.selectedContext base (modulusBits N)).residentSpace ≤
      (callerContext base N).residentSpace := fun _ => Nat.le_add_left _ _
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · intro axis
    change max (base.residentSpace axis)
      (max ((Slots.acceptedContext base).residentSpace axis) 0) ≤ _
    exact max_le ((first axis).trans ((second axis).trans (third axis)))
      (max_le ((second axis).trans (third axis)) (Nat.zero_le _))
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · intro axis
      change max ((Slots.acceptedContext base).residentSpace axis)
        (max ((Slots.selectedContext base (modulusBits N)).residentSpace axis) 0) ≤ _
      exact max_le ((second axis).trans (third axis)) (max_le (third axis) (Nat.zero_le _))
    · intro axis
      change max ((Slots.selectedContext base (modulusBits N)).residentSpace axis)
        (max ((callerContext base N).residentSpace axis) 0) ≤ _
      exact max_le (third axis) (max_le le_rfl (Nat.zero_le _))

/-- The original bank and all retained results include exactly one persistent selector. -/
theorem nativeOracle_retry_context_residentSpace :
    (context base noQuantum N).residentSpace =
      (Batch.retainedSpace N + selectorSpace N) + base.residentSpace := by
  change (Batch.context (callerContext base N)
    (caller_empty base noQuantum N) N).residentSpace = _
  rw [Batch.nativeOracle_batch_context_residentSpace, slots_resident, add_assoc]

private theorem recovery_resident_allowance :
    Batch.Recovery.additionalSpace N + (callerContext base N).residentSpace =
      additionalSpace N + base.residentSpace := by
  rw [slots_resident]
  exact (add_assoc _ _ _).symm

private theorem caller_resident_allowance :
    (callerContext base N).residentSpace ≤
      additionalSpace N + base.residentSpace := by
  rw [slots_resident]
  intro axis
  change selectorSpace N axis + base.residentSpace axis ≤
    (Batch.Recovery.additionalSpace N axis + selectorSpace N axis) + base.residentSpace axis
  omega

private theorem context_resident_allowance :
    (context base noQuantum N).residentSpace ≤
      additionalSpace N + base.residentSpace := by
  rw [nativeOracle_retry_context_residentSpace]
  intro axis
  change (Batch.retainedSpace N axis + selectorSpace N axis) + base.residentSpace axis ≤
    ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) + selectorSpace N axis) +
      base.residentSpace axis
  omega

private theorem first_resident (input : Input N) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (slots_peak_resident base N path.1).trans (caller_resident_allowance base N)
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (Batch.Recovery.nativeOracle_recovery_first_peakResidentSpace_le (callerContext base N)
        (caller_empty base noQuantum N) N input path.2.1).trans_eq
          (recovery_resident_allowance base N)
    · exact (Optional.into_resident_le
        (.storage (factorRef base noQuantum N).toCStorageRef)
        (selectionRefs base noQuantum N) path.2.2).trans
          (context_resident_allowance base noQuantum N)

private theorem next_resident (input : Input N) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (Batch.Recovery.nativeOracle_recovery_next_peakResidentSpace_le (callerContext base N)
      (caller_empty base noQuantum N) N input path.1).trans_eq
        (recovery_resident_allowance base N)
  · exact (Optional.into_resident_le
      (.storage (factorRef base noQuantum N).toCStorageRef)
      (selectionRefs base noQuantum N) path.2).trans
        (context_resident_allowance base noQuantum N)

/-- Every actual retry count shares the same complete resident storage allowance. -/
theorem nativeOracle_retry_peakResidentSpace_le (input : Input N) (laterCount : Nat)
    (path : (code base noQuantum N input laterCount).Path) :
    (code base noQuantum N input laterCount).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  have entry := context_resident_allowance base noQuantum N
  have tail := Circuit.forRange_resident_le laterCount
    (fun _ => next base noQuantum N input) (additionalSpace N + base.residentSpace) entry
    (fun _ => next_resident base noQuantum N input) path.2.1
  have finalPack : (pack base noQuantum N).peakResidentSpace path.2.2 =
      (context base noQuantum N).residentSpace := by
    funext axis
    exact Nat.max_zero _
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le
    (first_resident base noQuantum N input path.1) ?_)
  exact (Circuit.peakResidentSpace_seq _ _ path.2).le.trans
    (SpacePool.max_le tail (finalPack.trans_le entry))

private theorem slots_auxiliary :
    (callerContext base N).auxiliarySpace = selectorSpace N + base.auxiliarySpace := by
  simp only [callerContext, Slots.context, Slots.selectedContext, Slots.acceptedContext,
    RuntimeCtx.auxiliarySpace_addRetained]
  unfold selectorSpace
  ac_rfl

private theorem slots_peak_auxiliary (path : (Slots.allocate base (modulusBits N)).Path) :
    (Slots.allocate base (modulusBits N)).peakAuxiliarySpace path ≤
      (callerContext base N).auxiliarySpace := by
  have first : base.auxiliarySpace ≤ (Slots.acceptedContext base).auxiliarySpace :=
    fun _ => Nat.le_add_left _ _
  have second : (Slots.acceptedContext base).auxiliarySpace ≤
      (Slots.selectedContext base (modulusBits N)).auxiliarySpace := fun _ => Nat.le_add_left _ _
  have third : (Slots.selectedContext base (modulusBits N)).auxiliarySpace ≤
      (callerContext base N).auxiliarySpace := fun _ => Nat.le_add_left _ _
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · intro axis
    change max (base.auxiliarySpace axis)
      (max ((Slots.acceptedContext base).auxiliarySpace axis) 0) ≤ _
    exact max_le ((first axis).trans ((second axis).trans (third axis)))
      (max_le ((second axis).trans (third axis)) (Nat.zero_le _))
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · intro axis
      change max ((Slots.acceptedContext base).auxiliarySpace axis)
        (max ((Slots.selectedContext base (modulusBits N)).auxiliarySpace axis) 0) ≤ _
      exact max_le ((second axis).trans (third axis)) (max_le (third axis) (Nat.zero_le _))
    · intro axis
      change max ((Slots.selectedContext base (modulusBits N)).auxiliarySpace axis)
        (max ((callerContext base N).auxiliarySpace axis) 0) ≤ _
      exact max_le (third axis) (max_le le_rfl (Nat.zero_le _))

/-- The original bank and all retained results include exactly one persistent selector. -/
theorem nativeOracle_retry_context_auxiliarySpace :
    (context base noQuantum N).auxiliarySpace =
      (Batch.retainedSpace N + selectorSpace N) + base.auxiliarySpace := by
  change (Batch.context (callerContext base N)
    (caller_empty base noQuantum N) N).auxiliarySpace = _
  rw [Batch.nativeOracle_batch_context_auxiliarySpace, slots_auxiliary, add_assoc]

private theorem recovery_auxiliary_allowance :
    Batch.Recovery.additionalSpace N + (callerContext base N).auxiliarySpace =
      additionalSpace N + base.auxiliarySpace := by
  rw [slots_auxiliary]
  exact (add_assoc _ _ _).symm

private theorem caller_auxiliary_allowance :
    (callerContext base N).auxiliarySpace ≤
      additionalSpace N + base.auxiliarySpace := by
  rw [slots_auxiliary]
  intro axis
  change selectorSpace N axis + base.auxiliarySpace axis ≤
    (Batch.Recovery.additionalSpace N axis + selectorSpace N axis) + base.auxiliarySpace axis
  omega

private theorem context_auxiliary_allowance :
    (context base noQuantum N).auxiliarySpace ≤
      additionalSpace N + base.auxiliarySpace := by
  rw [nativeOracle_retry_context_auxiliarySpace]
  intro axis
  change (Batch.retainedSpace N axis + selectorSpace N axis) + base.auxiliarySpace axis ≤
    ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) + selectorSpace N axis) +
      base.auxiliarySpace axis
  omega

private theorem first_auxiliary (input : Input N) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (slots_peak_auxiliary base N path.1).trans (caller_auxiliary_allowance base N)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans (SpacePool.max_le ?_ ?_)
    · exact (Batch.Recovery.nativeOracle_recovery_first_peakAuxiliarySpace_le (callerContext base N)
        (caller_empty base noQuantum N) N input path.2.1).trans_eq
          (recovery_auxiliary_allowance base N)
    · exact (Optional.into_auxiliary_le
        (.storage (factorRef base noQuantum N).toCStorageRef)
        (selectionRefs base noQuantum N) path.2.2).trans
          (context_auxiliary_allowance base noQuantum N)

private theorem next_auxiliary (input : Input N) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (Batch.Recovery.nativeOracle_recovery_next_peakAuxiliarySpace_le (callerContext base N)
      (caller_empty base noQuantum N) N input path.1).trans_eq
        (recovery_auxiliary_allowance base N)
  · exact (Optional.into_auxiliary_le
      (.storage (factorRef base noQuantum N).toCStorageRef)
      (selectionRefs base noQuantum N) path.2).trans
        (context_auxiliary_allowance base noQuantum N)

/-- Every actual retry count shares the same complete auxiliary storage allowance. -/
theorem nativeOracle_retry_peakAuxiliarySpace_le (input : Input N) (laterCount : Nat)
    (path : (code base noQuantum N input laterCount).Path) :
    (code base noQuantum N input laterCount).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  have entry := context_auxiliary_allowance base noQuantum N
  have tail := Circuit.forRange_auxiliary_le laterCount
    (fun _ => next base noQuantum N input) (additionalSpace N + base.auxiliarySpace) entry
    (fun _ => next_auxiliary base noQuantum N input) path.2.1
  have finalPack : (pack base noQuantum N).peakAuxiliarySpace path.2.2 =
      (context base noQuantum N).auxiliarySpace := by
    funext axis
    exact Nat.max_zero _
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le
    (first_auxiliary base noQuantum N input path.1) ?_)
  exact (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans
    (SpacePool.max_le tail (finalPack.trans_le entry))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry
