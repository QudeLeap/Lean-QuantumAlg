/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Actual resources of recovery from a retained sample batch

Every attempt is charged together with its original first-accepted selector,
including attempts after an earlier success. One final pack follows the loop.
The original raw dependency bound is preserved for arbitrary event durations.
Four selector cells stay live throughout; the maximum single-attempt scratch
is reused and is not multiplied by the sample count. All bounds include the
complete caller context, including its already retained samples and target.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum}

/-- The original selector has two unconditional operations and two possible copies. -/
def selectionDepthLimit (width : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  duration (.classicalOperation (.bit .not)) + duration (.classicalOperation (.bit .and)) +
    (duration (.classicalOperation (.wordUnary .copy width)) +
      duration (.classicalOperation (.bit .copy)))

private theorem selector_depth {width : Nat} (inputs : FirstAccepted.Inputs ctx width)
    (refs : FirstAccepted.Refs ctx width) (duration : Resource.Event .quantum → Nat)
    (path : (FirstAccepted.circuit inputs refs).Path) :
    (FirstAccepted.circuit inputs refs).depth duration path ≤
      selectionDepthLimit width duration := by
  rw [FirstAccepted.firstAccepted_depth]
  unfold selectionDepthLimit
  apply Nat.add_le_add_left
  split <;> omega

/-- Independent events of every complete attempt and selector, followed by one actual pack. -/
def recoveryEnvelope (P : Parameters G) (count : Nat) : ResourcePool .quantum :=
  ResourcePool.scale count (attemptEnvelope P + FirstAccepted.nativeEnvelope .quantum P.width) +
    ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packOption P.width)))

/-- The same complete serial tail preserves the original per-attempt dependency allowance. -/
def recoveryDepthLimit (P : Parameters G) (count : Nat)
    (duration : Resource.Event .quantum → Nat) : Nat :=
  count * (attemptDepthLimit P duration + selectionDepthLimit P.width duration) +
    duration (.classicalOperation (.nominalEncoding (.packOption P.width)))

/-- The maximum extra live storage of a single attempt is reused across all samples. -/
def selectionAttemptSpace (P : Parameters G) : SpacePool .quantum :=
  ((attemptShapes P.width).map SpacePool.ofShape).sum + attemptActiveSpace P 0

/-- Four persistent selector cells enclose one reused maximum attempt workspace. -/
def recoveryScratchSpace (P : Parameters G) : SpacePool .quantum :=
  ((selectorShapes P.width).map SpacePool.ofShape).sum + selectionAttemptSpace P

private theorem attempt_pool (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (path : (selectAttempt P input target refs).Path) :
    (selectAttempt P input target refs).resourcePool path ≤
      attemptEnvelope P + FirstAccepted.nativeEnvelope .quantum P.width :=
  withAttempt_pool_le P input target _ (FirstAccepted.nativeEnvelope .quantum P.width)
    (fun candidate accepted transport =>
      FirstAccepted.firstAccepted_pool_le ⟨accepted, candidate⟩ (liftSelector refs transport)) path

private theorem attempt_depth (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (duration : Resource.Event .quantum → Nat) (path : (selectAttempt P input target refs).Path) :
    (selectAttempt P input target refs).depth duration path ≤
      attemptDepthLimit P duration + selectionDepthLimit P.width duration :=
  withAttempt_depth_le P input target _ duration (selectionDepthLimit P.width duration)
    (fun candidate accepted transport => selector_depth ⟨accepted, candidate⟩
      (liftSelector refs transport) duration) path

private theorem attempt_resident (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (path : (selectAttempt P input target refs).Path) :
    (selectAttempt P input target refs).peakResidentSpace path ≤
      selectionAttemptSpace P + ctx.residentSpace :=
  withAttempt_resident_le P input target _ 0 (by
    intro inner candidate accepted transport selected
    simpa only [zero_add] using FirstAccepted.firstAccepted_resident_le
      ⟨accepted, candidate⟩ (liftSelector refs transport) selected) path

private theorem attempt_auxiliary (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (path : (selectAttempt P input target refs).Path) :
    (selectAttempt P input target refs).peakAuxiliarySpace path ≤
      selectionAttemptSpace P + ctx.auxiliarySpace :=
  withAttempt_auxiliary_le P input target _ 0 (by
    intro inner candidate accepted transport selected
    simpa only [zero_add] using FirstAccepted.firstAccepted_auxiliary_le
      ⟨accepted, candidate⟩ (liftSelector refs transport) selected) path

variable (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (output : CWriteRef ctx (.option (.unsignedWord P.width)))

/-- The actual trace is the complete attempt loop followed by the one original pack event. -/
theorem groupRecoveryBody_eventTrace
    (path : (recoveryBody P count samples target refs output).Path) :
    (recoveryBody P count samples target refs output).eventTrace path =
      (selectionLoop P count samples target refs).eventTrace path.1 ++
        [.classicalOperation (.nominalEncoding (.packOption P.width))] := rfl

/-- The actual loop and final pack meet the independent coordinate allowance. -/
theorem groupRecoveryBody_pool_le (path : (recoveryBody P count samples target refs output).Path) :
    (recoveryBody P count samples target refs output).resourcePool path ≤
      recoveryEnvelope P count := by
  rw [Circuit.resourcePool, groupRecoveryBody_eventTrace, ResourcePool.ofList_append]
  exact add_le_add (Circuit.forRange_pool_le count _ _
    (fun index => attempt_pool P (samples index) target refs) path.1) le_rfl

/-- Arbitrary durations charge every actual attempt before the same final packing dependency. -/
theorem groupRecoveryBody_depth_le (duration : Resource.Event .quantum → Nat)
    (path : (recoveryBody P count samples target refs output).Path) :
    (recoveryBody P count samples target refs output).depth duration path ≤
      recoveryDepthLimit P count duration := by
  have loopBound := Circuit.forRange_depth_le_sum count
    (fun index => selectAttempt P (samples index) target refs) duration
    (fun _ => attemptDepthLimit P duration + selectionDepthLimit P.width duration)
    (fun index => attempt_depth P (samples index) target refs duration) path.1
  have loop : (selectionLoop P count samples target refs).depth duration path.1 ≤
      count * (attemptDepthLimit P duration + selectionDepthLimit P.width duration) := by
    simpa only [selectionLoop, Finset.sum_const, Finset.card_fin, smul_eq_mul] using loopBound
  exact Nat.add_le_add loop le_rfl

private theorem pack_resident {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (Circuit.classical (selectionPack refs output)).Path) :
    (Circuit.classical (selectionPack refs output)).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited member
  have same : visited = ctx := List.mem_singleton.mp member
  simpa only [same] using (le_refl ctx.residentSpace)

private theorem pack_auxiliary {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (Circuit.classical (selectionPack refs output)).Path) :
    (Circuit.classical (selectionPack refs output)).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited member
  have same : visited = ctx := List.mem_singleton.mp member
  simpa only [same] using (le_refl ctx.auxiliarySpace)

/-- The actual resident peak reuses one attempt workspace and includes the whole caller. -/
theorem groupRecoveryBody_resident_le
    (path : (recoveryBody P count samples target refs output).Path) :
    (recoveryBody P count samples target refs output).peakResidentSpace path ≤
      selectionAttemptSpace P + ctx.residentSpace := by
  dsimp only [recoveryBody] at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le
    (Circuit.forRange_resident_le count _ _ (le_add_of_nonneg_left zero_le)
      (fun index => attempt_resident P (samples index) target refs) path.1)
    ((pack_resident refs output path.2).trans (le_add_of_nonneg_left zero_le))

/-- The actual auxiliary peak reuses one attempt workspace and includes all caller roles. -/
theorem groupRecoveryBody_auxiliary_le
    (path : (recoveryBody P count samples target refs output).Path) :
    (recoveryBody P count samples target refs output).peakAuxiliarySpace path ≤
      selectionAttemptSpace P + ctx.auxiliarySpace := by
  dsimp only [recoveryBody] at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le
    (Circuit.forRange_auxiliary_le count _ _ (le_add_of_nonneg_left zero_le)
      (fun index => attempt_auxiliary P (samples index) target refs) path.1)
    ((pack_auxiliary refs output path.2).trans (le_add_of_nonneg_left zero_le))

omit refs in
/-- Four actual initializations and releases preserve the same independent event allowance. -/
theorem groupRecoveryInto_pool_le (path : (recoveryInto P count samples target output).Path) :
    (recoveryInto P count samples target output).resourcePool path ≤ recoveryEnvelope P count := by
  apply withCellsFrom_pool_le
  intro inner cells distinct transport separated selected
  exact groupRecoveryBody_pool_le P count (fun index => transport.liftInput (samples index))
    (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output) selected

omit refs in
/-- The original per-attempt duration allowance survives the real four-cell scope. -/
theorem groupRecoveryInto_depth_le (duration : Resource.Event .quantum → Nat)
    (path : (recoveryInto P count samples target output).Path) :
    (recoveryInto P count samples target output).depth duration path ≤
      recoveryDepthLimit P count duration := by
  apply withCellsFrom_depth_le
  intro inner cells distinct transport separated selected
  exact groupRecoveryBody_depth_le P count (fun index => transport.liftInput (samples index))
    (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output) duration selected

omit refs in
/-- Unit durations specialize the very same actual path and independent depth allowance. -/
theorem groupRecoveryInto_unit_depth_le (path : (recoveryInto P count samples target output).Path) :
    (recoveryInto P count samples target output).depth (fun _ => 1) path ≤
      count * (attemptDepthLimit P (fun _ => 1) + 4) + 1 :=
  groupRecoveryInto_depth_le P count samples target output (fun _ => 1) path

omit refs in
/-- Four once-allocated selector cells enclose one reused resident attempt maximum. -/
theorem groupRecoveryInto_resident_le (path : (recoveryInto P count samples target output).Path) :
    (recoveryInto P count samples target output).peakResidentSpace path ≤
      recoveryScratchSpace P + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (selectorShapes P.width)
    (fun cells _ transport _ =>
      recoveryBody P count (fun index => transport.liftInput (samples index))
        (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output))
    (selectionAttemptSpace P) (by
      intro inner cells distinct transport separated selected
      exact groupRecoveryBody_resident_le P count
        (fun index => transport.liftInput (samples index))
        (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output) selected)
    path

omit refs in
/-- The same fixed selector scope and one reused attempt maximum bound auxiliary storage. -/
theorem groupRecoveryInto_auxiliary_le (path : (recoveryInto P count samples target output).Path) :
    (recoveryInto P count samples target output).peakAuxiliarySpace path ≤
      recoveryScratchSpace P + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (selectorShapes P.width)
    (fun cells _ transport _ =>
      recoveryBody P count (fun index => transport.liftInput (samples index))
        (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output))
    (selectionAttemptSpace P) (by
      intro inner cells distinct transport separated selected
      exact groupRecoveryBody_auxiliary_le P count
        (fun index => transport.liftInput (samples index))
        (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output) selected)
    path

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
