/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Resources

/-!
# Original uniform bounds for actual signed reduction

The independent envelope retains the original syntax maximum at each of the
two branch sites. Actual native counts, durations and complete live-space
peaks satisfy these bounds. The execution-dependent equalities remain in the
resource owner; no worst-case bound is promoted to an exact execution cost.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution Modular.Reduce.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original phase-wise syntax envelope, with an independent maximum at each branch site. -/
def signedReductionEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
  ResourcePool model :=
  ResourcePool.ofList (signClassificationEvents model width) +
    ResourcePool.max (ResourcePool.ofList (signedMagnitudeEvents model width true))
      (ResourcePool.ofList (signedMagnitudeEvents model width false)) +
    ResourcePool.ofList (reductionEvents model (signedWidth width) width) +
    ResourcePool.max (ResourcePool.ofList (finalCorrectionEvents model width true))
      (ResourcePool.ofList (finalCorrectionEvents model width false))

private theorem bool_pool_le {model : ExecutionModel} (events : Bool → List (Resource.Event
  model)) (selected : Bool) :
    ResourcePool.ofList (events selected) ≤
      ResourcePool.max (ResourcePool.ofList (events true))
        (ResourcePool.ofList (events false)) := by
  cases selected
  · exact ResourcePool.le_max_right _ _
  · exact ResourcePool.le_max_left _ _

/-- Every actual pair of branch selections satisfies the original native syntax envelope. -/
theorem signedReductionEvents_pool_le {model : ExecutionModel} [BitWord.Selected model]
  (magnitude correction : Bool) :
    ResourcePool.ofList (signedReductionEvents model width magnitude correction) ≤
      signedReductionEnvelope model width := by
  rw [signedReductionEvents, ResourcePool.ofList_append, ResourcePool.ofList_append,
    ResourcePool.ofList_append]
  have available := add_le_add (le_refl (ResourcePool.ofList (signClassificationEvents model
    width)))
    (add_le_add (bool_pool_le (signedMagnitudeEvents model width) magnitude)
      (add_le_add (le_refl (ResourcePool.ofList (reductionEvents model (signedWidth width) width)))
        (bool_pool_le (finalCorrectionEvents model width) correction)))
  simpa only [signedReductionEnvelope, add_assoc] using available

/-- The original envelope bounds the counts of the same actual signed-reduction circuit. -/
theorem withSignedReduction_pool_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).resourcePool path ≤
      signedReductionEnvelope model width := by
  rw [withSignedReduction_resourcePool]
  exact signedReductionEvents_pool_le _ _

/-- Original serial duration allowance uses the same independent branch maxima. -/
def signedReductionDepthLimit {model : ExecutionModel} [BitWord.Selected model] (width : Nat)
  (duration : Resource.Event model → Nat) : Nat :=
  ((signClassificationEvents model width).map duration).sum +
    max ((signedMagnitudeEvents model width true).map duration).sum
      ((signedMagnitudeEvents model width false).map duration).sum +
    ((reductionEvents model (signedWidth width) width).map duration).sum +
    max ((finalCorrectionEvents model width true).map duration).sum
      ((finalCorrectionEvents model width false).map duration).sum

private theorem bool_duration_le {model : ExecutionModel} (events : Bool → List (Resource.Event
  model))
    (duration : Resource.Event model → Nat) (selected : Bool) :
    ((events selected).map duration).sum ≤
      max ((events true).map duration).sum ((events false).map duration).sum := by
  cases selected
  · exact Nat.le_max_right _ _
  · exact Nat.le_max_left _ _

/-- Actual branch durations are bounded by the original independent phase maxima. -/
theorem signedReductionEvents_depth_le {model : ExecutionModel} [BitWord.Selected model]
  (duration : Resource.Event model → Nat)
    (magnitude correction : Bool) :
    ((signedReductionEvents model width magnitude correction).map duration).sum ≤
      signedReductionDepthLimit width duration := by
  rw [signedReductionEvents, List.map_append, List.sum_append, List.map_append,
    List.sum_append, List.map_append, List.sum_append]
  have available := Nat.add_le_add
    (le_refl (((signClassificationEvents model width).map duration).sum))
    (Nat.add_le_add (bool_duration_le (signedMagnitudeEvents model width) duration magnitude)
      (Nat.add_le_add
        (le_refl (((reductionEvents model (signedWidth width) width).map duration).sum))
        (bool_duration_le (finalCorrectionEvents model width) duration correction)))
  simpa only [signedReductionDepthLimit, Nat.add_assoc] using available

/-- The original native-duration allowance applies to every actual complete selected path. -/
theorem withSignedReduction_depth_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).depth duration path ≤
      signedReductionDepthLimit width duration := by
  rw [withSignedReduction_durationDepth]
  exact signedReductionEvents_depth_le duration _ _

/-- The original uniform scratch allowance includes the complete correction branch capacity. -/
def signedReductionSpaceLimit (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  signedReductionScratchSpace width true

/-- Every actual selected scratch peak is bounded by the original full correction capacity. -/
theorem signedReductionScratchSpace_le (selected : Bool) :
    (signedReductionScratchSpace width selected : SpacePool kind) ≤
      signedReductionSpaceLimit kind width := by
  cases selected
  · intro axis
    change max _ 0 + _ + _ + _ ≤ max _ _ + _ + _ + _
    omega
  · exact le_rfl

/-- Every resident peak includes the entire caller context and original uniform scratch bound. -/
theorem withSignedReduction_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).peakResidentSpace path ≤
      signedReductionSpaceLimit model.kind width + ctx.residentSpace := by
  rw [withSignedReduction_resident]
  exact add_le_add (signedReductionScratchSpace_le _) le_rfl

/-- Auxiliary ownership retains the same actual complete context and original scratch allowance. -/
theorem withSignedReduction_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction (model := model) raw modulus output).Path) :
    (withSignedReduction (model := model) raw modulus output).peakAuxiliarySpace path ≤
      signedReductionSpaceLimit model.kind width + ctx.auxiliarySpace := by
  rw [withSignedReduction_auxiliary]
  exact add_le_add (signedReductionScratchSpace_le _) le_rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
