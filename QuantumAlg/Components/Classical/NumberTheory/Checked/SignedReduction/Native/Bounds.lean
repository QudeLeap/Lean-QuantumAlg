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
def signedReductionEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (signClassificationEvents kind width) +
    ResourcePool.max (ResourcePool.ofList (signedMagnitudeEvents kind width true))
      (ResourcePool.ofList (signedMagnitudeEvents kind width false)) +
    ResourcePool.ofList (reductionEvents kind (signedWidth width) width) +
    ResourcePool.max (ResourcePool.ofList (finalCorrectionEvents kind width true))
      (ResourcePool.ofList (finalCorrectionEvents kind width false))

private theorem bool_pool_le (events : Bool → List (Resource.Event kind)) (selected : Bool) :
    ResourcePool.ofList (events selected) ≤
      ResourcePool.max (ResourcePool.ofList (events true))
        (ResourcePool.ofList (events false)) := by
  cases selected
  · exact ResourcePool.le_max_right _ _
  · exact ResourcePool.le_max_left _ _

/-- Every actual pair of branch selections satisfies the original native syntax envelope. -/
theorem signedReductionEvents_pool_le (magnitude correction : Bool) :
    ResourcePool.ofList (signedReductionEvents kind width magnitude correction) ≤
      signedReductionEnvelope kind width := by
  rw [signedReductionEvents, ResourcePool.ofList_append, ResourcePool.ofList_append,
    ResourcePool.ofList_append]
  have available := add_le_add (le_refl (ResourcePool.ofList (signClassificationEvents kind width)))
    (add_le_add (bool_pool_le (signedMagnitudeEvents kind width) magnitude)
      (add_le_add (le_refl (ResourcePool.ofList (reductionEvents kind (signedWidth width) width)))
        (bool_pool_le (finalCorrectionEvents kind width) correction)))
  simpa only [signedReductionEnvelope, add_assoc] using available

/-- The original envelope bounds the counts of the same actual signed-reduction circuit. -/
theorem withSignedReduction_pool_le (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction raw modulus output).Path) :
    (withSignedReduction raw modulus output).resourcePool path ≤
      signedReductionEnvelope kind width := by
  rw [withSignedReduction_resourcePool]
  exact signedReductionEvents_pool_le _ _

/-- Original serial duration allowance uses the same independent branch maxima. -/
def signedReductionDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  ((signClassificationEvents kind width).map duration).sum +
    max ((signedMagnitudeEvents kind width true).map duration).sum
      ((signedMagnitudeEvents kind width false).map duration).sum +
    ((reductionEvents kind (signedWidth width) width).map duration).sum +
    max ((finalCorrectionEvents kind width true).map duration).sum
      ((finalCorrectionEvents kind width false).map duration).sum

private theorem bool_duration_le (events : Bool → List (Resource.Event kind))
    (duration : Resource.Event kind → Nat) (selected : Bool) :
    ((events selected).map duration).sum ≤
      max ((events true).map duration).sum ((events false).map duration).sum := by
  cases selected
  · exact Nat.le_max_right _ _
  · exact Nat.le_max_left _ _

/-- Actual branch durations are bounded by the original independent phase maxima. -/
theorem signedReductionEvents_depth_le (duration : Resource.Event kind → Nat)
    (magnitude correction : Bool) :
    ((signedReductionEvents kind width magnitude correction).map duration).sum ≤
      signedReductionDepthLimit width duration := by
  rw [signedReductionEvents, List.map_append, List.sum_append, List.map_append,
    List.sum_append, List.map_append, List.sum_append]
  have available := Nat.add_le_add
    (le_refl (((signClassificationEvents kind width).map duration).sum))
    (Nat.add_le_add (bool_duration_le (signedMagnitudeEvents kind width) duration magnitude)
      (Nat.add_le_add
        (le_refl (((reductionEvents kind (signedWidth width) width).map duration).sum))
        (bool_duration_le (finalCorrectionEvents kind width) duration correction)))
  simpa only [signedReductionDepthLimit, Nat.add_assoc] using available

/-- The original native-duration allowance applies to every actual complete selected path. -/
theorem withSignedReduction_depth_le (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (withSignedReduction raw modulus output).Path) :
    (withSignedReduction raw modulus output).depth duration path ≤
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
theorem withSignedReduction_resident_le (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction raw modulus output).Path) :
    (withSignedReduction raw modulus output).peakResidentSpace path ≤
      signedReductionSpaceLimit kind width + ctx.residentSpace := by
  rw [withSignedReduction_resident]
  exact add_le_add (signedReductionScratchSpace_le _) le_rfl

/-- Auxiliary ownership retains the same actual complete context and original scratch allowance. -/
theorem withSignedReduction_auxiliary_le (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (withSignedReduction raw modulus output).Path) :
    (withSignedReduction raw modulus output).peakAuxiliarySpace path ≤
      signedReductionSpaceLimit kind width + ctx.auxiliarySpace := by
  rw [withSignedReduction_auxiliary]
  exact add_le_add (signedReductionScratchSpace_le _) le_rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
