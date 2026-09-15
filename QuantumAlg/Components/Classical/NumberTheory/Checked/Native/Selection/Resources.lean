/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Selection
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Bounds

/-!
# Actual gcd decision and selected signed-reduction resources

The original increment and equality always execute. Signed arithmetic runs
only on the actual successful branch. Its independent syntax envelope is
retained, while each selected path has exactly its own serial event duration.
The comparison-one scope is released before any signed workspace is allocated.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution SignedReduction SignedReduction.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original widened-one increment and stored gcd comparison, in their actual order. -/
def checkedDecisionEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .increment (width + 1)),
    .classicalOperation (.wordBinary .equal (width + 1))]

/-- Original syntax allowance includes signed reduction on the successful branch only. -/
def checkedSelectionEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (checkedDecisionEvents kind width) +
    ResourcePool.max (signedReductionEnvelope kind width) 0

/-- Original serial decision duration followed by the selected signed-arithmetic allowance. -/
def checkedSelectionDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  ((checkedDecisionEvents kind width).map duration).sum + signedReductionDepthLimit width duration

/-- The original decision-one and signed scopes have successive, nonoverlapping lifetimes. -/
def checkedSelectionSpaceLimit (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (SpacePool.ofShape (.unsignedWord (width + 1)))
    (signedReductionSpaceLimit kind width)

private theorem checked_choice_pool_le
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (path : (checkedCoefficientChoice raw modulus inverse value).Path) :
    (checkedCoefficientChoice raw modulus inverse value).resourcePool path ≤
      ResourcePool.max (signedReductionEnvelope kind width) 0 := by
  cases value with
  | bit value =>
      cases value
      · exact ResourcePool.le_max_right _ _
      · exact (withSignedReduction_pool_le raw modulus inverse path).trans
          (ResourcePool.le_max_left _ _)

/-- The real stored-status branch satisfies the original independent syntax allowance. -/
theorem checkedCoefficientSelection_pool_le
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedCoefficientSelection gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection gcd raw modulus success inverse).resourcePool path ≤
      checkedSelectionEnvelope kind width := by
  change ResourcePool.ofList (checkedDecisionEvents kind width ++
    (checkedCoefficientChoice raw modulus inverse path.2.1).eventTrace path.2.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add le_rfl (checked_choice_pool_le raw modulus inverse path.2.1 path.2.2)

private theorem checked_choice_duration_trace
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (duration : Resource.Event kind → Nat)
    (path : (checkedCoefficientChoice raw modulus inverse value).Path) :
    (checkedCoefficientChoice raw modulus inverse value).depth duration path =
      (((checkedCoefficientChoice raw modulus inverse value).eventTrace path).map
        duration).sum := by
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact (withSignedReduction_durationDepth raw modulus inverse duration path).trans
          (congrArg (fun events => (events.map duration).sum)
            (withSignedReduction_eventTrace raw modulus inverse path)).symm

/-- Every actual selected branch has exactly the serial duration of its own emitted events. -/
theorem checkedCoefficientSelection_duration_eventTrace
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event kind → Nat)
    (path : (checkedCoefficientSelection gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection gcd raw modulus success inverse).depth duration path =
      (((checkedCoefficientSelection gcd raw modulus success inverse).eventTrace path).map
        duration).sum := by
  have selected := checked_choice_duration_trace raw modulus inverse path.2.1 duration path.2.2
  change (withUnitDecision gcd success).depth duration path.1 +
    (checkedCoefficientChoice raw modulus inverse path.2.1).depth duration path.2.2 =
      ((checkedDecisionEvents kind width ++
        (checkedCoefficientChoice raw modulus inverse path.2.1).eventTrace path.2.2).map
          duration).sum
  rw [withUnitDecision_durationDepth, selected]
  simp only [checkedDecisionEvents, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The actual decision and selected reduction satisfy the original serial duration allowance. -/
theorem checkedCoefficientSelection_depth_le
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event kind → Nat)
    (path : (checkedCoefficientSelection gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection gcd raw modulus success inverse).depth duration path ≤
      checkedSelectionDepthLimit width duration := by
  have selected : (checkedCoefficientChoice raw modulus inverse path.2.1).depth
      duration path.2.2 ≤ signedReductionDepthLimit width duration := by
    rcases path.2 with ⟨value, branch⟩
    cases value with
    | bit value =>
        cases value
        · exact Nat.zero_le _
        · exact withSignedReduction_depth_le raw modulus inverse duration branch
  change (withUnitDecision gcd success).depth duration path.1 + _ ≤ _
  exact Nat.add_le_add_left selected _

private theorem checked_choice_resident_le
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (path : (checkedCoefficientChoice raw modulus inverse value).Path) :
    (checkedCoefficientChoice raw modulus inverse value).peakResidentSpace path ≤
      checkedSelectionSpaceLimit kind width + ctx.residentSpace := by
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.residentSpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact le_add_self
      · exact (withSignedReduction_resident_le raw modulus inverse path).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The real decision-one scope is released before the signed resident workspace is allocated. -/
theorem checkedCoefficientSelection_resident_le
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedCoefficientSelection gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection gcd raw modulus success inverse).peakResidentSpace path ≤
      checkedSelectionSpaceLimit kind width + ctx.residentSpace := by
  refine (le_of_eq (Circuit.peakResidentSpace_seq (withUnitDecision gcd success)
    (.branch (decisionRead success) (checkedCoefficientChoice raw modulus inverse)) path)).trans ?_
  apply SpacePool.max_le
  · exact (le_of_eq (withUnitDecision_resident gcd success path.1)).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact checked_choice_resident_le raw modulus inverse path.2.1 path.2.2

private theorem checked_choice_auxiliary_le
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (path : (checkedCoefficientChoice raw modulus inverse value).Path) :
    (checkedCoefficientChoice raw modulus inverse value).peakAuxiliarySpace path ≤
      checkedSelectionSpaceLimit kind width + ctx.auxiliarySpace := by
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.auxiliarySpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact le_add_self
      · exact (withSignedReduction_auxiliary_le raw modulus inverse path).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The corresponding auxiliary bound counts both real sequential workspace lifetimes. -/
theorem checkedCoefficientSelection_auxiliary_le
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedCoefficientSelection gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection gcd raw modulus success inverse).peakAuxiliarySpace path ≤
      checkedSelectionSpaceLimit kind width + ctx.auxiliarySpace := by
  refine (le_of_eq (Circuit.peakAuxiliarySpace_seq (withUnitDecision gcd success)
    (.branch (decisionRead success) (checkedCoefficientChoice raw modulus inverse)) path)).trans ?_
  apply SpacePool.max_le
  · exact (le_of_eq (withUnitDecision_auxiliary gcd success path.1)).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact checked_choice_auxiliary_le raw modulus inverse path.2.1 path.2.2

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
