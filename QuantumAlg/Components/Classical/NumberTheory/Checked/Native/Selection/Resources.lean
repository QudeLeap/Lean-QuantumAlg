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
def checkedDecisionEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal (width + 1)))]

/-- Original syntax allowance includes signed reduction on the successful branch only. -/
def checkedSelectionEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
  ResourcePool model :=
  ResourcePool.ofList (checkedDecisionEvents model width) +
    ResourcePool.max (signedReductionEnvelope model width) 0

/-- Original serial decision duration followed by the selected signed-arithmetic allowance. -/
def checkedSelectionDepthLimit {model : ExecutionModel} [BitWord.Selected model] (width : Nat)
  (duration : Resource.Event model → Nat) : Nat :=
  ((checkedDecisionEvents model width).map duration).sum + signedReductionDepthLimit width duration

/-- The original decision-one and signed scopes have successive, nonoverlapping lifetimes. -/
def checkedSelectionSpaceLimit (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (SpacePool.ofShape (.unsignedWord (width + 1)))
    (signedReductionSpaceLimit kind width)

private theorem checked_choice_pool_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (path : (checkedCoefficientChoice (model := model) raw modulus inverse value).Path) :
    (checkedCoefficientChoice (model := model) raw modulus inverse value).resourcePool path ≤
      ResourcePool.max (signedReductionEnvelope model width) 0 := by
  cases value with
  | bit value =>
      cases value
      · exact ResourcePool.le_max_right _ _
      · exact (withSignedReduction_pool_le raw modulus inverse path).trans
          (ResourcePool.le_max_left _ _)

/-- The real stored-status branch satisfies the original independent syntax allowance. -/
theorem checkedCoefficientSelection_pool_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).resourcePool
      path ≤
      checkedSelectionEnvelope model width := by
  change ResourcePool.ofList ((withUnitDecision (model := model) gcd success).eventTrace path.1 ++
    (checkedCoefficientChoice (model := model) raw modulus inverse path.2.1).eventTrace path.2.2)
      ≤ _
  rw [withUnitDecision_eventTrace, ResourcePool.ofList_append]
  exact add_le_add le_rfl (checked_choice_pool_le raw modulus inverse path.2.1 path.2.2)

private theorem checked_choice_duration_trace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (duration : Resource.Event model → Nat)
    (path : (checkedCoefficientChoice (model := model) raw modulus inverse value).Path) :
    (checkedCoefficientChoice (model := model) raw modulus inverse value).depth duration path =
      (((checkedCoefficientChoice (model := model) raw modulus inverse value).eventTrace path).map
        duration).sum := by
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact (withSignedReduction_durationDepth raw modulus inverse duration path).trans
          (congrArg (fun events => (events.map duration).sum)
            (withSignedReduction_eventTrace raw modulus inverse path)).symm

/-- Every actual selected branch has exactly the serial duration of its own emitted events. -/
theorem checkedCoefficientSelection_duration_eventTrace {model : ExecutionModel}
  [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).depth duration
      path =
      (((checkedCoefficientSelection (model := model) gcd raw modulus success inverse).eventTrace
        path).map
        duration).sum := by
  have selected := checked_choice_duration_trace raw modulus inverse path.2.1 duration path.2.2
  change (withUnitDecision (model := model) gcd success).depth duration path.1 +
    (checkedCoefficientChoice (model := model) raw modulus inverse path.2.1).depth duration
      path.2.2 =
      (((withUnitDecision (model := model) gcd success).eventTrace path.1 ++
        (checkedCoefficientChoice (model := model) raw modulus inverse path.2.1).eventTrace
          path.2.2).map
          duration).sum
  rw [withUnitDecision_durationDepth, withUnitDecision_eventTrace, selected]
  simp only [List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The actual decision and selected reduction satisfy the original serial duration allowance. -/
theorem checkedCoefficientSelection_depth_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).depth duration
      path ≤
      checkedSelectionDepthLimit width duration := by
  have selected : (checkedCoefficientChoice (model := model) raw modulus inverse path.2.1).depth
      duration path.2.2 ≤ signedReductionDepthLimit width duration := by
    rcases path.2 with ⟨value, branch⟩
    cases value with
    | bit value =>
        cases value
        · exact Nat.zero_le _
        · exact withSignedReduction_depth_le raw modulus inverse duration branch
  change (withUnitDecision (model := model) gcd success).depth duration path.1 +
    (checkedCoefficientChoice (model := model) raw modulus inverse path.2.1).depth
      duration path.2.2 ≤ checkedSelectionDepthLimit width duration
  rw [withUnitDecision_durationDepth]
  simpa only [checkedSelectionDepthLimit, checkedDecisionEvents, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using
      Nat.add_le_add_left selected
        (((checkedDecisionEvents model width).map duration).sum)

private theorem checked_choice_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (path : (checkedCoefficientChoice (model := model) raw modulus inverse value).Path) :
    (checkedCoefficientChoice (model := model) raw modulus inverse value).peakResidentSpace path ≤
      checkedSelectionSpaceLimit model.kind width + ctx.residentSpace := by
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.residentSpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact le_add_self
      · exact (withSignedReduction_resident_le raw modulus inverse path).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The real decision-one scope is released before the signed resident workspace is allocated. -/
theorem checkedCoefficientSelection_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection (model := model) gcd raw modulus success
      inverse).peakResidentSpace path ≤
      checkedSelectionSpaceLimit model.kind width + ctx.residentSpace := by
  refine (le_of_eq (Circuit.peakResidentSpace_seq (withUnitDecision (model := model) gcd success)
    (.branch (decisionRead success) (checkedCoefficientChoice (model := model) raw modulus
      inverse)) path)).trans ?_
  apply SpacePool.max_le
  · exact (le_of_eq (withUnitDecision_resident gcd success path.1)).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact checked_choice_resident_le raw modulus inverse path.2.1 path.2.2

private theorem checked_choice_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (path : (checkedCoefficientChoice (model := model) raw modulus inverse value).Path) :
    (checkedCoefficientChoice (model := model) raw modulus inverse value).peakAuxiliarySpace path ≤
      checkedSelectionSpaceLimit model.kind width + ctx.auxiliarySpace := by
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.auxiliarySpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact le_add_self
      · exact (withSignedReduction_auxiliary_le raw modulus inverse path).trans
          (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The corresponding auxiliary bound counts both real sequential workspace lifetimes. -/
theorem checkedCoefficientSelection_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (path : (checkedCoefficientSelection (model := model) gcd raw modulus success inverse).Path) :
    (checkedCoefficientSelection (model := model) gcd raw modulus success
      inverse).peakAuxiliarySpace path ≤
      checkedSelectionSpaceLimit model.kind width + ctx.auxiliarySpace := by
  refine (le_of_eq (Circuit.peakAuxiliarySpace_seq (withUnitDecision (model := model) gcd success)
    (.branch (decisionRead success) (checkedCoefficientChoice (model := model) raw modulus
      inverse)) path)).trans ?_
  apply SpacePool.max_le
  · exact (le_of_eq (withUnitDecision_auxiliary gcd success path.1)).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact checked_choice_auxiliary_le raw modulus inverse path.2.1 path.2.2

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
