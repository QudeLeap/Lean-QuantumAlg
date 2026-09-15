/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Narrow
import all QuantumAlg.Components.Classical.FirstAccepted.Resources

/-!
# Actual native costs and storage of narrowing into persistent selection

One real width conversion precedes the existing selector's two decision
instructions and possible two copies. The independent allowance has five
native events; the actual path has three or five. One real output-width
classical word is the only additional live storage, and its scope returns
the original physical quantum layout without adding any quantum system.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- Independent native allowance for actual conversion and the complete possible copy arm. -/
def nativeEnvelope (kind : ProblemKind) (sourceWidth width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordResize sourceWidth width)) +
    FirstAccepted.nativeEnvelope kind width

/-- The true trace records one resize and exactly the actual stored selection branch. -/
theorem nativeQuadratic_narrow_eventTrace (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (path : (code eligible candidate original).Path) :
    (code eligible candidate original).eventTrace path =
      [.classicalOperation (.wordResize sourceWidth width)] ++
        (FirstAccepted.circuit (inputs eligible width) (refs original)).eventTrace path.2 := rfl

/-- All actual native coordinates fit the independent five-event allowance. -/
theorem nativeQuadratic_narrow_pool_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (path : (code eligible candidate original).Path) :
    (code eligible candidate original).resourcePool path ≤
      nativeEnvelope kind sourceWidth width := by
  rw [Circuit.resourcePool, nativeQuadratic_narrow_eventTrace, ResourcePool.ofList_append]
  exact add_le_add le_rfl (FirstAccepted.firstAccepted_pool_le _ _ path.2)

/-- The independent native budget has five entries, including both possible copies. -/
theorem nativeQuadratic_narrow_nativeEnvelope_card (kind : ProblemKind) (sourceWidth width : Nat) :
    (nativeEnvelope kind sourceWidth width).card = 5 := rfl

/-- The actual event total is three or five according to the real selector branch. -/
theorem nativeQuadratic_narrow_eventCount (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (path : (code eligible candidate original).Path) :
    ((code eligible candidate original).resourcePool path).card =
      if path.2.2.1.toBool then 5 else 3 := by
  let selected : (FirstAccepted.circuit (inputs eligible width) (refs original)).Path := path.2
  have actual := congrArg
    (fun events : List (Resource.Event kind) =>
      ([Resource.Event.classicalOperation (.wordResize sourceWidth width)] ++ events).length)
    (FirstAccepted.firstAccepted_eventTrace (inputs eligible width) (refs original) selected)
  have count (taken : Bool) :
      ([Resource.Event.classicalOperation (.wordResize sourceWidth width)] ++
        (FirstAccepted.decisionEvents kind ++
          (if taken then FirstAccepted.copyEvents kind width else []))).length =
        if taken then 5 else 3 := by
    cases taken <;> rfl
  exact actual.trans (count selected.2.1.toBool)

/-- Serial unit-duration depth counts the same actual conversion and selected instructions. -/
theorem nativeQuadratic_narrow_unitDepth (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (path : (code eligible candidate original).Path) :
    (code eligible candidate original).depth (fun _ => 1) path =
      if path.2.2.1.toBool then 5 else 3 := by
  let selected : (FirstAccepted.circuit (inputs eligible width) (refs original)).Path := path.2
  have actual := congrArg (fun depth : Nat => 1 + depth)
    (FirstAccepted.firstAccepted_unit_depth (inputs eligible width) (refs original) selected)
  have count (taken : Bool) : 1 + (if taken then 4 else 2) = (if taken then 5 else 3) := by
    cases taken <;> rfl
  exact actual.trans (count selected.2.1.toBool)

/-- Every actual visited context is either the caller or its one-word lexical extension. -/
theorem nativeQuadratic_narrow_visited (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (path : (code eligible candidate original).Path) :
    ∀ visited ∈ (code eligible candidate original).visitedContexts path,
      visited = ctx ∨ visited = context ctx width := by
  intro visited present
  change visited ∈ ctx :: ([context ctx width] ++
    (FirstAccepted.circuit (inputs eligible width) (refs original)).visitedContexts path.2) ++
      [ctx] at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with (same | same | selector) | same
  · exact Or.inl same
  · exact Or.inr same
  · exact Or.inr (FirstAccepted.firstAccepted_visited _ _ path.2 visited selector)
  · exact Or.inl same

/-- Resident and auxiliary peaks are bounded by the caller plus the real extra classical word. -/
theorem nativeQuadratic_narrow_space_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (path : (code eligible candidate original).Path) :
    (code eligible candidate original).peakResidentSpace path ≤
        SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace ∧
      (code eligible candidate original).peakAuxiliarySpace path ≤
        SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace := by
  have residentCaller : ctx.residentSpace ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace := by
    intro axis
    change ctx.residentSpace axis ≤
      SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis
    omega
  have auxiliaryCaller : ctx.auxiliarySpace ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace := by
    intro axis
    change ctx.auxiliarySpace axis ≤
      SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis
    omega
  constructor
  · apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rcases nativeQuadratic_narrow_visited eligible candidate original path visited present with
      rfl | rfl
    · exact residentCaller
    · exact le_rfl
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rcases nativeQuadratic_narrow_visited eligible candidate original path visited present with
      rfl | rfl
    · exact auxiliaryCaller
    · exact le_rfl

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection
