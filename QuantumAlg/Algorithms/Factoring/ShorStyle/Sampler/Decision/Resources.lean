/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Resources
import all QuantumAlg.Components.Classical.NumberTheory.GCD.EventCounts

/-!
# Independent native coordinates for the actual residue decision

The envelope retains each operation's real word width and includes both
possible result-arm coordinates. Rejection's single payload clear is already
covered by the unit-arm allowance. The envelope's cardinality is a capacity
bound, not a claim that either branch executes the other branch's events.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Four unconditional instructions initialize the actual candidate, unit and tag. -/
def initializationEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordBinary .bitXor width),
    .classicalOperation (.wordUnary .increment width),
    .classicalOperation (.bit .xor)]

/-- Literal unit-copy and payload-clear coordinates. -/
def unitEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordBinary .bitXor width)]

/-- Literal factor-resize and tag-negation coordinates. -/
def factorEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize (width + 1) width),
    .classicalOperation (.bit .not)]

/-- The real stored-unit resize and GCD equality coordinates. -/
def comparisonEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize width (width + 1)),
    .classicalOperation (.wordBinary .equal (width + 1))]

/-- An independent coordinate allowance that covers either selected result arm. -/
def resultEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (unitEvents kind width) + ResourcePool.ofList (factorEvents kind width)

/-- Candidate widening, the expanded GCD, the stored test and either result arm. -/
def acceptedEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordResize width (width + 1))) +
    (NumberTheory.GCD.nativeEnvelope kind (width + 1) +
      (ResourcePool.ofList (comparisonEvents kind width) + resultEnvelope kind width))

/-- Complete allowance for initialization, the selected decision, and the final product write. -/
def nativeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (initializationEvents kind width) +
    (acceptedEnvelope kind width +
      ResourcePool.singleton (.classicalOperation
        (.nominalEncoding (.packProduct width (1 + width)))))

/-- The actual stored branch charges precisely one of the two literal result traces. -/
theorem decisionResult_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (chooseResult shared scratch gcdResult).Path) :
    (chooseResult shared scratch gcdResult).resourcePool path ≤ resultEnvelope kind width := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · change ResourcePool.ofList (factorEvents kind width) ≤ _
        exact le_add_of_nonneg_left
          (zero_le : (0 : ResourcePool kind) ≤ ResourcePool.ofList (unitEvents kind width))
      · change ResourcePool.ofList (unitEvents kind width) ≤ _
        exact le_add_of_nonneg_right
          (zero_le : (0 : ResourcePool kind) ≤ ResourcePool.ofList (factorEvents kind width))

/-- The accepted trace contains its actual GCD path and selected result path. -/
theorem decisionAccepted_eventTrace (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (acceptedBody shared scratch gcdResult).Path) :
    (acceptedBody shared scratch gcdResult).eventTrace path =
      [.classicalOperation (.wordResize width (width + 1))] ++
        ((NumberTheory.GCD.lexicalBody
          (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult).eventTrace
            path.2.1 ++
          (comparisonEvents kind width ++
            (chooseResult shared scratch gcdResult).eventTrace path.2.2.2.2)) := rfl

/-- Every actual accepted-arm event is bounded at its exact native coordinate. -/
theorem decisionAccepted_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (acceptedBody shared scratch gcdResult).Path) :
    (acceptedBody shared scratch gcdResult).resourcePool path ≤ acceptedEnvelope kind width := by
  rw [Circuit.resourcePool, decisionAccepted_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (NumberTheory.GCD.gcdLexical_pool_le
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult path.2.1)
    (add_le_add le_rfl (decisionResult_pool_le shared scratch gcdResult path.2.2.2.2)))

private theorem rejected_pool_le (kind : ProblemKind) (width : Nat) :
    ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor width)) ≤
      acceptedEnvelope kind width := by
  have unitBound : ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor width)) ≤
      ResourcePool.ofList (unitEvents kind width) := by
    change ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor width)) ≤
      ResourcePool.singleton (.classicalOperation (.wordUnary .copy width)) +
        ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor width))
    exact le_add_of_nonneg_left zero_le
  have resultBound : ResourcePool.ofList (unitEvents kind width) ≤ resultEnvelope kind width :=
    le_add_of_nonneg_right zero_le
  have comparisonBound : resultEnvelope kind width ≤
      ResourcePool.ofList (comparisonEvents kind width) + resultEnvelope kind width :=
    le_add_of_nonneg_left zero_le
  have gcdBound : ResourcePool.ofList (comparisonEvents kind width) + resultEnvelope kind width ≤
      NumberTheory.GCD.nativeEnvelope kind (width + 1) +
        (ResourcePool.ofList (comparisonEvents kind width) + resultEnvelope kind width) :=
    le_add_of_nonneg_left zero_le
  exact unitBound.trans (resultBound.trans (comparisonBound.trans
    (gcdBound.trans (le_add_of_nonneg_left zero_le))))

/-- Actual acceptance selection fits the same envelope, including its rejected payload clear. -/
theorem decisionAcceptance_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (chooseAccepted shared scratch gcdResult).Path) :
    (chooseAccepted shared scratch gcdResult).resourcePool path ≤ acceptedEnvelope kind width := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · exact rejected_pool_le kind width
      · exact decisionAccepted_pool_le shared scratch gcdResult selected

/-- Every path of the full native decision satisfies its independently stated resource pool. -/
theorem decision_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width))
    (path : (circuit shared scratch gcdResult output).Path) :
    (circuit shared scratch gcdResult output).resourcePool path ≤ nativeEnvelope kind width := by
  change ResourcePool.ofList (initializationEvents kind width ++
    ((chooseAccepted shared scratch gcdResult).eventTrace path.2.1 ++
      [.classicalOperation
        (.nominalEncoding (.packProduct width (1 + width)))])) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (decisionAcceptance_pool_le shared scratch gcdResult path.2.1) le_rfl)

/-- Independent coordinate capacity is linear, including width zero. -/
theorem decisionNativeEnvelope_card (kind : ProblemKind) (width : Nat) :
    (nativeEnvelope kind width).card = 10 * width + 32 := by
  simp only [nativeEnvelope, acceptedEnvelope, resultEnvelope, Multiset.card_add,
    NumberTheory.GCD.gcdNativeEnvelope_card]
  simp [initializationEvents, unitEvents, factorEvents, comparisonEvents,
    ResourcePool.ofList, ResourcePool.singleton]
  omega

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
