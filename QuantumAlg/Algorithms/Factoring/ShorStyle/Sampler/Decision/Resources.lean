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

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Four unconditional instructions initialize the actual candidate, unit and tag. -/
def initializationEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .xor))]

/-- Literal unit-copy and payload-clear coordinates. -/
def unitEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width))]

/-- Literal factor-resize and tag-negation coordinates. -/
def factorEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize (width + 1) width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))]

/-- The real stored-unit resize and GCD equality coordinates. -/
def comparisonEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal (width + 1)))]

/-- An independent coordinate allowance that covers either selected result arm. -/
def resultEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ResourcePool.ofList (unitEvents model width) + ResourcePool.ofList (factorEvents model width)

/-- Candidate widening, the expanded GCD, the stored test and either result arm. -/
def acceptedEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize width (width + 1)))) +
    (NumberTheory.GCD.nativeEnvelope model (width + 1) +
      (ResourcePool.ofList (comparisonEvents model width) + resultEnvelope model width))

/-- Complete allowance for initialization, the selected decision, and the final product write. -/
def nativeEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ResourcePool.ofList (initializationEvents model width) +
    (acceptedEnvelope model width +
      ResourcePool.singleton (.classicalOperation
        (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packProduct width (1 + width))))))

private lemma unit_trace (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (path : (unitBody (model := model) shared scratch).Path) :
    (unitBody (model := model) shared scratch).eventTrace path = unitEvents model width := by
  change (BitWord.instruction (execution := model) (.wordUnary .copy width ctx
    (FirstAccepted.cellRead scratch.candidate) shared.selector.selected)).eventTrace path.1 ++
    (BitWord.instruction (execution := model) (clearWordOp scratch.candidate)).eventTrace path.2 = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

private lemma factor_trace (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (factorBody (model := model) scratch gcdResult).Path) :
    (factorBody (model := model) scratch gcdResult).eventTrace path = factorEvents model width := by
  change (BitWord.instruction (execution := model) (.wordResize (width + 1) width ctx
    (FirstAccepted.cellRead gcdResult) scratch.candidate)).eventTrace path.1 ++
    (BitWord.instruction (execution := model)
      (.bit .not ctx (FirstAccepted.cellRead scratch.eligible) scratch.eligible)).eventTrace
        path.2 = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

private lemma initialization_trace (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (path : (initializeBody (model := model) shared scratch).Path) :
    (initializeBody (model := model) shared scratch).eventTrace path =
      initializationEvents model width := by
  change (BitWord.instruction (execution := model) (.wordUnary .copy width ctx
    (FirstAccepted.cellRead shared.selector.selected) scratch.candidate)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model)
      (clearWordOp shared.selector.selected)).eventTrace path.2.1 ++
      ((BitWord.instruction (execution := model) (.wordUnary .increment width ctx
        (FirstAccepted.cellRead shared.selector.selected)
          shared.selector.selected)).eventTrace path.2.2.1 ++
        (BitWord.instruction (execution := model)
          (clearBitOp scratch.eligible)).eventTrace path.2.2.2)) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The actual stored branch charges precisely one of the two literal result traces. -/
lemma decisionResult_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (chooseResult (model := model) shared scratch gcdResult).Path) :
    (chooseResult (model := model) shared scratch gcdResult).resourcePool path ≤
      resultEnvelope model width := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · change (factorBody (model := model) scratch gcdResult).Path at selected
        change ResourcePool.ofList
          ((factorBody (model := model) scratch gcdResult).eventTrace selected) ≤ _
        rw [factor_trace (model := model) scratch gcdResult selected]
        exact le_add_of_nonneg_left
          (zero_le : (0 : ResourcePool model) ≤ ResourcePool.ofList (unitEvents model width))
      · change (unitBody (model := model) shared scratch).Path at selected
        change ResourcePool.ofList
          ((unitBody (model := model) shared scratch).eventTrace selected) ≤ _
        rw [unit_trace (model := model) shared scratch selected]
        exact le_add_of_nonneg_right
          (zero_le : (0 : ResourcePool model) ≤ ResourcePool.ofList (factorEvents model width))

/-- The accepted trace contains its actual GCD path and selected result path. -/
lemma decisionAccepted_eventTrace (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (acceptedBody (model := model) shared scratch gcdResult).Path) :
    (acceptedBody (model := model) shared scratch gcdResult).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))] ++
        ((NumberTheory.GCD.lexicalBody (model := model)
          (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult).eventTrace
            path.2.1 ++
          (comparisonEvents model width ++
            (chooseResult (model := model) shared scratch gcdResult).eventTrace path.2.2.2.2)) := by
  change (BitWord.instruction (execution := model)
    (Proposal.extendOp scratch)).eventTrace path.1 ++
    ((NumberTheory.GCD.lexicalBody (model := model)
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult).eventTrace
        path.2.1 ++
      ((BitWord.instruction (execution := model) (.wordResize width (width + 1) ctx
        (FirstAccepted.cellRead shared.selector.selected) scratch.extended)).eventTrace
          path.2.2.1 ++
        ((BitWord.instruction (execution := model) (.wordBinary .equal (width + 1) ctx
          (.product (FirstAccepted.cellRead gcdResult)
            (FirstAccepted.cellRead scratch.extended)) scratch.positive)).eventTrace path.2.2.2.1 ++
          (chooseResult (model := model) shared scratch gcdResult).eventTrace path.2.2.2.2))) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Every actual accepted-arm event is bounded at its exact native coordinate. -/
lemma decisionAccepted_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (acceptedBody (model := model) shared scratch gcdResult).Path) :
    (acceptedBody (model := model) shared scratch gcdResult).resourcePool path ≤
      acceptedEnvelope model width := by
  rw [Circuit.resourcePool, decisionAccepted_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (NumberTheory.GCD.gcdLexical_pool_le
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult path.2.1)
    (add_le_add le_rfl (decisionResult_pool_le shared scratch gcdResult path.2.2.2.2)))

private lemma rejected_pool_le (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width))) ≤
      acceptedEnvelope model width := by
  have unitBound : ResourcePool.singleton (.classicalOperation
      (BitWord.selectedCoordinate (execution := model)
    (.wordBinary .bitXor width))) ≤
      ResourcePool.ofList (unitEvents model width) := by
    change ResourcePool.singleton (.classicalOperation
      (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width))) ≤
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .copy width))) +
        ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .bitXor width)))
    exact le_add_of_nonneg_left zero_le
  have resultBound : ResourcePool.ofList (unitEvents model width) ≤ resultEnvelope model width :=
    le_add_of_nonneg_right zero_le
  have comparisonBound : resultEnvelope model width ≤
      ResourcePool.ofList (comparisonEvents model width) + resultEnvelope model width :=
    le_add_of_nonneg_left zero_le
  have gcdBound : ResourcePool.ofList (comparisonEvents model width) + resultEnvelope model width ≤
      NumberTheory.GCD.nativeEnvelope model (width + 1) +
        (ResourcePool.ofList (comparisonEvents model width) + resultEnvelope model width) :=
    le_add_of_nonneg_left zero_le
  exact unitBound.trans (resultBound.trans (comparisonBound.trans
    (gcdBound.trans (le_add_of_nonneg_left zero_le))))

/-- Actual acceptance selection fits the same envelope, including its rejected payload clear. -/
lemma decisionAcceptance_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (chooseAccepted (model := model) shared scratch gcdResult).Path) :
    (chooseAccepted (model := model) shared scratch gcdResult).resourcePool path ≤
      acceptedEnvelope model width := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · change (BitWord.instruction (execution := model)
          (clearWordOp scratch.candidate)).Path at selected
        change ResourcePool.ofList ((BitWord.instruction (execution := model)
          (clearWordOp scratch.candidate)).eventTrace selected) ≤ _
        rw [BitWord.bitWord_instruction_eventTrace (execution := model)
          (clearWordOp scratch.candidate) selected]
        exact rejected_pool_le model width
      · exact decisionAccepted_pool_le shared scratch gcdResult selected

/-- Every path of the full native decision satisfies its independently stated resource pool. -/
lemma decision_pool_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width))
    (path : (circuit (model := model) shared scratch gcdResult output).Path) :
    (circuit (model := model) shared scratch gcdResult output).resourcePool path ≤
      nativeEnvelope model width := by
  change ResourcePool.ofList
    ((initializeBody (model := model) shared scratch).eventTrace path.1 ++
      ((chooseAccepted (model := model) shared scratch gcdResult).eventTrace path.2.1 ++
        (BitWord.instruction (execution := model)
          (packOp shared scratch output)).eventTrace path.2.2)) ≤ _
  rw [initialization_trace, BitWord.bitWord_instruction_eventTrace]
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (decisionAcceptance_pool_le shared scratch gcdResult path.2.1) le_rfl)

/-- Independent coordinate capacity is linear, including width zero. -/
lemma decisionNativeEnvelope_card (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) :
    (nativeEnvelope model width).card = 10 * width + 32 := by
  simp only [nativeEnvelope, acceptedEnvelope, resultEnvelope, Multiset.card_add,
    NumberTheory.GCD.gcdNativeEnvelope_card]
  simp [initializationEvents, unitEvents, factorEvents, comparisonEvents,
    ResourcePool.ofList, ResourcePool.singleton]
  omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
