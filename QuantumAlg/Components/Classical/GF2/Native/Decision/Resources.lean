/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual event resources of the original GF(2) decisions

The same actual branch path determines both emitted markers and duration.
The bounds cover every syntactic path, including either equality rejecting,
without assuming a valid free mask or any original latch initialization.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original rejection always emits copy before stable self-XOR. -/
def decisionFailureEvents (kind : ProblemKind) : List (Resource.Event kind) :=
  [.classicalOperation (.bit .copy), .classicalOperation (.bit .xor)]

/-- The actual stored equality outcome chooses the corresponding real marker events. -/
def decisionBranchEvents (kind : ProblemKind) (reject : Bool) :
    CShape.Value .bit → List (Resource.Event kind)
  | .bit value =>
      match reject, value with
      | false, false => decisionFailureEvents kind
      | false, true => []
      | true, false => []
      | true, true => decisionFailureEvents kind

/-- The original equality retains its native width. -/
def decisionEqualityEvent (kind : ProblemKind) (width : Nat) : Resource.Event kind :=
  .classicalOperation (.wordBinary .equal width)

/-- Both original failure instructions are emitted on every failure path. -/
theorem gf2MarkFailure_events (success : CWriteRef ctx .bit)
    (path : (markFailure success).Path) :
    (markFailure success).eventTrace path = decisionFailureEvents kind := rfl

/-- The same real branch outcome selects precisely the original marker events. -/
theorem gf2DecisionChoice_events (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).eventTrace path = decisionBranchEvents kind reject value
      := by
  cases value with
  | bit value => cases reject <;> cases value <;> rfl

/-- The exact original equality event precedes the branch's actual emitted markers. -/
theorem gf2DecisionTest_events (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).eventTrace path =
      [decisionEqualityEvent kind width] ++ decisionBranchEvents kind reject path.2.1 :=
  congrArg (fun events : List (Resource.Event kind) => [decisionEqualityEvent kind width] ++ events)
    (gf2DecisionChoice_events reject success path.2.1 path.2.2)

private theorem choice_duration (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (duration : Resource.Event kind → Nat)
    (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).depth duration path =
      ((decisionBranchEvents kind reject value).map duration).sum := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · change duration (.classicalOperation (.bit .copy)) +
          duration (.classicalOperation (.bit .xor)) =
            duration (.classicalOperation (.bit .copy)) +
              (duration (.classicalOperation (.bit .xor)) + 0)
        omega
      · rfl
      · rfl
      · change duration (.classicalOperation (.bit .copy)) +
          duration (.classicalOperation (.bit .xor)) =
            duration (.classicalOperation (.bit .copy)) +
              (duration (.classicalOperation (.bit .xor)) + 0)
        omega

/-- Every actual equality and selected failure path has its exact serial duration sum. -/
theorem gf2DecisionTest_duration_eventTrace (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).depth duration path =
      (((decisionTest reject left right success flag).eventTrace path).map duration).sum := by
  change duration (decisionEqualityEvent kind width) +
    (decisionChoice reject success path.2.1).depth duration path.2.2 = _
  rw [gf2DecisionTest_events, choice_duration]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- One real equality and its possible original two-instruction failure marker. -/
def decisionTestEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (decisionEqualityEvent kind width) +
    ResourcePool.ofList (decisionFailureEvents kind)

/-- The original decrement and mask precede both equality decisions. -/
def uniqueFreeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordUnary .decrement width)) +
    (ResourcePool.singleton (.classicalOperation (.wordBinary .bitAnd width)) +
      (decisionTestEnvelope kind width + decisionTestEnvelope kind width))

/-- Every original equality duration is followed by its possible copy and clear durations. -/
def decisionTestDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (decisionEqualityEvent kind width) +
    (duration (.classicalOperation (.bit .copy)) + duration (.classicalOperation (.bit .xor)))

/-- All four original unconditional instructions and both failure arms retain their durations. -/
def uniqueFreeDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.wordUnary .decrement width)) +
    (duration (.classicalOperation (.wordBinary .bitAnd width)) +
      (decisionTestDepthLimit width duration + decisionTestDepthLimit width duration))

private theorem choice_pool_le (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).resourcePool path ≤
      ResourcePool.ofList (decisionFailureEvents kind) := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · exact le_rfl
      · change (0 : ResourcePool kind) ≤ _
        exact zero_le
      · change (0 : ResourcePool kind) ≤ _
        exact zero_le
      · exact le_rfl

private theorem choice_depth_le (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (duration : Resource.Event kind → Nat)
    (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).depth duration path ≤
      duration (.classicalOperation (.bit .copy)) + duration (.classicalOperation (.bit .xor)) := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · exact le_rfl
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact le_rfl

/-- Every actual equality-test path respects its original native allowance. -/
theorem gf2DecisionTest_pool_le (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).resourcePool path ≤
      decisionTestEnvelope kind width := by
  change ResourcePool.ofList ([decisionEqualityEvent kind width] ++
    (decisionChoice reject success path.2.1).eventTrace path.2.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add le_rfl (choice_pool_le reject success path.2.1 path.2.2)

/-- Every actual equality-test path retains its arbitrary-duration allowance. -/
theorem gf2DecisionTest_depth_le (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).depth duration path ≤
      decisionTestDepthLimit width duration :=
  Nat.add_le_add_left (choice_depth_le reject success path.2.1 duration path.2.2) _

/-- The complete unique-free body charges both real tests after its decrement and mask. -/
theorem gf2UniqueFreeBody_pool_le (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).resourcePool path ≤
      uniqueFreeEnvelope kind width := by
  change ResourcePool.ofList
    ([.classicalOperation (.wordUnary .decrement width)] ++
      (([.classicalOperation (.wordBinary .bitAnd width)] : List (Resource.Event kind)) ++
        ((decisionTest false work zero success flag).eventTrace path.2.2.1 ++
          (decisionTest true free zero success flag).eventTrace path.2.2.2))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl
    (add_le_add (gf2DecisionTest_pool_le false work zero success flag path.2.2.1)
      (gf2DecisionTest_pool_le true free zero success flag path.2.2.2)))

/-- The complete unique-free body retains every original serial duration. -/
theorem gf2UniqueFreeBody_depth_le (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (duration : Resource.Event kind → Nat)
    (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).depth duration path ≤
      uniqueFreeDepthLimit width duration :=
  Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add (gf2DecisionTest_depth_le false work zero success flag duration path.2.2.1)
      (gf2DecisionTest_depth_le true free zero success flag duration path.2.2.2)) _) _

/-- The original complete unique-free body has exact same-path serial event durations. -/
theorem gf2UniqueFreeBody_duration_eventTrace
    (free zero work : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).depth duration path =
      (((uniqueFreeBody free zero work success flag).eventTrace path).map duration).sum := by
  change duration (.classicalOperation (.wordUnary .decrement width)) +
    (duration (.classicalOperation (.wordBinary .bitAnd width)) +
      ((decisionTest false work zero success flag).depth duration path.2.2.1 +
        (decisionTest true free zero success flag).depth duration path.2.2.2)) =
    ((([.classicalOperation (.wordUnary .decrement width)] : List (Resource.Event kind)) ++
      (([.classicalOperation (.wordBinary .bitAnd width)] : List (Resource.Event kind)) ++
        ((decisionTest false work zero success flag).eventTrace path.2.2.1 ++
          (decisionTest true free zero success flag).eventTrace path.2.2.2))).map duration).sum
  rw [gf2DecisionTest_duration_eventTrace, gf2DecisionTest_duration_eventTrace]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Both actual scopes preserve the complete unique-free native allowance. -/
theorem gf2UniqueFree_pool_le (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).resourcePool path ≤ uniqueFreeEnvelope kind width :=
  gf2UniqueFreeBody_pool_le _ _ _ _ _ path

/-- Both actual scopes preserve the complete unique-free duration allowance. -/
theorem gf2UniqueFree_depth_le (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (duration : Resource.Event kind → Nat)
    (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).depth duration path ≤
      uniqueFreeDepthLimit width duration :=
  gf2UniqueFreeBody_depth_le _ _ _ _ _ duration path

/-- Complete lexical initialization and release do not insert uncharged decision events. -/
theorem gf2UniqueFree_duration_eventTrace (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (duration : Resource.Event kind → Nat)
    (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).depth duration path =
      (((selectUniqueFree free zero success).eventTrace path).map duration).sum :=
  gf2UniqueFreeBody_duration_eventTrace _ _ _ _ _ duration path

/-- The original nonzero check charges its equality and both possible failure instructions. -/
theorem gf2CandidateNonzero_pool_le (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).resourcePool path ≤
      decisionTestEnvelope kind width :=
  gf2DecisionTest_pool_le true _ _ _ _ path

/-- Both nonzero-check scopes preserve its actual arbitrary-duration allowance. -/
theorem gf2CandidateNonzero_depth_le (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (duration : Resource.Event kind → Nat)
    (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).depth duration path ≤
      decisionTestDepthLimit width duration :=
  gf2DecisionTest_depth_le true _ _ _ _ duration path

/-- Even the original unused-word scope retains exactly the same actual decision durations. -/
theorem gf2CandidateNonzero_duration_eventTrace
    (candidate zero : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).depth duration path =
      (((checkCandidateNonzero candidate zero success).eventTrace path).map duration).sum :=
  gf2DecisionTest_duration_eventTrace true _ _ _ _ duration path

/-- Every syntactic unique-free path contains at most the original eight native instructions. -/
theorem gf2UniqueFree_unit_depth_le (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).depth (fun _ => 1) path ≤ 8 :=
  gf2UniqueFree_depth_le free zero success (fun _ => 1) path

/-- Every syntactic nonzero-check path contains at most its original three native instructions. -/
theorem gf2CandidateNonzero_unit_depth_le
    (candidate zero : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).depth (fun _ => 1) path ≤ 3 :=
  gf2CandidateNonzero_depth_le candidate zero success (fun _ => 1) path

end

end QuantumAlg.ClassicalRoutines.GF2.Native
