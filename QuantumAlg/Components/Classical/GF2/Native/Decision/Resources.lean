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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The selected native coordinate of one built-in bit or word operation. -/
def decisionOperationEvent (label : Resource.ClassicalOpLabel) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model) label)

/-- The original rejection always emits copy before stable self-XOR. -/
def decisionFailureEvents : List (Resource.Event model) :=
  [decisionOperationEvent (model := model) (.bit .copy),
    decisionOperationEvent (model := model) (.bit .xor)]

/-- The actual stored equality outcome chooses the corresponding real marker events. -/
def decisionBranchEvents (reject : Bool) : CShape.Value .bit → List (Resource.Event model)
  | .bit value =>
      match reject, value with
      | false, false => decisionFailureEvents (model := model)
      | false, true => []
      | true, false => []
      | true, true => decisionFailureEvents (model := model)

/-- The original equality retains its native width. -/
def decisionEqualityEvent (width : Nat) : Resource.Event model :=
  decisionOperationEvent (model := model) (.wordBinary .equal width)

/-- Both original failure instructions are emitted on every failure path. -/
lemma gf2MarkFailure_events (success : CWriteRef ctx .bit)
    (path : (markFailure success).Path) :
    (markFailure success).eventTrace path = decisionFailureEvents (model := model) := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotRejectedOp success))
    (BitWord.instruction (execution := model) (pivotClearOp success))).Path at path
  change (BitWord.instruction (execution := model) (pivotRejectedOp success)).eventTrace path.1 ++
    (BitWord.instruction (execution := model) (pivotClearOp success)).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change [decisionOperationEvent (model := model) (.bit .copy),
    decisionOperationEvent (model := model) (.bit .xor)] = _
  rfl

/-- Failure-marker depth is the sum of its two selected native instructions. -/
private lemma markFailure_duration (success : CWriteRef ctx .bit)
    (duration : Resource.Event model → Nat) (path : (markFailure success).Path) :
    (markFailure success).depth duration path =
      duration (decisionOperationEvent (model := model) (.bit .copy)) +
        duration (decisionOperationEvent (model := model) (.bit .xor)) := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotRejectedOp success))
    (BitWord.instruction (execution := model) (pivotClearOp success))).Path at path
  change (BitWord.instruction (execution := model) (pivotRejectedOp success)).depth
      duration path.1 +
    (BitWord.instruction (execution := model) (pivotClearOp success)).depth
      duration path.2 = _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  rfl

/-- The same real branch outcome selects precisely the original marker events. -/
lemma gf2DecisionChoice_events (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).eventTrace path =
      decisionBranchEvents (model := model) reject value
      := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · change (markFailure (model := model) success).Path at path
        exact gf2MarkFailure_events success path
      · rfl
      · rfl
      · change (markFailure (model := model) success).Path at path
        exact gf2MarkFailure_events success path

/-- The exact original equality event precedes the branch's actual emitted markers. -/
lemma gf2DecisionTest_events (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).eventTrace path =
      [decisionEqualityEvent (model := model) width] ++
        decisionBranchEvents (model := model) reject path.2.1 := by
  change (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success))).Path at path
  change (BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag)).eventTrace path.1 ++
    (decisionChoice (model := model) reject success path.2.1).eventTrace path.2.2 = _
  rw [BitWord.bitWord_instruction_eventTrace]
  exact congrArg (fun events : List (Resource.Event model) =>
    [decisionEqualityEvent (model := model) width] ++ events)
    (gf2DecisionChoice_events reject success path.2.1 path.2.2)

private lemma choice_duration (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (duration : Resource.Event model → Nat)
    (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).depth duration path =
      ((decisionBranchEvents (model := model) reject value).map duration).sum := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · change (markFailure (model := model) success).Path at path
        change (markFailure (model := model) success).depth duration path =
          ((decisionFailureEvents (model := model)).map duration).sum
        rw [markFailure_duration]
        simp only [decisionFailureEvents, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      · rfl
      · rfl
      · change (markFailure (model := model) success).Path at path
        change (markFailure (model := model) success).depth duration path =
          ((decisionFailureEvents (model := model)).map duration).sum
        rw [markFailure_duration]
        simp only [decisionFailureEvents, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Every actual equality and selected failure path has its exact serial duration sum. -/
lemma gf2DecisionTest_duration_eventTrace (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (duration : Resource.Event model → Nat)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).depth duration path =
      (((decisionTest reject left right success flag).eventTrace path).map duration).sum := by
  change (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success))).Path at path
  change (BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag)).depth duration path.1 +
    (decisionChoice (model := model) reject success path.2.1).depth duration path.2.2 =
      (((BitWord.instruction (execution := model)
          (decisionEqualityOp left right flag)).eventTrace path.1 ++
        (decisionChoice (model := model) reject success path.2.1).eventTrace path.2.2).map
          duration).sum
  rw [BitWord.bitWord_instruction_depth]
  change duration (decisionEqualityEvent (model := model) width) +
    (decisionChoice reject success path.2.1).depth duration path.2.2 = _
  rw [choice_duration, BitWord.bitWord_instruction_eventTrace,
    gf2DecisionChoice_events]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

/-- One real equality and its possible original two-instruction failure marker. -/
def decisionTestEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.singleton (decisionEqualityEvent (model := model) width) +
    ResourcePool.ofList (decisionFailureEvents (model := model))

/-- The original decrement and mask precede both equality decisions. -/
def uniqueFreeEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.singleton
      (decisionOperationEvent (model := model) (.wordUnary .decrement width)) +
    (ResourcePool.singleton
        (decisionOperationEvent (model := model) (.wordBinary .bitAnd width)) +
      (decisionTestEnvelope (model := model) width +
        decisionTestEnvelope (model := model) width))

/-- Every original equality duration is followed by its possible copy and clear durations. -/
def decisionTestDepthLimit (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (decisionEqualityEvent (model := model) width) +
    (duration (decisionOperationEvent (model := model) (.bit .copy)) +
      duration (decisionOperationEvent (model := model) (.bit .xor)))

/-- All four original unconditional instructions and both failure arms retain their durations. -/
def uniqueFreeDepthLimit (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (decisionOperationEvent (model := model) (.wordUnary .decrement width)) +
    (duration (decisionOperationEvent (model := model) (.wordBinary .bitAnd width)) +
      (decisionTestDepthLimit (model := model) width duration +
        decisionTestDepthLimit (model := model) width duration))

private lemma choice_pool_le (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).resourcePool path ≤
      ResourcePool.ofList (decisionFailureEvents (model := model)) := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · change (markFailure (model := model) success).Path at path
        change ResourcePool.ofList ((markFailure (model := model) success).eventTrace path) ≤ _
        rw [gf2MarkFailure_events]
      · change (0 : ResourcePool model) ≤ _
        exact zero_le
      · change (0 : ResourcePool model) ≤ _
        exact zero_le
      · change (markFailure (model := model) success).Path at path
        change ResourcePool.ofList ((markFailure (model := model) success).eventTrace path) ≤ _
        rw [gf2MarkFailure_events]

private lemma choice_depth_le (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (duration : Resource.Event model → Nat)
    (path : (decisionChoice reject success value).Path) :
    (decisionChoice reject success value).depth duration path ≤
      duration (decisionOperationEvent (model := model) (.bit .copy)) +
        duration (decisionOperationEvent (model := model) (.bit .xor)) := by
  cases value with
  | bit value =>
      cases reject <;> cases value
      · change (markFailure (model := model) success).Path at path
        change (markFailure (model := model) success).depth duration path ≤ _
        rw [markFailure_duration]
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · change (markFailure (model := model) success).Path at path
        change (markFailure (model := model) success).depth duration path ≤ _
        rw [markFailure_duration]

/-- Every actual equality-test path respects its original native allowance. -/
lemma gf2DecisionTest_pool_le (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).resourcePool path ≤
      decisionTestEnvelope (model := model) width := by
  change (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success))).Path at path
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag)).eventTrace path.1 ++
      (decisionChoice (model := model) reject success path.2.1).eventTrace path.2.2) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList ([decisionEqualityEvent (model := model) width] ++
    (decisionChoice reject success path.2.1).eventTrace path.2.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add le_rfl (choice_pool_le reject success path.2.1 path.2.2)

/-- Every actual equality-test path retains its arbitrary-duration allowance. -/
lemma gf2DecisionTest_depth_le (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (duration : Resource.Event model → Nat)
    (path : (decisionTest reject left right success flag).Path) :
    (decisionTest reject left right success flag).depth duration path ≤
      decisionTestDepthLimit (model := model) width duration := by
  change (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef)
      (decisionChoice (model := model) reject success))).Path at path
  change (BitWord.instruction (execution := model)
      (decisionEqualityOp left right flag)).depth duration path.1 +
    (decisionChoice (model := model) reject success path.2.1).depth duration path.2.2 ≤ _
  rw [BitWord.bitWord_instruction_depth]
  exact Nat.add_le_add_left (choice_depth_le reject success path.2.1 duration path.2.2) _

/-- The complete unique-free body charges both real tests after its decrement and mask. -/
lemma gf2UniqueFreeBody_pool_le (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).resourcePool path ≤
      uniqueFreeEnvelope (model := model) width := by
  change (Circuit.seq (BitWord.instruction (execution := model) (decisionDecrementOp free work))
    (.seq (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag)))).Path at path
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (decisionDecrementOp free work)).eventTrace
        path.1 ++
      ((BitWord.instruction (execution := model) (decisionMaskOp free work)).eventTrace
          path.2.1 ++
        ((decisionTest (model := model) false work zero success flag).eventTrace path.2.2.1 ++
          (decisionTest (model := model) true free zero success flag).eventTrace
            path.2.2.2))) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList
    ([decisionOperationEvent (model := model) (.wordUnary .decrement width)] ++
      (([decisionOperationEvent (model := model) (.wordBinary .bitAnd width)] :
          List (Resource.Event model)) ++
        ((decisionTest false work zero success flag).eventTrace path.2.2.1 ++
          (decisionTest true free zero success flag).eventTrace path.2.2.2))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl
    (add_le_add (gf2DecisionTest_pool_le false work zero success flag path.2.2.1)
      (gf2DecisionTest_pool_le true free zero success flag path.2.2.2)))

/-- The complete unique-free body retains every original serial duration. -/
lemma gf2UniqueFreeBody_depth_le (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).depth duration path ≤
      uniqueFreeDepthLimit (model := model) width duration := by
  change (Circuit.seq (BitWord.instruction (execution := model) (decisionDecrementOp free work))
    (.seq (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag)))).Path at path
  change (BitWord.instruction (execution := model) (decisionDecrementOp free work)).depth
      duration path.1 +
    ((BitWord.instruction (execution := model) (decisionMaskOp free work)).depth
      duration path.2.1 +
      ((decisionTest (model := model) false work zero success flag).depth duration path.2.2.1 +
        (decisionTest (model := model) true free zero success flag).depth
          duration path.2.2.2)) ≤ _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  exact Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add (gf2DecisionTest_depth_le false work zero success flag duration path.2.2.1)
      (gf2DecisionTest_depth_le true free zero success flag duration path.2.2.2)) _) _

/-- The original complete unique-free body has exact same-path serial event durations. -/
lemma gf2UniqueFreeBody_duration_eventTrace
    (free zero work : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (duration : Resource.Event model → Nat)
    (path : (uniqueFreeBody free zero work success flag).Path) :
    (uniqueFreeBody free zero work success flag).depth duration path =
      (((uniqueFreeBody free zero work success flag).eventTrace path).map duration).sum := by
  change (Circuit.seq (BitWord.instruction (execution := model) (decisionDecrementOp free work))
    (.seq (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag)))).Path at path
  change (BitWord.instruction (execution := model) (decisionDecrementOp free work)).depth
      duration path.1 +
    ((BitWord.instruction (execution := model) (decisionMaskOp free work)).depth
      duration path.2.1 +
      ((decisionTest (model := model) false work zero success flag).depth duration path.2.2.1 +
        (decisionTest (model := model) true free zero success flag).depth
          duration path.2.2.2)) =
    (((BitWord.instruction (execution := model) (decisionDecrementOp free work)).eventTrace
        path.1 ++
      ((BitWord.instruction (execution := model) (decisionMaskOp free work)).eventTrace
          path.2.1 ++
        ((decisionTest (model := model) false work zero success flag).eventTrace path.2.2.1 ++
          (decisionTest (model := model) true free zero success flag).eventTrace
            path.2.2.2))).map duration).sum
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change duration (decisionOperationEvent (model := model) (.wordUnary .decrement width)) +
    (duration (decisionOperationEvent (model := model) (.wordBinary .bitAnd width)) +
      ((decisionTest false work zero success flag).depth duration path.2.2.1 +
        (decisionTest true free zero success flag).depth duration path.2.2.2)) =
    ((([decisionOperationEvent (model := model) (.wordUnary .decrement width)] :
        List (Resource.Event model)) ++
      (([decisionOperationEvent (model := model) (.wordBinary .bitAnd width)] :
          List (Resource.Event model)) ++
        ((decisionTest false work zero success flag).eventTrace path.2.2.1 ++
          (decisionTest true free zero success flag).eventTrace path.2.2.2))).map duration).sum
  rw [gf2DecisionTest_duration_eventTrace, gf2DecisionTest_duration_eventTrace]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Both actual scopes preserve the complete unique-free native allowance. -/
lemma gf2UniqueFree_pool_le (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).resourcePool path ≤
      uniqueFreeEnvelope (model := model) width :=
  gf2UniqueFreeBody_pool_le _ _ _ _ _ path

/-- Both actual scopes preserve the complete unique-free duration allowance. -/
lemma gf2UniqueFree_depth_le (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).depth duration path ≤
      uniqueFreeDepthLimit (model := model) width duration :=
  gf2UniqueFreeBody_depth_le _ _ _ _ _ duration path

/-- Complete lexical initialization and release do not insert uncharged decision events. -/
lemma gf2UniqueFree_duration_eventTrace (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).depth duration path =
      (((selectUniqueFree free zero success).eventTrace path).map duration).sum :=
  gf2UniqueFreeBody_duration_eventTrace _ _ _ _ _ duration path

/-- The original nonzero check charges its equality and both possible failure instructions. -/
lemma gf2CandidateNonzero_pool_le (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).resourcePool path ≤
      decisionTestEnvelope (model := model) width :=
  gf2DecisionTest_pool_le true _ _ _ _ path

/-- Both nonzero-check scopes preserve its actual arbitrary-duration allowance. -/
lemma gf2CandidateNonzero_depth_le (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).depth duration path ≤
      decisionTestDepthLimit (model := model) width duration :=
  gf2DecisionTest_depth_le true _ _ _ _ duration path

/-- Even the original unused-word scope retains exactly the same actual decision durations. -/
lemma gf2CandidateNonzero_duration_eventTrace
    (candidate zero : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (duration : Resource.Event model → Nat)
    (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).depth duration path =
      (((checkCandidateNonzero candidate zero success).eventTrace path).map duration).sum :=
  gf2DecisionTest_duration_eventTrace true _ _ _ _ duration path

/-- Every syntactic unique-free path contains at most the original eight native instructions. -/
lemma gf2UniqueFree_unit_depth_le (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (path : (selectUniqueFree free zero success).Path) :
    (selectUniqueFree free zero success).depth (fun _ => 1) path ≤ 8 :=
  gf2UniqueFree_depth_le free zero success (fun _ => 1) path

/-- Every syntactic nonzero-check path contains at most its original three native instructions. -/
lemma gf2CandidateNonzero_unit_depth_le
    (candidate zero : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (path : (checkCandidateNonzero candidate zero success).Path) :
    (checkCandidateNonzero candidate zero success).depth (fun _ => 1) path ≤ 3 :=
  gf2CandidateNonzero_depth_le candidate zero success (fun _ => 1) path

end

end QuantumAlg.ClassicalRoutines.GF2.Native
