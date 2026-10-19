/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Circuit
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual native resources of literal constant loading

Every compiled bit emits a shift and emits an increment precisely when that
bit is one. The independent word allowance reserves both coordinates per
target bit. All visited contexts are the original context: this loader adds
no resident or auxiliary cell, at zero width as well as positive widths.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual shift coordinate contains the intrinsic target width. -/
def shiftEvent (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordUnary .shiftLeft width))

/-- The actual selected increment coordinate contains the same target width. -/
def incrementEvent (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordUnary .increment width))

/-- Independent capacity of one compiled bit, admitting either literal branch. -/
def bitEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ResourcePool.singleton (shiftEvent model width) +
    ResourcePool.singleton (incrementEvent model width)

/-- Independent native capacity, with exactly one bit allowance per target position. -/
def envelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : ResourcePool model :=
  ResourcePool.scale width (bitEnvelope model width)

/-- The literal source bit determines the actual emitted native event list. -/
lemma constantWord_append_eventTrace (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (path : (append (model := model) output bit).Path) :
    (append (model := model) output bit).eventTrace path =
      [shiftEvent model width] ++ if bit then [incrementEvent model width] else [] := by
  cases bit with
  | false =>
      change (BitWord.instruction (execution := model) (shiftOp output)).eventTrace path.1 ++
        [] = _
      rw [BitWord.bitWord_instruction_eventTrace]
      rfl
  | true =>
      change (BitWord.instruction (execution := model) (shiftOp output)).eventTrace path.1 ++
        (BitWord.instruction (execution := model) (incrementOp output)).eventTrace path.2 = _
      rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
      rfl

/-- Either literal bit fits the independent two-coordinate allowance. -/
lemma constantWord_append_pool_le (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (path : (append (model := model) output bit).Path) :
    (append (model := model) output bit).resourcePool path ≤ bitEnvelope model width := by
  change ResourcePool.ofList ((append (model := model) output bit).eventTrace path) ≤ _
  rw [constantWord_append_eventTrace]
  cases bit
  · exact le_add_of_nonneg_right
      (zero_le : (0 : ResourcePool model) ≤ ResourcePool.singleton (incrementEvent model width))
  · exact le_rfl

/-- The actual list fold fits one independent bit allowance per compiled list element. -/
lemma constantWord_fold_pool_le (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) : ∀ path : (fold (model := model) output bits).Path,
    (fold (model := model) output bits).resourcePool path ≤
      ResourcePool.scale bits.length (bitEnvelope model width) := by
  induction bits with
  | nil => intro path; exact le_rfl
  | cons bit remaining ih =>
      intro path
      change ResourcePool.ofList ((append (model := model) output bit).eventTrace path.1 ++
        (fold (model := model) output remaining).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (constantWord_append_pool_le output bit path.1) (ih path.2)

/-- The literal whole-word program satisfies its independent native-coordinate budget. -/
lemma constantWord_pool_le (output : CWriteRef ctx (.unsignedWord width)) (constant : Nat)
    (path : (circuit (model := model) output constant).Path) :
    (circuit (model := model) output constant).resourcePool path ≤ envelope model width := by
  simpa only [circuit, envelope, List.length_ofFn] using
    constantWord_fold_pool_le output (List.ofFn (constantBits width constant)) path

/-- Each actual bit has the duration of its shift and selected increment only. -/
lemma constantWord_append_depth (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (duration : Resource.Event model → Nat)
    (path : (append (model := model) output bit).Path) :
    (append (model := model) output bit).depth duration path =
      duration (shiftEvent model width) +
        if bit then duration (incrementEvent model width) else 0 := by
  cases bit with
  | false =>
      change (BitWord.instruction (execution := model) (shiftOp output)).depth duration path.1 +
        0 = _
      rw [BitWord.bitWord_instruction_depth]
      rfl
  | true =>
      change (BitWord.instruction (execution := model) (shiftOp output)).depth duration path.1 +
        (BitWord.instruction (execution := model) (incrementOp output)).depth duration path.2 = _
      rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
      rfl

/-- The real serial fold has the sum of at most one shift and increment duration per bit. -/
lemma constantWord_fold_depth_le (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (duration : Resource.Event model → Nat) :
    ∀ path : (fold (model := model) output bits).Path,
      (fold (model := model) output bits).depth duration path ≤ bits.length *
        (duration (shiftEvent model width) + duration (incrementEvent model width)) := by
  induction bits with
  | nil => intro path; exact Nat.zero_le _
  | cons bit remaining ih =>
      intro path
      change (append (model := model) output bit).depth duration path.1 +
        (fold (model := model) output remaining).depth duration path.2 ≤ _
      rw [constantWord_append_depth]
      have later := ih path.2
      simp only [List.length_cons, Nat.succ_mul]
      cases bit <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- Width-many actual bits give the explicit whole-word native duration bound. -/
lemma constantWord_depth_le (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (duration : Resource.Event model → Nat)
    (path : (circuit (model := model) output constant).Path) :
    (circuit (model := model) output constant).depth duration path ≤ width *
      (duration (shiftEvent model width) + duration (incrementEvent model width)) := by
  simpa only [circuit, List.length_ofFn] using
    constantWord_fold_depth_le output (List.ofFn (constantBits width constant)) duration path

/-- No literal compiled bit allocates a new cell. -/
lemma constantWord_append_visited (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (path : (append (model := model) output bit).Path) :
    (append (model := model) output bit).visitedContexts path = [ctx, ctx] := by
  cases bit <;> rfl

/-- Every context visited by the complete literal fold is the original live context. -/
lemma constantWord_fold_visited (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) : ∀ (path : (fold (model := model) output bits).Path)
      (visited : RuntimeCtx model.kind),
    visited ∈ (fold (model := model) output bits).visitedContexts path → visited = ctx := by
  induction bits with
  | nil => intro path visited present; exact List.mem_singleton.mp present
  | cons bit remaining ih =>
      intro path visited present
      change visited ∈ (append (model := model) output bit).visitedContexts path.1 ++
        (fold (model := model) output remaining).visitedContexts path.2 at present
      rcases List.mem_append.mp present with first | later
      · rw [constantWord_append_visited] at first
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using first
      · exact ih path.2 visited later

/-- Loading a known word needs only the resident storage already present. -/
lemma constantWord_resident_le (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (path : (circuit (model := model) output constant).Path) :
    (circuit (model := model) output constant).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (constantWord_fold_visited output _ path visited present) ▸ le_rfl

/-- The auxiliary peak needs no storage beyond existing scopes. -/
lemma constantWord_auxiliary_le (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (path : (circuit (model := model) output constant).Path) :
    (circuit (model := model) output constant).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (constantWord_fold_visited output _ path visited present) ▸ le_rfl

end

end QuantumAlg.ClassicalRoutines.ConstantWord
