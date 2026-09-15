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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual shift coordinate contains the intrinsic target width. -/
def shiftEvent (kind : ProblemKind) (width : Nat) : Resource.Event kind :=
  .classicalOperation (.wordUnary .shiftLeft width)

/-- The actual selected increment coordinate contains the same target width. -/
def incrementEvent (kind : ProblemKind) (width : Nat) : Resource.Event kind :=
  .classicalOperation (.wordUnary .increment width)

/-- Independent capacity of one compiled bit, admitting either literal branch. -/
def bitEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (shiftEvent kind width) +
    ResourcePool.singleton (incrementEvent kind width)

/-- Independent native capacity, with exactly one bit allowance per target position. -/
def envelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.scale width (bitEnvelope kind width)

/-- The literal source bit determines the actual emitted native event list. -/
theorem constantWord_append_eventTrace (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (path : (append output bit).Path) :
    (append output bit).eventTrace path =
      [shiftEvent kind width] ++ if bit then [incrementEvent kind width] else [] := by
  cases bit <;> rfl

/-- Either literal bit fits the independent two-coordinate allowance. -/
theorem constantWord_append_pool_le (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (path : (append output bit).Path) :
    (append output bit).resourcePool path ≤ bitEnvelope kind width := by
  change ResourcePool.ofList ((append output bit).eventTrace path) ≤ _
  rw [constantWord_append_eventTrace]
  cases bit
  · exact le_add_of_nonneg_right
      (zero_le : (0 : ResourcePool kind) ≤ ResourcePool.singleton (incrementEvent kind width))
  · exact le_rfl

/-- The actual list fold fits one independent bit allowance per compiled list element. -/
theorem constantWord_fold_pool_le (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) : ∀ path : (fold output bits).Path,
    (fold output bits).resourcePool path ≤
      ResourcePool.scale bits.length (bitEnvelope kind width) := by
  induction bits with
  | nil => intro path; exact le_rfl
  | cons bit remaining ih =>
      intro path
      change ResourcePool.ofList ((append output bit).eventTrace path.1 ++
        (fold output remaining).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (constantWord_append_pool_le output bit path.1) (ih path.2)

/-- The literal whole-word program satisfies its independent native-coordinate budget. -/
theorem constantWord_pool_le (output : CWriteRef ctx (.unsignedWord width)) (constant : Nat)
    (path : (circuit output constant).Path) :
    (circuit output constant).resourcePool path ≤ envelope kind width := by
  simpa only [circuit, envelope, List.length_ofFn] using
    constantWord_fold_pool_le output (List.ofFn (constantBits width constant)) path

/-- Each actual bit has the duration of its shift and selected increment only. -/
theorem constantWord_append_depth (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (duration : Resource.Event kind → Nat) (path : (append output bit).Path) :
    (append output bit).depth duration path =
      duration (shiftEvent kind width) +
        if bit then duration (incrementEvent kind width) else 0 := by
  cases bit <;> rfl

/-- The real serial fold has the sum of at most one shift and increment duration per bit. -/
theorem constantWord_fold_depth_le (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (duration : Resource.Event kind → Nat) :
    ∀ path : (fold output bits).Path,
      (fold output bits).depth duration path ≤ bits.length *
        (duration (shiftEvent kind width) + duration (incrementEvent kind width)) := by
  induction bits with
  | nil => intro path; exact Nat.zero_le _
  | cons bit remaining ih =>
      intro path
      change (append output bit).depth duration path.1 +
        (fold output remaining).depth duration path.2 ≤ _
      rw [constantWord_append_depth]
      have later := ih path.2
      simp only [List.length_cons, Nat.succ_mul]
      cases bit <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- Width-many actual bits give the explicit whole-word native duration bound. -/
theorem constantWord_depth_le (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (duration : Resource.Event kind → Nat)
    (path : (circuit output constant).Path) :
    (circuit output constant).depth duration path ≤ width *
      (duration (shiftEvent kind width) + duration (incrementEvent kind width)) := by
  simpa only [circuit, List.length_ofFn] using
    constantWord_fold_depth_le output (List.ofFn (constantBits width constant)) duration path

/-- No literal compiled bit allocates a new cell. -/
theorem constantWord_append_visited (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (path : (append output bit).Path) :
    (append output bit).visitedContexts path = [ctx, ctx] := by
  cases bit <;> rfl

/-- Every context visited by the complete literal fold is the original live context. -/
theorem constantWord_fold_visited (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) : ∀ (path : (fold output bits).Path) (visited : RuntimeCtx kind),
    visited ∈ (fold output bits).visitedContexts path → visited = ctx := by
  induction bits with
  | nil => intro path visited present; exact List.mem_singleton.mp present
  | cons bit remaining ih =>
      intro path visited present
      change visited ∈ (append output bit).visitedContexts path.1 ++
        (fold output remaining).visitedContexts path.2 at present
      rcases List.mem_append.mp present with first | later
      · rw [constantWord_append_visited] at first
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using first
      · exact ih path.2 visited later

/-- Loading a known word needs only the resident storage already present. -/
theorem constantWord_resident_le (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (path : (circuit output constant).Path) :
    (circuit output constant).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (constantWord_fold_visited output _ path visited present) ▸ le_rfl

/-- The auxiliary peak needs no storage beyond existing scopes. -/
theorem constantWord_auxiliary_le (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (path : (circuit output constant).Path) :
    (circuit output constant).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (constantWord_fold_visited output _ path visited present) ▸ le_rfl

end QuantumAlg.ClassicalRoutines.ConstantWord
