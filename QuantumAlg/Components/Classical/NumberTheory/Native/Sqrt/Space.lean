/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Construction
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Complete live storage of the actual native square root

The six real scratch heads are two twice-width words, three width-word
cells and one comparison bit. Their total is `7 * width + 1` classical
bits. Every actual body instruction operates on this same context; the
complete scope trace includes each parent on entry and release. No quantum
capacity is added or removed, and the original result cell is already part
of the caller context. The same accounting includes the zero-width case.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent capacity of all six simultaneous real lexical scratch cells. -/
def additionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (7 * width + 1))

/-- Both real comparison branches operate on the same existing context. -/
theorem nativeSqrt_select_visited (refs : RoundRefs ctx width) (path : (select refs).Path) :
    (select refs).visitedContexts path = [ctx] := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit flag => cases flag <;> rfl

/-- A round's five instruction positions allocate no additional live cell. -/
theorem nativeSqrt_round_visited
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (path : (round input refs).Path) :
    (round input refs).visitedContexts path = [ctx, ctx, ctx, ctx, ctx] := by
  change [ctx] ++ ([ctx] ++ ([ctx] ++
    ((select refs).visitedContexts path.2.2.2.1 ++ [ctx]))) = _
  rw [nativeSqrt_select_visited]
  rfl

/-- Every actual iteration visits only its original live context. -/
theorem nativeSqrt_iteration_visited
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (count : Nat) (path : (Circuit.iterate count (round input refs)).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈ (Circuit.iterate count (round input refs)).visitedContexts path) :
    visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun index : Fin count =>
    (round input refs).visitedContexts (path index))).flatten at present
  rcases List.mem_cons.mp present with same | inner
  · exact same
  · rcases List.mem_flatten.mp inner with ⟨contexts, listed, member⟩
    rcases List.mem_ofFn.mp listed with ⟨index, rfl⟩
    rw [nativeSqrt_round_visited] at member
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member

/-- The entire initialized body stays within the already allocated six-cell context. -/
theorem nativeSqrt_body_visited (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (body input output).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈ (body input output).visitedContexts path) :
    visited = context ctx width := by
  change visited ∈ [context ctx width] ++
    ((ConstantWord.circuit (halfCell ctx width) (initialHalf width)).visitedContexts path.2.1 ++
      ((rounds ctx width).visitedContexts path.2.2.1 ++ [context ctx width])) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with original | loader | loop | original
  · exact original
  · exact ConstantWord.constantWord_fold_visited _ _ path.2.1 visited loader
  · exact nativeSqrt_iteration_visited _ _ width path.2.2.1 visited loop
  · exact original

private def scopeContexts (ctx : RuntimeCtx kind) (width : Nat) : List (RuntimeCtx kind) :=
  [ctx, wideContext ctx width, rootContext ctx width, halfContext ctx width,
    candidateContext ctx width, squareContext ctx width]

-- Isolate the literal list law from the body's dependent execution path.
private theorem into_trace (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into input output).Path) :
    (into input output).visitedContexts path = scopeContexts ctx width ++
      ((body input output).visitedContexts path ++ (scopeContexts ctx width).reverse) := by
  change (ctx :: ((wideContext ctx width :: ((rootContext ctx width ::
    ((halfContext ctx width :: ((candidateContext ctx width ::
      ((squareContext ctx width :: (body input output).visitedContexts path ++
        [squareContext ctx width])) ++ [candidateContext ctx width])) ++
          [halfContext ctx width])) ++ [rootContext ctx width])) ++
            [wideContext ctx width])) ++ [ctx]) = _
  simp only [scopeContexts, List.reverse_cons, List.reverse_nil,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The actual scope visits only its six allocation stages and their original parent. -/
theorem nativeSqrt_into_visited (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into input output).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (into input output).visitedContexts path) :
    visited ∈ [ctx, wideContext ctx width, rootContext ctx width, halfContext ctx width,
      candidateContext ctx width, squareContext ctx width, context ctx width] := by
  change visited ∈ scopeContexts ctx width ++ [context ctx width]
  rw [into_trace] at present
  rcases List.mem_append.mp present with entered | rest
  · exact List.mem_append_left _ entered
  · rcases List.mem_append.mp rest with internal | released
    · have same := nativeSqrt_body_visited input output path visited internal
      exact List.mem_append_right _ (List.mem_singleton.mpr same)
    · exact List.mem_append_left _ (List.mem_reverse.mp released)

/-- The resident peak counts every actual lexical cell and preserves all quantum coordinates. -/
theorem nativeSqrt_into_resident_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into input output).Path) :
    (into input output).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace kind width := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have member := nativeSqrt_into_visited input output path visited present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [additionalSpace, wideContext, rootContext, halfContext,
        candidateContext, squareContext, context, SpacePool.ofShape] <;> omega

/-- Every simultaneously live scratch cell contributes to the actual auxiliary peak. -/
theorem nativeSqrt_into_auxiliary_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into input output).Path) :
    (into input output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace kind width := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have member := nativeSqrt_into_visited input output path visited present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [additionalSpace, wideContext, rootContext, halfContext,
        candidateContext, squareContext, context, SpacePool.ofShape] <;> omega

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
