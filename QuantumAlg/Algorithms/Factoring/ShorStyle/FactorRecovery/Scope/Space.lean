/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Complete simultaneous capacity of the actual seven-cell factor scope

The real canonical base and half-power use two modulus-width words. The
optional order, its decoded pair and the zero operand use three phase-width
words together with their actual tag and flag bits. All seven entries remain
live during the complete native order recovery. Their `2m+3t+7` bits are added
to that routine's full simultaneous scratch capacity, including its division
and modular-power workspace. Both entry and release contexts are accounted for.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Every actual outer cell is live simultaneously with the complete recovery workspace. -/
def spaceBound (kind : ProblemKind) (N : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (2 * modulusBits N + 3 * phaseBits N + 7 +
    OrderRecovery.Native.extraClassicalBits (modulusBits N) (phaseBits N)))

private def innerScope (ctx : RuntimeCtx kind) (N : Nat)
    (tail : Circuit (context ctx N) (context ctx N)) :
    Circuit (zeroContext ctx N) (zeroContext ctx N) :=
  .workspace (zeroContext ctx N) (zeroContext ctx N).canonicalFreshKey .bit
    (zeroContext ctx N).canonicalFreshKey_fresh
    (.workspace (activeContext ctx N) (activeContext ctx N).canonicalFreshKey .bit
      (activeContext ctx N).canonicalFreshKey_fresh
      (.workspace (positiveContext ctx N) (positiveContext ctx N).canonicalFreshKey
        (.unsignedWord (modulusBits N)) (positiveContext ctx N).canonicalFreshKey_fresh tail))

private def middleScope (ctx : RuntimeCtx kind) (N : Nat)
    (tail : Circuit (zeroContext ctx N) (zeroContext ctx N)) :
    Circuit (orderContext ctx N) (orderContext ctx N) :=
  .workspace (orderContext ctx N) (orderContext ctx N).canonicalFreshKey
    (.product .bit (.unsignedWord (phaseBits N + 1)))
    (orderContext ctx N).canonicalFreshKey_fresh
    (.workspace (expandedContext ctx N) (expandedContext ctx N).canonicalFreshKey
      (.unsignedWord (phaseBits N + 1)) (expandedContext ctx N).canonicalFreshKey_fresh tail)

private def outerScope (ctx : RuntimeCtx kind) (N : Nat)
    (tail : Circuit (orderContext ctx N) (orderContext ctx N)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.canonicalResidue (modulusBits N))
    ctx.canonicalFreshKey_fresh
    (.workspace (baseContext ctx N) (baseContext ctx N).canonicalFreshKey
      (.option (.unsignedWord (phaseBits N + 1)))
      (baseContext ctx N).canonicalFreshKey_fresh tail)

private theorem strip_context {α : Type} (head : α) (inside : List α) (value : α)
    (present : value ∈ head :: inside ++ [head]) : value = head ∨ value ∈ inside := by
  rcases List.mem_append.mp present with before | after
  · exact List.mem_cons.mp before
  · exact Or.inl (List.mem_singleton.mp after)

private theorem inner_visited (tail : Circuit (context ctx N) (context ctx N))
    (path : tail.Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (innerScope ctx N tail).visitedContexts path) :
    visited ∈ [zeroContext ctx N, activeContext ctx N, positiveContext ctx N] ∨
      visited ∈ tail.visitedContexts path := by
  change visited ∈ zeroContext ctx N :: (activeContext ctx N ::
    (positiveContext ctx N :: tail.visitedContexts path ++ [positiveContext ctx N]) ++
      [activeContext ctx N]) ++ [zeroContext ctx N] at present
  rcases strip_context (zeroContext ctx N) _ visited present with same | later
  · exact Or.inl (List.mem_cons.mpr (Or.inl same))
  rcases strip_context (activeContext ctx N) _ visited later with same | later
  · exact Or.inl (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl same))))
  rcases strip_context (positiveContext ctx N) _ visited later with same | inside
  · exact Or.inl (List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr same)))))
  · exact Or.inr inside

private theorem middle_visited (tail : Circuit (zeroContext ctx N) (zeroContext ctx N))
    (path : tail.Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (middleScope ctx N tail).visitedContexts path) :
    visited ∈ [orderContext ctx N, expandedContext ctx N] ∨
      visited ∈ tail.visitedContexts path := by
  change visited ∈ orderContext ctx N ::
    (expandedContext ctx N :: tail.visitedContexts path ++ [expandedContext ctx N]) ++
      [orderContext ctx N] at present
  rcases strip_context (orderContext ctx N) _ visited present with same | later
  · exact Or.inl (List.mem_cons.mpr (Or.inl same))
  rcases strip_context (expandedContext ctx N) _ visited later with same | inside
  · exact Or.inl (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr same)))
  · exact Or.inr inside

private theorem outer_visited (tail : Circuit (orderContext ctx N) (orderContext ctx N))
    (path : tail.Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (outerScope ctx N tail).visitedContexts path) :
    visited ∈ [ctx, baseContext ctx N] ∨ visited ∈ tail.visitedContexts path := by
  change visited ∈ ctx :: (baseContext ctx N :: tail.visitedContexts path ++
    [baseContext ctx N]) ++ [ctx] at present
  rcases strip_context ctx _ visited present with same | later
  · exact Or.inl (List.mem_cons.mpr (Or.inl same))
  rcases strip_context (baseContext ctx N) _ visited later with same | inside
  · exact Or.inl (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr same)))
  · exact Or.inr inside

private theorem layered_visited (tail : Circuit (context ctx N) (context ctx N))
    (path : tail.Path) (visited : RuntimeCtx kind)
    (present : visited ∈
      (outerScope ctx N (middleScope ctx N (innerScope ctx N tail))).visitedContexts path) :
    visited ∈ [ctx, baseContext ctx N, orderContext ctx N, expandedContext ctx N,
      zeroContext ctx N, activeContext ctx N, positiveContext ctx N] ∨
      visited ∈ tail.visitedContexts path := by
  rcases outer_visited (ctx := ctx) (N := N)
    (middleScope ctx N (innerScope ctx N tail)) path visited present with first | later
  · exact Or.inl (List.mem_append_left
      [orderContext ctx N, expandedContext ctx N, zeroContext ctx N,
        activeContext ctx N, positiveContext ctx N] first)
  rcases middle_visited (ctx := ctx) (N := N)
    (innerScope ctx N tail) path visited later with second | later
  · exact Or.inl (List.mem_append_right [ctx, baseContext ctx N]
      (List.mem_append_left [zeroContext ctx N, activeContext ctx N, positiveContext ctx N] second))
  rcases inner_visited (ctx := ctx) (N := N) tail path visited later with third | inside
  · exact Or.inl (List.mem_append_right
      [ctx, baseContext ctx N, orderContext ctx N, expandedContext ctx N] third)
  · exact Or.inr inside

private theorem code_visited (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source parameter phase output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (code source parameter phase output).visitedContexts path) :
    visited ∈ [ctx, baseContext ctx N, orderContext ctx N, expandedContext ctx N,
      zeroContext ctx N, activeContext ctx N, positiveContext ctx N] ∨
      visited ∈ (body source parameter phase output).visitedContexts path :=
  layered_visited (ctx := ctx) (N := N) (body source parameter phase output) path visited present

private theorem prefix_resident_capacity (visited : RuntimeCtx kind)
    (present : visited ∈ [ctx, baseContext ctx N, orderContext ctx N, expandedContext ctx N,
      zeroContext ctx N, activeContext ctx N, positiveContext ctx N]) :
    visited.residentSpace ≤ ctx.residentSpace + spaceBound kind N := by
  intro axis
  have capacities : ∀ entry ∈ [ctx, baseContext ctx N, orderContext ctx N, expandedContext ctx N,
      zeroContext ctx N, activeContext ctx N, positiveContext ctx N],
      entry.residentSpace axis ≤ (ctx.residentSpace + spaceBound kind N) axis := by
    cases axis <;>
      simp [positiveContext, activeContext, zeroContext, expandedContext, orderContext, baseContext,
        spaceBound, SpacePool.ofShape]
    all_goals omega
  exact capacities visited present

private theorem full_resident_capacity :
    (context ctx N).residentSpace + NativeFactorTail.spaceBound kind N ≤
      ctx.residentSpace + spaceBound kind N := by
  intro axis
  cases axis <;>
    simp [context, positiveContext, activeContext, zeroContext, expandedContext, orderContext,
      baseContext, NativeFactorTail.spaceBound, spaceBound, SpacePool.ofShape]
  all_goals omega

/-- Every outer entry remains included while the complete resident recovery scratch is live. -/
theorem code_resident_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source parameter phase output).Path) :
    (code source parameter phase output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound kind N := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases code_visited source parameter phase output path visited present with outer | inner
  · exact prefix_resident_capacity visited outer
  · exact (Circuit.residentSpace_le_peak_of_visited
      (body source parameter phase output) path visited inner).trans
        ((NativeFactorTail.code_resident_le source (liftInput parameter) (liftInput phase)
          (cells ctx N) (liftWrite output) path).trans full_resident_capacity)

private theorem prefix_auxiliary_capacity (visited : RuntimeCtx kind)
    (present : visited ∈ [ctx, baseContext ctx N, orderContext ctx N, expandedContext ctx N,
      zeroContext ctx N, activeContext ctx N, positiveContext ctx N]) :
    visited.auxiliarySpace ≤ ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  have capacities : ∀ entry ∈ [ctx, baseContext ctx N, orderContext ctx N, expandedContext ctx N,
      zeroContext ctx N, activeContext ctx N, positiveContext ctx N],
      entry.auxiliarySpace axis ≤ (ctx.auxiliarySpace + spaceBound kind N) axis := by
    cases axis <;>
      simp [positiveContext, activeContext, zeroContext, expandedContext, orderContext, baseContext,
        spaceBound, SpacePool.ofShape]
    all_goals omega
  exact capacities visited present

private theorem full_auxiliary_capacity :
    (context ctx N).auxiliarySpace + NativeFactorTail.spaceBound kind N ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  cases axis <;>
    simp [context, positiveContext, activeContext, zeroContext, expandedContext, orderContext,
      baseContext, NativeFactorTail.spaceBound, spaceBound, SpacePool.ofShape]
  all_goals omega

/-- Every outer entry remains included while the complete auxiliary recovery scratch is live. -/
theorem code_auxiliary_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code source parameter phase output).Path) :
    (code source parameter phase output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases code_visited source parameter phase output path visited present with outer | inner
  · exact prefix_auxiliary_capacity visited outer
  · exact (Circuit.auxiliarySpace_le_peak_of_visited
      (body source parameter phase output) path visited inner).trans
        ((NativeFactorTail.code_auxiliary_le source (liftInput parameter) (liftInput phase)
          (cells ctx N) (liftWrite output) path).trans full_auxiliary_capacity)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
