/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Space
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Core.Execution.Trace.Composition
import Mathlib.Tactic.Tauto

/-!
# All simultaneous workspace of the actual six-cell factor scope

The candidate, one, modulus, two comparison bits and payload remain live
during each GCD. Those cells use `4m+5` bits, and the complete nested GCD uses
another `6m+7`. Their simultaneous peak is therefore bounded by `10m+12`
additional classical bits. Original resident and auxiliary roles are retained
through every actual entry, selected arm and matching release.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Six outer cells together with all live GCD work; no result or division scratch is omitted. -/
def spaceBound (kind : ProblemKind) (N : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (10 * modulusBits N + 12))

private theorem body_resident_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (body halfPower output).Path) :
    (body halfPower output).peakResidentSpace path ≤
      (context ctx N).residentSpace + NativeHalfGCD.spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq (ConstantWord.circuit (oneRef ctx N) 1)
    (.seq (ConstantWord.circuit (modulusRef ctx N) N)
      (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output)))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (ConstantWord.constantWord_resident_le (oneRef ctx N) 1 path.1).trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakResidentSpace_seq (ConstantWord.circuit (modulusRef ctx N) N)
      (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (ConstantWord.constantWord_resident_le (modulusRef ctx N) N path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · exact NativeHalfFactor.code_resident_le
        (liftInput halfPower) (cells ctx N) (liftWrite output) path.2.2

private theorem body_auxiliary_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (body halfPower output).Path) :
    (body halfPower output).peakAuxiliarySpace path ≤
      (context ctx N).auxiliarySpace + NativeHalfGCD.spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq (ConstantWord.circuit (oneRef ctx N) 1)
    (.seq (ConstantWord.circuit (modulusRef ctx N) N)
      (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output)))
    path).le.trans ?_
  apply SpacePool.max_le
  · exact (ConstantWord.constantWord_auxiliary_le (oneRef ctx N) 1 path.1).trans
      (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakAuxiliarySpace_seq (ConstantWord.circuit (modulusRef ctx N) N)
      (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output))
      path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (ConstantWord.constantWord_auxiliary_le (modulusRef ctx N) N path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · exact NativeHalfFactor.code_auxiliary_le
        (liftInput halfPower) (cells ctx N) (liftWrite output) path.2.2

set_option maxHeartbeats 800000 in
-- Elaborating the six actual dependent allocation contexts repeatedly checks their fresh-key
-- transports. Keep that finite elaboration allowance local to this actual trace-membership bridge.
private theorem code_visited (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (code halfPower output).visitedContexts path) :
    visited ∈ [ctx, candidateContext ctx N, oneContext ctx N, modulusContext ctx N,
      lowerContext ctx N, upperContext ctx N] ∨
      visited ∈ (body halfPower output).visitedContexts path := by
  change visited ∈ (ctx) :: ((candidateContext ctx N) :: ((oneContext ctx N) :: ((modulusContext
    ctx N) :: ((lowerContext ctx N) :: ((upperContext ctx N) :: ((body halfPower
    output).visitedContexts path ++ [upperContext ctx N]) ++ [lowerContext ctx N]) ++
    [modulusContext ctx N]) ++ [oneContext ctx N]) ++ [candidateContext ctx N]) ++ [ctx])
    at present
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem prefix_resident_capacity (visited : RuntimeCtx kind)
    (present : visited ∈ [ctx, candidateContext ctx N, oneContext ctx N, modulusContext ctx N,
      lowerContext ctx N, upperContext ctx N]) :
    visited.residentSpace ≤ ctx.residentSpace + spaceBound kind N := by
  intro axis
  have capacities : ∀ entry ∈ [ctx, candidateContext ctx N, oneContext ctx N, modulusContext ctx N,
      lowerContext ctx N, upperContext ctx N],
      entry.residentSpace axis ≤ (ctx.residentSpace + spaceBound kind N) axis := by
    cases axis <;>
      simp [upperContext, lowerContext, modulusContext, oneContext, candidateContext,
        spaceBound, SpacePool.ofShape]
    all_goals omega
  exact capacities visited present

private theorem full_resident_capacity :
    (context ctx N).residentSpace + NativeHalfGCD.spaceBound kind N ≤
      ctx.residentSpace + spaceBound kind N := by
  intro axis
  cases axis <;>
    simp [context, upperContext, lowerContext, modulusContext, oneContext, candidateContext,
      NativeHalfGCD.spaceBound, spaceBound, SpacePool.ofShape]
  all_goals omega

/-- The actual resident peak includes every outer entry while nested division cells are live. -/
theorem code_resident_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower output).Path) :
    (code halfPower output).peakResidentSpace path ≤ ctx.residentSpace + spaceBound kind N := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases code_visited halfPower output path visited present with outer | inner
  · exact prefix_resident_capacity visited outer
  · exact (Circuit.residentSpace_le_peak_of_visited
      (body halfPower output) path visited inner).trans
        ((body_resident_le halfPower output path).trans full_resident_capacity)

private theorem prefix_auxiliary_capacity (visited : RuntimeCtx kind)
    (present : visited ∈ [ctx, candidateContext ctx N, oneContext ctx N, modulusContext ctx N,
      lowerContext ctx N, upperContext ctx N]) :
    visited.auxiliarySpace ≤ ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  have capacities : ∀ entry ∈ [ctx, candidateContext ctx N, oneContext ctx N, modulusContext ctx N,
      lowerContext ctx N, upperContext ctx N],
      entry.auxiliarySpace axis ≤ (ctx.auxiliarySpace + spaceBound kind N) axis := by
    cases axis <;>
      simp [upperContext, lowerContext, modulusContext, oneContext, candidateContext,
        spaceBound, SpacePool.ofShape]
    all_goals omega
  exact capacities visited present

private theorem full_auxiliary_capacity :
    (context ctx N).auxiliarySpace + NativeHalfGCD.spaceBound kind N ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  cases axis <;>
    simp [context, upperContext, lowerContext, modulusContext, oneContext, candidateContext,
      NativeHalfGCD.spaceBound, spaceBound, SpacePool.ofShape]
  all_goals omega

/-- The actual auxiliary peak includes every outer entry while nested division cells are live. -/
theorem code_auxiliary_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower output).Path) :
    (code halfPower output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace + spaceBound kind N := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases code_visited halfPower output path visited present with outer | inner
  · exact prefix_auxiliary_capacity visited outer
  · exact (Circuit.auxiliarySpace_le_peak_of_visited
      (body halfPower output) path visited inner).trans
        ((body_auxiliary_le halfPower output path).trans full_auxiliary_capacity)

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
