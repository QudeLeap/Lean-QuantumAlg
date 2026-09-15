/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Space
import all QuantumAlg.Components.Classical.NumberTheory.FactorRange.Resources
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Complete live space of actual left-priority half-power recovery

The left and right GCD invocations execute sequentially and release their
own scratch before the next stage. Their peak allowance is therefore one
complete GCD workspace. The range checks and result packaging use the
already present candidate, comparison and payload cells without allocation.
The enclosing six-cell scope is counted separately by its actual owner.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem pack_visited (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (pack cells output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (pack cells output).visitedContexts path) : visited = ctx := by
  change visited ∈ [ctx, ctx] at present
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

private theorem pack_resident_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (pack cells output).Path) :
    (pack cells output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (pack_visited cells output path visited present) ▸ le_rfl

private theorem pack_auxiliary_le (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (pack cells output).Path) :
    (pack cells output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (pack_visited cells output path visited present) ▸ le_rfl

private theorem right_resident_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (right halfPower cells output).Path) :
    (right halfPower cells output).peakResidentSpace path ≤
      ctx.residentSpace + NativeHalfGCD.spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq
    (NativeHalfGCD.code (N := N) true halfPower cells.candidate)
    (.seq (FactorRange.code (checkRefs cells)) (pack cells output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact NativeHalfGCD.code_resident_le true halfPower cells.candidate path.1
  · refine (Circuit.peakResidentSpace_seq (FactorRange.code (checkRefs cells))
      (pack cells output) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (FactorRange.code_resident_le (checkRefs cells) path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · exact (pack_resident_le cells output path.2.2).trans
        (fun _ => Nat.le_add_right _ _)

private theorem right_auxiliary_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (right halfPower cells output).Path) :
    (right halfPower cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + NativeHalfGCD.spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq
    (NativeHalfGCD.code (N := N) true halfPower cells.candidate)
    (.seq (FactorRange.code (checkRefs cells)) (pack cells output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact NativeHalfGCD.code_auxiliary_le true halfPower cells.candidate path.1
  · refine (Circuit.peakAuxiliarySpace_seq (FactorRange.code (checkRefs cells))
      (pack cells output) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (FactorRange.code_auxiliary_le (checkRefs cells) path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · exact (pack_auxiliary_le cells output path.2.2).trans
        (fun _ => Nat.le_add_right _ _)

private theorem choose_resident_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (choose halfPower cells output).Path) :
    (choose halfPower cells output).peakResidentSpace path ≤
      ctx.residentSpace + NativeHalfGCD.spaceBound kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact right_resident_le halfPower cells output path
      · exact (pack_resident_le cells output path).trans (fun _ => Nat.le_add_right _ _)

private theorem choose_auxiliary_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (choose halfPower cells output).Path) :
    (choose halfPower cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + NativeHalfGCD.spaceBound kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact right_auxiliary_le halfPower cells output path
      · exact (pack_auxiliary_le cells output path).trans (fun _ => Nat.le_add_right _ _)

/-- Sequential GCD calls share one complete peak workspace while all existing cells stay live. -/
theorem code_resident_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower cells output).Path) :
    (code halfPower cells output).peakResidentSpace path ≤
      ctx.residentSpace + NativeHalfGCD.spaceBound kind N := by
  refine (Circuit.peakResidentSpace_seq
    (NativeHalfGCD.code (N := N) false halfPower cells.candidate)
    (.seq (FactorRange.code (checkRefs cells)) (choose halfPower cells output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact NativeHalfGCD.code_resident_le false halfPower cells.candidate path.1
  · refine (Circuit.peakResidentSpace_seq (FactorRange.code (checkRefs cells))
      (choose halfPower cells output) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (FactorRange.code_resident_le (checkRefs cells) path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · exact choose_resident_le halfPower cells output path.2.2

/-- All actual temporary GCD roles contribute to the same auxiliary peak bound. -/
theorem code_auxiliary_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower cells output).Path) :
    (code halfPower cells output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + NativeHalfGCD.spaceBound kind N := by
  refine (Circuit.peakAuxiliarySpace_seq
    (NativeHalfGCD.code (N := N) false halfPower cells.candidate)
    (.seq (FactorRange.code (checkRefs cells)) (choose halfPower cells output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact NativeHalfGCD.code_auxiliary_le false halfPower cells.candidate path.1
  · refine (Circuit.peakAuxiliarySpace_seq (FactorRange.code (checkRefs cells))
      (choose halfPower cells output) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (FactorRange.code_auxiliary_le (checkRefs cells) path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · exact choose_auxiliary_le halfPower cells output path.2.2

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
