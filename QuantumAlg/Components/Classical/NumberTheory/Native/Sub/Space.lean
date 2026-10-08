/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Circuit
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Base.Accounting.Context
import Lean.Elab.Tactic.Omega

/-!
# Actual live storage of native saturating subtraction

The comparison and selected word operation share one real lexical bit.
The operands and destination are existing cells, even when they alias.
Every visited context therefore fits the original context plus that bit,
with no extra quantum capacity at any dimension or input width.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The independent allowance counts the single actual temporary comparison bit. -/
def additionalSpace (kind : ProblemKind) : SpacePool kind := SpacePool.ofShape .bit

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual entry, two instructions and release visit precisely these four contexts. -/
theorem nativeSub_into_visited (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) left right
      output).Path) :
    (into (model := model) left right output).visitedContexts path = [ctx, context ctx, context
      ctx, ctx] := by
  rcases path with ⟨head, value, tail⟩
  cases value with
  | bit flag => cases flag <;> rfl

/-- The resident peak includes the actual decision bit and every pre-existing live system. -/
theorem nativeSub_into_resident_le (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) left right
      output).Path) :
    (into (model := model) left right output).peakResidentSpace path ≤ ctx.residentSpace +
      additionalSpace model.kind := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [nativeSub_into_visited] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases model <;> cases axis <;> simp [context, additionalSpace, SpacePool.ofShape] <;> omega

/-- The one temporary bit is also charged as actual auxiliary storage for its full live scope. -/
theorem nativeSub_into_auxiliary_le (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) left right
      output).Path) :
    (into (model := model) left right output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace model.kind := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [nativeSub_into_visited] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases model <;> cases axis <;> simp [context, additionalSpace, SpacePool.ofShape] <;> omega

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
