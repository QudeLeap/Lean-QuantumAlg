/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Complete live storage of the actual residue decision

The input layout already contains the GCD result cell. Only the selected
Euclidean arm allocates further storage: two state words, its branch bit and
the live quotient/remainder pair. Every other decision instruction reuses
the existing cells. No extra result word is inserted into this allowance.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem result_visited (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (chooseResult shared scratch gcdResult).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (chooseResult shared scratch gcdResult).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit value =>
      cases value
      all_goals
        change visited ∈ [ctx, ctx] at present
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

private theorem accepted_visited (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (property : RuntimeCtx kind → Prop) (base : property ctx)
    (reduced : ∀ (path : (NumberTheory.GCD.lexicalBody
        (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult).Path)
        (visited : RuntimeCtx kind),
      visited ∈ (NumberTheory.GCD.lexicalBody
        (.product (FirstAccepted.cellRead scratch.extended) shared.modulus)
        gcdResult).visitedContexts path → property visited)
    (path : (acceptedBody shared scratch gcdResult).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (acceptedBody shared scratch gcdResult).visitedContexts path) :
    property visited := by
  change visited ∈ [ctx] ++
    ((NumberTheory.GCD.lexicalBody
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus)
      gcdResult).visitedContexts path.2.1 ++
      ([ctx] ++ ([ctx] ++ (chooseResult shared scratch gcdResult).visitedContexts
        path.2.2.2.2))) at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with same | inner | same | same | selected
  · exact same.symm ▸ base
  · exact reduced path.2.1 visited inner
  · exact same.symm ▸ base
  · exact same.symm ▸ base
  · exact (result_visited shared scratch gcdResult path.2.2.2.2 visited selected).symm ▸ base

private theorem decision_visited (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width))
    (property : RuntimeCtx kind → Prop) (base : property ctx)
    (reduced : ∀ (path : (NumberTheory.GCD.lexicalBody
        (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult).Path)
        (visited : RuntimeCtx kind),
      visited ∈ (NumberTheory.GCD.lexicalBody
        (.product (FirstAccepted.cellRead scratch.extended) shared.modulus)
        gcdResult).visitedContexts path → property visited)
    (path : (circuit shared scratch gcdResult output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (circuit shared scratch gcdResult output).visitedContexts path) :
    property visited := by
  change visited ∈ [ctx, ctx, ctx, ctx] ++
    ((chooseAccepted shared scratch gcdResult).visitedContexts path.2.1 ++ [ctx]) at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rcases present with same | selected | same
  · exact same.symm ▸ base
  · have branchProperty : ∀ (selectedPath : (chooseAccepted shared scratch gcdResult).Path),
        visited ∈ (chooseAccepted shared scratch gcdResult).visitedContexts selectedPath →
          property visited := by
      rintro ⟨value, selectedPath⟩ member
      cases value with
      | bit value =>
          cases value
          · exact (List.mem_singleton.mp member).symm ▸ base
          · exact accepted_visited shared scratch gcdResult property base reduced
              selectedPath visited member
    exact branchProperty path.2.1 selected
  · exact same.symm ▸ base

/-- The complete selected decision needs only the lexical Euclidean resident allowance. -/
theorem decision_resident_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width))
    (path : (circuit shared scratch gcdResult output).Path) :
    (circuit shared scratch gcdResult output).peakResidentSpace path ≤
      ctx.residentSpace + NumberTheory.GCD.lexicalAdditionalSpace kind (width + 1) := by
  apply Circuit.peakResidentSpace_le_of_visited
  apply decision_visited shared scratch gcdResult output
  · intro axis
    exact Nat.le_add_right _ _
  · intro reduced visited present
    exact (Circuit.residentSpace_le_peak_of_visited _ reduced visited present).trans
      (NumberTheory.GCD.gcdLexical_resident_le
        (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult reduced)

/-- The same real path counts every live Euclidean cell in its auxiliary allowance. -/
theorem decision_auxiliary_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width))
    (path : (circuit shared scratch gcdResult output).Path) :
    (circuit shared scratch gcdResult output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + NumberTheory.GCD.lexicalAdditionalSpace kind (width + 1) := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  apply decision_visited shared scratch gcdResult output
  · intro axis
    exact Nat.le_add_right _ _
  · intro reduced visited present
    exact (Circuit.auxiliarySpace_le_peak_of_visited _ reduced visited present).trans
      (NumberTheory.GCD.gcdLexical_auxiliary_le
        (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult reduced)

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
