/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Layout
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Space of the actual eleven sampler cells

The exact storage contribution is five width-many words and nine further
classical bits. Each partial allocation stage uses no more storage than the
complete inner context. All pre-existing quantum-dimension coordinates and
their original resident and auxiliary roles are retained.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

variable {kind : ProblemKind}

/-- Independent capacity of the eleven actual cells in the sampler layout. -/
def cellSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (5 * width + 9))

/-- The actual allocation stages, including the caller before the first allocation. -/
def stages (ctx : RuntimeCtx kind) (width : Nat) : List (RuntimeCtx kind) :=
  [ctx, modulusCtx ctx width, gcdCtx ctx width, candidateCtx ctx width,
    extendedCtx ctx width, positiveCtx ctx width, belowCtx ctx width,
    eligibleCtx ctx width, acceptedCtx ctx width, selectedCtx ctx width,
    availableCtx ctx width, context ctx width]

/-- All eleven actual cells contribute exactly their encoded widths to resident space. -/
lemma samplerLayout_residentSpace (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).residentSpace = ctx.residentSpace + cellSpace kind width := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [context, availableCtx, selectedCtx, acceptedCtx, eligibleCtx, belowCtx,
      positiveCtx, extendedCtx, candidateCtx, gcdCtx, modulusCtx,
      cellSpace, SpacePool.ofShape]; omega

/-- The real cells all have lexical workspace roles and contribute the same auxiliary width. -/
lemma samplerLayout_auxiliarySpace (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).auxiliarySpace = ctx.auxiliarySpace + cellSpace kind width := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [context, availableCtx, selectedCtx, acceptedCtx, eligibleCtx, belowCtx,
      positiveCtx, extendedCtx, candidateCtx, gcdCtx, modulusCtx,
      cellSpace, SpacePool.ofShape]; omega

/-- Every actual partial allocation fits the complete layout's resident space. -/
lemma samplerLayout_stage_resident_le (ctx : RuntimeCtx kind) (width : Nat)
    (visited : RuntimeCtx kind) (present : visited ∈ stages ctx width) :
    visited.residentSpace ≤ (context ctx width).residentSpace := by
  simp only [stages, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [context, availableCtx, selectedCtx, acceptedCtx, eligibleCtx, belowCtx,
        positiveCtx, extendedCtx, candidateCtx, gcdCtx, modulusCtx, SpacePool.ofShape] <;> omega

/-- Every actual partial allocation fits the complete layout's auxiliary space. -/
lemma samplerLayout_stage_auxiliary_le (ctx : RuntimeCtx kind) (width : Nat)
    (visited : RuntimeCtx kind) (present : visited ∈ stages ctx width) :
    visited.auxiliarySpace ≤ (context ctx width).auxiliarySpace := by
  simp only [stages, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [context, availableCtx, selectedCtx, acceptedCtx, eligibleCtx, belowCtx,
        positiveCtx, extendedCtx, candidateCtx, gcdCtx, modulusCtx, SpacePool.ofShape] <;> omega

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout
