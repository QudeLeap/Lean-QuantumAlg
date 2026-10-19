/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.ClassicalTag.State
import all QuantumAlg.Core.Execution.State.Marginal

/-!
# Local observations of a classical spectator encoded in the reference

Forgetting the external tag sums the same complete density blocks as
forgetting its classical label. The old quantum reference is retained in the
stronger identity. Tracing it afterwards yields the identical unconditional
local joint state, with no normalized-slice or independence premise.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {H : Type} [Fintype H]

/-- Forgetting a decoded tag equals its partial trace, retaining the complete old reference. -/
lemma decodeReferenceTag_forgetReferenceFrame
    (state : State ctx (Tag.prod Reference) H) :
    (decodeReferenceTag state).mapHistory Prod.fst = state.forgetReferenceFrame := by
  have reassociated : (decodeReferenceTag state).mapHistory Prod.fst =
      (ExecutionState.decodeClassicalTag
        (state.reindex (S := Tag.prod (ctx.register.prod Reference))
          (referenceTagBasis (ctx := ctx) (Reference := Reference) (Tag := Tag)))).mapClassical
            Prod.fst := by
    simp only [decodeReferenceTag, mapHistory,
      ExecutionState.executionState_mapClassical_comp]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  rw [reassociated]
  apply ExecutionState.ext
  intro record
  apply DensityOperator.ext
  ext row column
  let exposed := state.reindex (S := Tag.prod (ctx.register.prod Reference))
    (referenceTagBasis (ctx := ctx) (Reference := Reference) (Tag := Tag))
  calc
    _ = ∑ tag : Tag.Index, (exposed.block record).matrix (tag, row) (tag, column) := by
      refine Eq.trans ?_
        (ExecutionState.decodeClassicalTag_forget_entry
          (R := ctx.register.prod Reference) (Tag := Tag) exposed record row column)
      exact congrArg (fun current : ExecutionState (Store ctx × H)
          (ctx.register.prod Reference) => (current.block record).matrix row column)
        (ExecutionState.executionState_mapClassical_congr _ rfl)
    _ = _ := by
      rw [ExecutionState.executionState_forgetReferenceFrame_entry]
      rfl

/-- Encoding and then tracing the tag equals forgetting only its original classical label. -/
lemma encodeReferenceTag_forgetReferenceFrame
    (state : State ctx Reference (H × Tag.Index)) :
    (encodeReferenceTag state).forgetReferenceFrame = state.mapHistory Prod.fst := by
  rw [← decodeReferenceTag_forgetReferenceFrame, decode_encodeReferenceTag]

/-- Local admission sees exactly the original joint state after the spectator is forgotten. -/
lemma encodeReferenceTag_marginalLeft
    (state : State ctx Reference (H × Tag.Index)) :
    (encodeReferenceTag state).marginalLeft =
      state.marginalLeft.mapClassical (fun record => (record.1, record.2.1)) := by
  rw [← ExecutionState.executionState_forgetReferenceFrame_marginal (encodeReferenceTag state),
    encodeReferenceTag_forgetReferenceFrame]
  exact ExecutionState.executionState_marginalLeft_mapClassical state _

end

end QuantumAlg.Execution.State
