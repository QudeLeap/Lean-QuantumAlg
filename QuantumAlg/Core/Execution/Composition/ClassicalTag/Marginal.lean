/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.ClassicalTag
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Marginal
import all QuantumAlg.Core.Execution.State.History

/-!
# Forgetting decoded service and path tags

Summing a decoded mathematical tag is the partial trace of that external
register, for arbitrary quantum input including off-diagonal tag entries.
The real service state, original history and actual path remain unchanged.
-/

namespace QuantumAlg.Execution.State

noncomputable section

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {Hidden H Path : Type} [Fintype Hidden] [Fintype H] [Fintype Path]

/-- Summing the input tag forgets only that reference subsystem. -/
lemma decodeOracleTag_forgetReferenceFrame
    (state : State ctx (Tag.prod Reference) (Hidden × H)) :
    (decodeOracleTag state).mapHistory (fun record => (record.1, record.2.1)) =
      state.forgetReferenceFrame := by
  calc
    _ = (decodeReferenceTag state).mapHistory Prod.fst := by
      simp only [decodeOracleTag, mapHistory_comp]
      rfl
    _ = _ := decodeReferenceTag_forgetReferenceFrame state

/-- Summing the output tag retains the original history and the same actual path. -/
lemma decodeExecutionTag_forgetReferenceFrame
    (state : State ctx (Tag.prod Reference) (Hidden × (H × Path))) :
    (decodeExecutionTag state).mapHistory
      (fun record => (record.1, (record.2.1.1, record.2.2))) =
      state.forgetReferenceFrame := by
  calc
    _ = (decodeReferenceTag state).mapHistory Prod.fst := by
      simp only [decodeExecutionTag, decodeOracleTag, mapHistory_comp]
      rfl
    _ = _ := decodeReferenceTag_forgetReferenceFrame state

end

end QuantumAlg.Execution.State
