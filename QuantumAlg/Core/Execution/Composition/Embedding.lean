/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Interpret.Preserving
import all QuantumAlg.Core.Execution.State

/-!
# Recursive execution inside a complete physical frame

Only the interpreter uses the recursive body's result function. The original
child syntax remains an AST node. Complement cells, physical systems and
external reference correlations are retained throughout the coordinate split,
recursive execution and join.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  {Hidden Path : Type} [Fintype Hidden] [Fintype Path]

/-- Keep the complete resident complement around a recursive interpreter call. -/
def embedPreserving (placement : ContextEmbedding localCtx caller) (Reference : Register)
    (body : Preserving Hidden localCtx localCtx
      (Register.prod placement.frame.register Reference) Path) :
    Preserving Hidden caller caller Reference Path := fun state =>
  let split := placement.split state
  let localState := split.mapHistory (fun history =>
    (history.2.1, (history.1, history.2.2)))
  let result := body localState
  let arranged := result.val.mapHistory (fun history =>
    (history.2.1.1, (history.1, (history.2.1.2, history.2.2))))
  ⟨placement.join arranged,
    (placement.contextEmbedding_join_mass arranged).trans
      ((result.val.mapHistory_mass _).trans (result.property.trans
        ((split.mapHistory_mass _).trans (placement.contextEmbedding_split_mass state))))⟩

end

end QuantumAlg.Execution
