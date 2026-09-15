/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Initialization

/-!
# Reads preserved by the actual residue decision initialization

The four native instructions write only the candidate, selected unit and
factor flag. Every complete structural read excluding those three actual
keys is preserved, independently of all incoming values.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The initialization preserves all complete reads outside its actual three written cells. -/
theorem decisionInitialization_read_other (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (candidateFree : scratch.candidate.key ∉ other.storageKeys)
    (unitFree : shared.selector.selected.key ∉ other.storageKeys)
    (flagFree : scratch.eligible.key ∉ other.storageKeys) (store : Store ctx) :
    (initializationStore shared scratch store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys _ (clearBitOp scratch.eligible)
    other flagFree).trans
      ((Store.read_applyOp_of_not_mem_storageKeys _
        (.wordUnary .increment width ctx (FirstAccepted.cellRead shared.selector.selected)
          shared.selector.selected) other unitFree).trans
        ((Store.read_applyOp_of_not_mem_storageKeys _ (clearWordOp shared.selector.selected)
          other unitFree).trans
          (Store.read_applyOp_of_not_mem_storageKeys store
            (.wordUnary .copy width ctx (FirstAccepted.cellRead shared.selector.selected)
              scratch.candidate) other candidateFree)))

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
