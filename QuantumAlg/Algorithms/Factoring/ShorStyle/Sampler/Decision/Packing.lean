/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Readout

/-!
# Final parameter packing and the actual rejected branch

The final write reads all three fields before changing its destination. A
rejected scan executes its real payload clear and preserves the stored unit
and flag; initialization has already supplied their default values.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The rejected arm executes one payload clear while preserving the full unit and tag values. -/
theorem decisionRejected_fields (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (candidateUnit : scratch.candidate.key ≠ shared.selector.selected.key)
    (candidateFlag : scratch.candidate.key ≠ scratch.eligible.key) (store : Store ctx) :
    fields shared scratch (store.applyOp (clearWordOp scratch.candidate)) =
      .product (store.read (FirstAccepted.cellRead shared.selector.selected))
        (.product (store.read (FirstAccepted.cellRead scratch.eligible))
          (CShape.wordOfNat width 0)) := by
  have unitRead : (store.applyOp (clearWordOp scratch.candidate)).read
      (FirstAccepted.cellRead shared.selector.selected) =
        store.read (FirstAccepted.cellRead shared.selector.selected) :=
    Store.read_write_other store (clearWordOp scratch.candidate).outputRef
      shared.selector.selected.toCStorageRef _ candidateUnit
  have flagRead : (store.applyOp (clearWordOp scratch.candidate)).read
      (FirstAccepted.cellRead scratch.eligible) =
        store.read (FirstAccepted.cellRead scratch.eligible) :=
    Store.read_write_other store (clearWordOp scratch.candidate).outputRef
      scratch.eligible.toCStorageRef _ candidateFlag
  unfold fields
  rw [unitRead, flagRead, decision_clearWord_read]

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Complete output read of the actual initialization, acceptance branch and final pack. -/
theorem decision_read (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    (step (model := model) shared scratch gcdResult output store).1.read
      (FirstAccepted.cellRead output) =
      fields shared scratch
        (acceptanceStep (model := model) shared scratch gcdResult
          (initializationStore shared scratch store)).1 :=
  decisionPack_read shared scratch output _


end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
