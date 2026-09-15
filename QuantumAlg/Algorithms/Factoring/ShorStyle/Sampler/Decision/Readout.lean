/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Arms
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Initialization

/-!
# Complete fields written by the residue decision arms

The unit arm copies the original candidate and clears the payload. The factor
arm stores the actual computed GCD with the instruction's finite-width
interpretation and negates its real incoming tag. Key inequalities here are
internal layout obligations; the sampler's actual fresh cells discharge them.
No arm assumes a clean temporary or computes through a read reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- All parameter fields as a mathematical observation of their actual stored values. -/
def fields (shared : Proposal.SharedRefs ctx width) (scratch : Proposal.ScratchRefs ctx width)
    (store : Store ctx) : (ParameterShape width).Value :=
  .product (store.read (FirstAccepted.cellRead shared.selector.selected))
    (.product (store.read (FirstAccepted.cellRead scratch.eligible))
      (store.read (FirstAccepted.cellRead scratch.candidate)))

/-- The real packing operation writes the complete parameter, including both factor fields. -/
theorem decisionPack_read (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    (store.applyOp (packOp shared scratch output)).read (FirstAccepted.cellRead output) =
      fields shared scratch store :=
  Store.read_applyOp_output store (packOp shared scratch output)

/-- The real unit arm copies the candidate and clears only its factor payload. -/
theorem decisionUnit_fields (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (candidateUnit : scratch.candidate.key ≠ shared.selector.selected.key)
    (candidateFlag : scratch.candidate.key ≠ scratch.eligible.key)
    (unitFlag : shared.selector.selected.key ≠ scratch.eligible.key) (store : Store ctx) :
    fields shared scratch (unitStore shared scratch store) =
      .product (store.read (FirstAccepted.cellRead scratch.candidate))
        (.product (store.read (FirstAccepted.cellRead scratch.eligible))
          (CShape.wordOfNat width 0)) := by
  let copy : ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
    .wordUnary .copy width ctx (FirstAccepted.cellRead scratch.candidate)
      shared.selector.selected
  let copied := store.applyOp copy
  have copiedRead : copied.read (FirstAccepted.cellRead shared.selector.selected) =
      store.read (FirstAccepted.cellRead scratch.candidate) :=
    Store.read_applyOp_output store copy
  have unitRead : (unitStore shared scratch store).read
      (FirstAccepted.cellRead shared.selector.selected) =
        store.read (FirstAccepted.cellRead scratch.candidate) :=
    (Store.read_write_other copied (clearWordOp scratch.candidate).outputRef
      shared.selector.selected.toCStorageRef _ candidateUnit).trans copiedRead
  have flagRead : (unitStore shared scratch store).read
      (FirstAccepted.cellRead scratch.eligible) =
        store.read (FirstAccepted.cellRead scratch.eligible) :=
    (Store.read_write_other copied (clearWordOp scratch.candidate).outputRef
      scratch.eligible.toCStorageRef _ candidateFlag).trans
        (Store.read_write_other store copy.outputRef scratch.eligible.toCStorageRef _ unitFlag)
  have payloadRead : (unitStore shared scratch store).read
      (FirstAccepted.cellRead scratch.candidate) = CShape.wordOfNat width 0 :=
    decision_clearWord_read scratch.candidate copied
  unfold fields
  rw [unitRead, flagRead, payloadRead]

/-- The real factor arm preserves the unit and writes the resized GCD and negated incoming tag. -/
theorem decisionFactor_fields (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (candidateUnit : scratch.candidate.key ≠ shared.selector.selected.key)
    (flagUnit : scratch.eligible.key ≠ shared.selector.selected.key)
    (flagCandidate : scratch.eligible.key ≠ scratch.candidate.key) (store : Store ctx) :
    fields shared scratch (factorStore scratch gcdResult store) =
      .product (store.read (FirstAccepted.cellRead shared.selector.selected))
        (.product (.bit (!(store.read (FirstAccepted.cellRead scratch.eligible)).toBool))
          (CShape.wordOfNat width (store.read (FirstAccepted.cellRead gcdResult)).toNat)) := by
  let resize : ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord width) ctx ctx :=
    .wordResize (width + 1) width ctx (FirstAccepted.cellRead gcdResult) scratch.candidate
  let negate : ClassicalOp .bit .bit ctx ctx :=
    .bit .not ctx (FirstAccepted.cellRead scratch.eligible) scratch.eligible
  let copied := store.applyOp resize
  have copiedRead : copied.read (FirstAccepted.cellRead scratch.candidate) =
      CShape.wordOfNat width (store.read (FirstAccepted.cellRead gcdResult)).toNat :=
    Store.read_applyOp_output store resize
  have payloadRead : (factorStore scratch gcdResult store).read
      (FirstAccepted.cellRead scratch.candidate) =
        CShape.wordOfNat width (store.read (FirstAccepted.cellRead gcdResult)).toNat :=
    (Store.read_write_other copied negate.outputRef scratch.candidate.toCStorageRef _
      flagCandidate).trans copiedRead
  have unitRead : (factorStore scratch gcdResult store).read
      (FirstAccepted.cellRead shared.selector.selected) =
        store.read (FirstAccepted.cellRead shared.selector.selected) :=
    (Store.read_write_other copied negate.outputRef shared.selector.selected.toCStorageRef _
      flagUnit).trans (Store.read_write_other store resize.outputRef
        shared.selector.selected.toCStorageRef _ candidateUnit)
  have flagBefore : copied.read (FirstAccepted.cellRead scratch.eligible) =
      store.read (FirstAccepted.cellRead scratch.eligible) :=
    Store.read_write_other store resize.outputRef scratch.eligible.toCStorageRef _
      flagCandidate.symm
  have flagRead : (factorStore scratch gcdResult store).read
      (FirstAccepted.cellRead scratch.eligible) =
        .bit (!(store.read (FirstAccepted.cellRead scratch.eligible)).toBool) := by
    have actual := Store.read_applyOp_output copied negate
    change (factorStore scratch gcdResult store).read (FirstAccepted.cellRead scratch.eligible) =
      Resource.BitOpcode.eval .not
        (copied.read (FirstAccepted.cellRead scratch.eligible)) at actual
    rw [flagBefore] at actual
    cases value : store.read (FirstAccepted.cellRead scratch.eligible) with
    | bit bit =>
        rw [value] at actual
        exact actual
  unfold fields
  rw [unitRead, flagRead, payloadRead]

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
