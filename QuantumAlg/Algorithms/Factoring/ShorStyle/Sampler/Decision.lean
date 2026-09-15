/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Construction

/-!
# Actual GCD decision after first-residue selection

The selected candidate is copied before its latch becomes the default unit.
The accepted arm runs the expanded Euclidean circuit, reuses the extended
word for comparison with the actual default unit, and selects either the
unit copy or the factor copy. The candidate cell becomes the final factor
payload, and the eligibility cell becomes its tag. All constants are formed
by real clearing and increment instructions. The final product is packed by
one actual closed operation into the supplied complete parameter cell.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Clear a real word by XOR with that same stored word. -/
def clearWordOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitXor width ctx
    (.product (FirstAccepted.cellRead output) (FirstAccepted.cellRead output)) output

/-- Clear the real factor tag with a Boolean XOR on its current value. -/
def clearBitOp (output : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (FirstAccepted.cellRead output) (FirstAccepted.cellRead output)) output

/-- Preserve the selected word, build the default unit, and clear the factor tag. -/
def initializeBody (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical (.wordUnary .copy width ctx
    (FirstAccepted.cellRead shared.selector.selected) scratch.candidate))
    (.seq (.classical (clearWordOp shared.selector.selected))
      (.seq (.classical (.wordUnary .increment width ctx
        (FirstAccepted.cellRead shared.selector.selected) shared.selector.selected))
        (.classical (clearBitOp scratch.eligible))))

/-- On a unit proposal, copy the preserved candidate to the unit and clear the factor payload. -/
def unitBody (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical (.wordUnary .copy width ctx
    (FirstAccepted.cellRead scratch.candidate) shared.selector.selected))
    (.classical (clearWordOp scratch.candidate))

/-- On a nonunit proposal, materialize the computed factor and set its initially cleared tag. -/
def factorBody (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .seq (.classical (.wordResize (width + 1) width ctx
    (FirstAccepted.cellRead gcdResult) scratch.candidate))
    (.classical (.bit .not ctx (FirstAccepted.cellRead scratch.eligible) scratch.eligible))

/-- The actual coprimality bit selects precisely the unit or factor instructions. -/
def chooseResult (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .branch (FirstAccepted.cellRead scratch.positive) (fun value =>
    if value.toBool then unitBody shared scratch else factorBody scratch gcdResult)

/-- Compute the GCD, overwrite the now-consumed extended candidate with one, and test equality. -/
def acceptedBody (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .seq (.classical (Proposal.extendOp scratch))
    (.seq (NumberTheory.GCD.lexicalBody
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult)
      (.seq (.classical (.wordResize width (width + 1) ctx
        (FirstAccepted.cellRead shared.selector.selected) scratch.extended))
        (.seq (.classical (.wordBinary .equal (width + 1) ctx
          (.product (FirstAccepted.cellRead gcdResult)
            (FirstAccepted.cellRead scratch.extended)) scratch.positive))
          (chooseResult shared scratch gcdResult))))

/-- A rejected scan keeps the default unit and clears its unused factor payload. -/
def chooseAccepted (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .branch (FirstAccepted.cellRead shared.selector.accepted) (fun value =>
    if value.toBool then acceptedBody shared scratch gcdResult
      else .classical (clearWordOp scratch.candidate))

/-- Pack all three actual output fields without dropping the factor flag or its payload. -/
def packOp (shared : Proposal.SharedRefs ctx width) (scratch : Proposal.ScratchRefs ctx width)
    (output : CWriteRef ctx (ParameterShape width)) :
    ClassicalOp (ParameterShape width) (ParameterShape width) ctx ctx :=
  .packProduct ctx (.product (FirstAccepted.cellRead shared.selector.selected)
    (.product (FirstAccepted.cellRead scratch.eligible)
      (FirstAccepted.cellRead scratch.candidate))) output

/-- Complete actual parameter preparation after the ordered proposal scan. -/
def circuit (shared : Proposal.SharedRefs ctx width) (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) : Circuit ctx ctx :=
  .seq (initializeBody shared scratch)
    (.seq (chooseAccepted shared scratch gcdResult) (.classical (packOp shared scratch output)))

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
