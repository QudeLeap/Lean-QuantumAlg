/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Comparison
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Initialization.Readout

/-!
# Caller reads preserved by the actual residue decision

Each branch writes only its real candidate, unit, flag, extended word, test
bit and GCD result, followed by the complete parameter output. Reads outside
these actual cells survive for arbitrary stores and arbitrary selected paths.
The enclosing concrete layout discharges the key conditions structurally.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem result_read_other (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    {shape : CShape} (other : CInputRef ctx shape)
    (candidateFree : scratch.candidate.key ∉ other.storageKeys)
    (unitFree : shared.selector.selected.key ∉ other.storageKeys)
    (flagFree : scratch.eligible.key ∉ other.storageKeys) (store : Store ctx) :
    (resultStep shared scratch gcdResult store).1.read other = store.read other := by
  rw [decisionResult_store]
  split
  · exact (Store.read_applyOp_of_not_mem_storageKeys _ (clearWordOp scratch.candidate)
      other candidateFree).trans
        (Store.read_applyOp_of_not_mem_storageKeys store
          (.wordUnary .copy width ctx (FirstAccepted.cellRead scratch.candidate)
            shared.selector.selected) other unitFree)
  · exact (Store.read_applyOp_of_not_mem_storageKeys _
      (.bit .not ctx (FirstAccepted.cellRead scratch.eligible) scratch.eligible)
      other flagFree).trans
        (Store.read_applyOp_of_not_mem_storageKeys store
          (.wordResize (width + 1) width ctx (FirstAccepted.cellRead gcdResult)
            scratch.candidate) other candidateFree)

private theorem accepted_read_other (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    {shape : CShape} (other : CInputRef ctx shape)
    (candidateFree : scratch.candidate.key ∉ other.storageKeys)
    (unitFree : shared.selector.selected.key ∉ other.storageKeys)
    (flagFree : scratch.eligible.key ∉ other.storageKeys)
    (extendedFree : scratch.extended.key ∉ other.storageKeys)
    (positiveFree : scratch.positive.key ∉ other.storageKeys)
    (gcdFree : gcdResult.key ∉ other.storageKeys) (store : Store ctx) :
    (acceptedStep shared scratch gcdResult store).1.read other = store.read other := by
  rw [decisionAccepted_store]
  exact (result_read_other shared scratch gcdResult other candidateFree unitFree flagFree
    (comparisonStore shared scratch gcdResult (reducedStore shared scratch gcdResult store))).trans
      ((decisionComparison_read_other shared scratch gcdResult other extendedFree positiveFree
        (reducedStore shared scratch gcdResult store)).trans
        (decisionReduction_read_other shared scratch gcdResult other extendedFree gcdFree store))

/-- The complete native decision preserves all reads outside its actual written cells. -/
theorem decision_read_other (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) {shape : CShape}
    (other : CInputRef ctx shape)
    (candidateFree : scratch.candidate.key ∉ other.storageKeys)
    (unitFree : shared.selector.selected.key ∉ other.storageKeys)
    (flagFree : scratch.eligible.key ∉ other.storageKeys)
    (extendedFree : scratch.extended.key ∉ other.storageKeys)
    (positiveFree : scratch.positive.key ∉ other.storageKeys)
    (gcdFree : gcdResult.key ∉ other.storageKeys)
    (outputFree : output.key ∉ other.storageKeys) (store : Store ctx) :
    (step shared scratch gcdResult output store).1.read other = store.read other := by
  let initialized := initializationStore shared scratch store
  change (((acceptanceStep shared scratch gcdResult initialized).1).applyOp
    (packOp shared scratch output)).read other = _
  refine (Store.read_applyOp_of_not_mem_storageKeys _ (packOp shared scratch output)
    other outputFree).trans ?_
  rw [decisionAcceptance_store]
  have initializationRead := decisionInitialization_read_other shared scratch other
    candidateFree unitFree flagFree store
  split
  · exact (accepted_read_other shared scratch gcdResult other candidateFree unitFree flagFree
      extendedFree positiveFree gcdFree initialized).trans initializationRead
  · exact (Store.read_applyOp_of_not_mem_storageKeys initialized (clearWordOp scratch.candidate)
      other candidateFree).trans initializationRead

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
