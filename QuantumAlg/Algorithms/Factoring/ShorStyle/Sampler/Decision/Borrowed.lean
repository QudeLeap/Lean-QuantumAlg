/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Comparison
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Preservation

/-!
# Borrowed values through the real residue decision

The actual Euclidean scopes reuse the canonical GCD preservation theorem.
Every other operation writes an intrinsically writable cell. Both stored
branches preserve all borrowed values for arbitrary incoming storage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem result_borrowed (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (resultStep shared scratch gcdResult store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [decisionResult_store]
  split <;> simp only [unitStore, factorStore, Store.readBorrowedClassical_applyOp]

/-- The actual resize, Euclidean scopes and stored result arm preserve every borrowed value. -/
theorem decisionAccepted_borrowed_values (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (acceptedStep shared scratch gcdResult store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [decisionAccepted_store, result_borrowed]
  simp only [comparisonStore, Store.readBorrowedClassical_applyOp]
  exact (NumberTheory.GCD.gcdLexical_borrowed_values
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult
    (store.applyOp (Proposal.extendOp scratch))).trans
      (Store.readBorrowedClassical_applyOp store (Proposal.extendOp scratch))

private theorem acceptance_borrowed (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (acceptanceStep shared scratch gcdResult store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [decisionAcceptance_store]
  split
  · exact decisionAccepted_borrowed_values shared scratch gcdResult store
  · exact Store.readBorrowedClassical_applyOp store (clearWordOp scratch.candidate)

/-- The complete actual initialization, decision and parameter write preserve borrowed values. -/
theorem decision_borrowed_values (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    (step shared scratch gcdResult output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  change (((acceptanceStep shared scratch gcdResult
    (initializationStore shared scratch store)).1).applyOp
      (packOp shared scratch output)).readBorrowedClassical = _
  rw [Store.readBorrowedClassical_applyOp, acceptance_borrowed]
  simp only [initializationStore, Store.readBorrowedClassical_applyOp]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
