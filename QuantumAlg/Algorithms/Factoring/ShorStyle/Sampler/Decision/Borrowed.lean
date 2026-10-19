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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma result_borrowed (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (resultStep (model := model) shared scratch gcdResult store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [decisionResult_store]
  split <;> simp only [unitStore, factorStore, Store.readBorrowedClassical_applyOp]

/-- The actual resize, Euclidean scopes and stored result arm preserve every borrowed value. -/
lemma decisionAccepted_borrowed_values (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (acceptedStep (model := model) shared scratch gcdResult store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [decisionAccepted_store, result_borrowed]
  simp only [comparisonStore, Store.readBorrowedClassical_applyOp]
  exact (NumberTheory.GCD.gcdLexical_borrowed_values (model := model)
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult
    (store.applyOp (Proposal.extendOp scratch))).trans
      (Store.readBorrowedClassical_applyOp store (Proposal.extendOp scratch))

private lemma acceptance_borrowed (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (acceptanceStep (model := model) shared scratch gcdResult store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [decisionAcceptance_store]
  split
  · exact decisionAccepted_borrowed_values (model := model) shared scratch gcdResult store
  · exact Store.readBorrowedClassical_applyOp store (clearWordOp scratch.candidate)

/-- The complete actual initialization, decision and parameter write preserve borrowed values. -/
lemma decision_borrowed_values (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    (step (model := model) shared scratch gcdResult output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  change (((acceptanceStep (model := model) shared scratch gcdResult
    (initializationStore shared scratch store)).1).applyOp
      (packOp shared scratch output)).readBorrowedClassical = _
  rw [Store.readBorrowedClassical_applyOp, acceptance_borrowed]
  simp only [initializationStore, Store.readBorrowedClassical_applyOp]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
