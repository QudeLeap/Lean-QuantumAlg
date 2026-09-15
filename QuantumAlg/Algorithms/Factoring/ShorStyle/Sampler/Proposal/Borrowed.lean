/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Semantics
import all QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!
# Borrowed classical values through the actual proposal scan

The decoder and selector use their shared raw-store preservation theorems.
The four intervening comparisons write only intrinsically writable cells.
This composition applies to every initial store, selected path and width.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- Each real decoded prefix preserves all borrowed classical values. -/
theorem proposalPrefix_borrowed_values (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (store : Store ctx) :
    (prefixStep sample proposal shared scratch store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [prefixStep, comparisonStore, Store.readBorrowedClassical_applyOp]
  exact TerminalDecode.terminalDecode_foldStep_borrowed_values scratch.candidate _ store

/-- The actual first-accepted writes preserve the same complete borrowed values. -/
theorem proposalSlot_borrowed_values (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (store : Store ctx) :
    (slotStep sample proposal shared scratch store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  exact (FirstAccepted.firstAccepted_step_borrowed_values (selectorInputs scratch)
    shared.selector (prefixStep sample proposal shared scratch store).1).trans
      (proposalPrefix_borrowed_values sample proposal shared scratch store)

/-- Every finite actual scan preserves borrowed values in the original proposal order. -/
theorem proposalFold_borrowed_values (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) (store : Store ctx) :
    (foldSteps sample shared scratch proposals store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  induction proposals generalizing store with
  | nil => rfl
  | cons proposal remaining ih =>
      exact (ih (slotStep sample proposal shared scratch store).1).trans
        (proposalSlot_borrowed_values sample proposal shared scratch store)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
