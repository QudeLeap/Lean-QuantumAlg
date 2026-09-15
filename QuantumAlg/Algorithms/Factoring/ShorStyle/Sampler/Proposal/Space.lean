/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Resources

/-!
# Actual live context of the source proposal scan

The addressed decoder, four comparison instructions and first-accepted
writes allocate no storage. Every context visited by any finite scan is its
original caller context, including both selector paths and width zero.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- The actual decoding and comparison prefix visits only its original live context. -/
theorem proposalPrefix_visited (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (prefixBody sample proposal shared scratch).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (prefixBody sample proposal shared scratch).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (TerminalDecode.intoFromBitRefs .littleEndian
    (PackedSample.proposalRefs sample proposal) scratch.candidate).visitedContexts path.1 ++
      [ctx, ctx, ctx, ctx] at present
  rcases List.mem_append.mp present with decoding | comparison
  · exact TerminalDecode.terminalDecode_fold_visited scratch.candidate
      (List.ofFn (fun index => PackedSample.proposalRefs sample proposal
        (TerminalDecode.sourceIndex .littleEndian index))) path.1 visited decoding
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using comparison

/-- Both actual latch paths reuse only the original proposal cells. -/
theorem proposalSlot_visited (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (slot sample proposal shared scratch).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (slot sample proposal shared scratch).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (prefixBody sample proposal shared scratch).visitedContexts path.1 ++
    (FirstAccepted.circuit (selectorInputs scratch) shared.selector).visitedContexts path.2
    at present
  rcases List.mem_append.mp present with first | selected
  · exact proposalPrefix_visited sample proposal shared scratch path.1 visited first
  · exact FirstAccepted.firstAccepted_visited (selectorInputs scratch) shared.selector
      path.2 visited selected

/-- Every finite actual proposal fold visits the same caller context. -/
theorem proposalFold_visited (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) :
    ∀ (path : (foldSlots sample shared scratch proposals).Path) (visited : RuntimeCtx kind),
      visited ∈ (foldSlots sample shared scratch proposals).visitedContexts path →
        visited = ctx := by
  induction proposals with
  | nil => intro path visited present; exact List.mem_singleton.mp present
  | cons proposal remaining ih =>
      intro path visited present
      change visited ∈ (slot sample proposal shared scratch).visitedContexts path.1 ++
        (foldSlots sample shared scratch remaining).visitedContexts path.2 at present
      rcases List.mem_append.mp present with first | later
      · exact proposalSlot_visited sample proposal shared scratch path.1 visited first
      · exact ih path.2 visited later

/-- The complete source scan needs no additional resident storage. -/
theorem proposalScan_resident_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (scan sample shared scratch).Path) :
    (scan sample shared scratch).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (proposalFold_visited sample shared scratch
    (List.ofFn (fun proposal : Fin count => proposal)) path visited present) ▸ le_rfl

/-- The auxiliary peak is bounded by the already present roles of those same cells. -/
theorem proposalScan_auxiliary_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (scan sample shared scratch).Path) :
    (scan sample shared scratch).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (proposalFold_visited sample shared scratch
    (List.ofFn (fun proposal : Fin count => proposal)) path visited present) ▸ le_rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
