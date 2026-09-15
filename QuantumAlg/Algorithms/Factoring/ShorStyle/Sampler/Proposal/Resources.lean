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
# Native coordinate budgets of the actual proposal scan

One slot allows a shift and selected increment per decoded bit, four explicit
comparison instructions, and the four-event selector allowance. Their native
coordinates include the actual word widths. The total allowance is
`count * (2 * width + 8)` events; an individual path can execute fewer events.
The random draw and later GCD decision are separate real stages.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- Literal comparison suffix: resize, two strict comparisons and conjunction. -/
def comparisonEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize width (width + 1)),
    .classicalOperation (.wordBinary .lessThan (width + 1)),
    .classicalOperation (.wordBinary .lessThan (width + 1)),
    .classicalOperation (.bit .and)]

/-- Independent allowance for decoding one proposal and computing its eligibility. -/
def prefixEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  TerminalDecode.envelope width + ResourcePool.ofList (comparisonEvents kind width)

/-- Independent native allowance for one complete proposal and first-accepted step. -/
def slotEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  prefixEnvelope kind width + FirstAccepted.nativeEnvelope kind width

/-- Exactly one independent slot allowance for each original source proposal. -/
def scanEnvelope (kind : ProblemKind) (width count : Nat) : ResourcePool kind :=
  ResourcePool.scale count (slotEnvelope kind width)

/-- The actual comparison suffix emits exactly its four named native coordinates. -/
theorem proposalComparison_eventTrace (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (path : (comparisonBody shared scratch).Path) :
    (comparisonBody shared scratch).eventTrace path = comparisonEvents kind width := rfl

/-- Actual decoding and comparisons fit their independent native-coordinate budget. -/
theorem proposalPrefix_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (prefixBody sample proposal shared scratch).Path) :
    (prefixBody sample proposal shared scratch).resourcePool path ≤ prefixEnvelope kind width := by
  change ResourcePool.ofList
    ((TerminalDecode.intoFromBitRefs .littleEndian
      (PackedSample.proposalRefs sample proposal) scratch.candidate).eventTrace path.1 ++
      comparisonEvents kind width) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (TerminalDecode.terminalDecode_intoFromBitRefs_pool_le .littleEndian
    (PackedSample.proposalRefs sample proposal) scratch.candidate path.1) le_rfl

/-- Every source-addressed slot includes the actual selected branch's native charges. -/
theorem proposalSlot_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (slot sample proposal shared scratch).Path) :
    (slot sample proposal shared scratch).resourcePool path ≤ slotEnvelope kind width := by
  change ResourcePool.ofList ((prefixBody sample proposal shared scratch).eventTrace path.1 ++
    (FirstAccepted.circuit (selectorInputs scratch) shared.selector).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (proposalPrefix_pool_le sample proposal shared scratch path.1)
    (FirstAccepted.firstAccepted_pool_le (selectorInputs scratch) shared.selector path.2)

/-- The actual ordered fold consumes at most its list's number of independent slot allowances. -/
theorem proposalFold_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) :
    ∀ path : (foldSlots sample shared scratch proposals).Path,
      (foldSlots sample shared scratch proposals).resourcePool path ≤
        ResourcePool.scale proposals.length (slotEnvelope kind width) := by
  induction proposals with
  | nil =>
      intro path
      exact le_rfl
  | cons proposal remaining ih =>
      intro path
      change ResourcePool.ofList ((slot sample proposal shared scratch).eventTrace path.1 ++
        (foldSlots sample shared scratch remaining).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (proposalSlot_pool_le sample proposal shared scratch path.1) (ih path.2)

/-- The complete finite scan has one allowance per actual ascending proposal index. -/
theorem proposalScan_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (scan sample shared scratch).Path) :
    (scan sample shared scratch).resourcePool path ≤ scanEnvelope kind width count := by
  simpa only [scan, scanEnvelope, List.length_ofFn] using
    proposalFold_pool_le sample shared scratch (List.ofFn (fun proposal : Fin count => proposal))
      path

/-- The independent per-slot allowance has exactly two events per bit and eight fixed events. -/
theorem proposalSlotEnvelope_card (kind : ProblemKind) (width : Nat) :
    (slotEnvelope kind width).card = 2 * width + 8 := by
  simp [slotEnvelope, prefixEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents,
    comparisonEvents, ResourcePool.ofList, ResourcePool.scale, ResourcePool.singleton]
  omega

/-- The scan's independent total native capacity is the exact sum of its slot allowances. -/
theorem proposalScanEnvelope_card (kind : ProblemKind) (width count : Nat) :
    (scanEnvelope kind width count).card = count * (2 * width + 8) := by
  simp [scanEnvelope, ResourcePool.scale, proposalSlotEnvelope_card]

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
