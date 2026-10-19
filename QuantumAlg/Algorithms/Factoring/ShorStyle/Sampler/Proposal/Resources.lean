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

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width count : Nat}

/-- Literal comparison suffix: resize, two strict comparisons and conjunction. -/
def comparisonEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))]

/-- Independent allowance for decoding one proposal and computing its eligibility. -/
def prefixEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  TerminalDecode.envelope (model := model)
    width + ResourcePool.ofList (comparisonEvents model width)

/-- Independent native allowance for one complete proposal and first-accepted step. -/
def slotEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  prefixEnvelope model width + FirstAccepted.nativeEnvelope model width

/-- Exactly one independent slot allowance for each original source proposal. -/
def scanEnvelope (model : ExecutionModel) [BitWord.Selected model] (width count : Nat) :
    ResourcePool model :=
  ResourcePool.scale count (slotEnvelope model width)

/-- The actual comparison suffix emits exactly its four named native coordinates. -/
lemma proposalComparison_eventTrace (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (path : (comparisonBody (model := model)
      shared scratch).Path) :
    (comparisonBody (model := model)
      shared scratch).eventTrace path = comparisonEvents model width := by
  change (BitWord.instruction (execution := model) (extendOp scratch)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (positiveOp shared scratch)).eventTrace path.2.1 ++
      ((BitWord.instruction (execution := model) (belowOp shared scratch)).eventTrace path.2.2.1 ++
        (BitWord.instruction (execution := model) (eligibleOp scratch)).eventTrace path.2.2.2)) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual decoding and comparisons fit their independent native-coordinate budget. -/
lemma proposalPrefix_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (prefixBody (model := model) sample proposal shared scratch).Path) :
    (prefixBody (model := model)
      sample proposal shared scratch).resourcePool path ≤ prefixEnvelope model width := by
  change ResourcePool.ofList
    ((TerminalDecode.intoFromBitRefs (model := model) .littleEndian
      (PackedSample.proposalRefs sample proposal) scratch.candidate).eventTrace path.1 ++
      (comparisonBody (model := model) shared scratch).eventTrace path.2) ≤ _
  rw [proposalComparison_eventTrace, ResourcePool.ofList_append]
  exact add_le_add (TerminalDecode.terminalDecode_intoFromBitRefs_pool_le (model := model)
    .littleEndian
    (PackedSample.proposalRefs sample proposal) scratch.candidate path.1) le_rfl

/-- Every source-addressed slot includes the actual selected branch's native charges. -/
lemma proposalSlot_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (slot (model := model) sample proposal shared scratch).Path) :
    (slot (model := model)
      sample proposal shared scratch).resourcePool path ≤ slotEnvelope model width := by
  change ResourcePool.ofList ((prefixBody (model := model)
    sample proposal shared scratch).eventTrace path.1 ++
    (FirstAccepted.circuit (model := model)
      (selectorInputs scratch) shared.selector).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (proposalPrefix_pool_le (model := model) sample proposal shared scratch path.1)
    (FirstAccepted.firstAccepted_pool_le (model := model)
      (selectorInputs scratch) shared.selector path.2)

/-- The actual ordered fold consumes at most its list's number of independent slot allowances. -/
lemma proposalFold_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) :
    ∀ path : (foldSlots (model := model) sample shared scratch proposals).Path,
      (foldSlots (model := model) sample shared scratch proposals).resourcePool path ≤
        ResourcePool.scale proposals.length (slotEnvelope model width) := by
  induction proposals with
  | nil =>
      intro path
      exact le_rfl
  | cons proposal remaining ih =>
      intro path
      change ResourcePool.ofList ((slot (model := model)
        sample proposal shared scratch).eventTrace path.1 ++
        (foldSlots (model := model) sample shared scratch remaining).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (proposalSlot_pool_le (model := model)
        sample proposal shared scratch path.1) (ih path.2)

/-- The complete finite scan has one allowance per actual ascending proposal index. -/
lemma proposalScan_pool_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (scan (model := model) sample shared scratch).Path) :
    (scan (model := model)
      sample shared scratch).resourcePool path ≤ scanEnvelope model width count := by
  simpa only [scan, scanEnvelope, List.length_ofFn] using
    proposalFold_pool_le (model := model)
      sample shared scratch (List.ofFn (fun proposal : Fin count => proposal))
      path

/-- The independent per-slot allowance has exactly two events per bit and eight fixed events. -/
lemma proposalSlotEnvelope_card (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    (slotEnvelope model width).card = 2 * width + 8 := by
  simp [slotEnvelope, prefixEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents,
    comparisonEvents, ResourcePool.ofList, ResourcePool.scale, ResourcePool.singleton]
  omega

/-- The scan's independent total native capacity is the exact sum of its slot allowances. -/
lemma proposalScanEnvelope_card (model : ExecutionModel) [BitWord.Selected model]
    (width count : Nat) :
    (scanEnvelope model width count).card = count * (2 * width + 8) := by
  simp [scanEnvelope, ResourcePool.scale, proposalSlotEnvelope_card]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
