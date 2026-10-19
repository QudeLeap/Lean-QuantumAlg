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
# Unit-duration depth of the actual ordered proposal scan

The bound includes each real decoder shift and selected increment, all four
native interval instructions and the selected first-accepted writes. Every
source proposal remains in its original serial order.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open ClassicalRoutines

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width count : Nat}

/-- Actual candidate decoding and interval checks have at most two events per bit plus four. -/
lemma proposalPrefix_unit_depth_le (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (prefixBody (model := model) sample proposal shared scratch).Path) :
    (prefixBody (model := model)
      sample proposal shared scratch).depth (fun _ => 1) path ≤ 2 * width + 4 := by
  have decoded := TerminalDecode.terminalDecode_intoFromBitRefs_depth_le (model := model)
    .littleEndian
    (PackedSample.proposalRefs sample proposal) scratch.candidate (fun _ => 1) path.1
  change (TerminalDecode.intoFromBitRefs (model := model)
    .littleEndian (PackedSample.proposalRefs sample proposal)
    scratch.candidate).depth (fun _ => 1) path.1 + 4 ≤ _
  omega

/-- One full actual slot includes its selected latch writes in the serial depth. -/
lemma proposalSlot_unit_depth_le (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (slot (model := model) sample proposal shared scratch).Path) :
    (slot (model := model)
      sample proposal shared scratch).depth (fun _ => 1) path ≤ 2 * width + 8 := by
  have prefixed := proposalPrefix_unit_depth_le (model := model)
    sample proposal shared scratch path.1
  have selected := FirstAccepted.firstAccepted_unit_depth (model := model) (selectorInputs scratch)
    shared.selector path.2
  have selectedBound : (FirstAccepted.circuit (model := model)
    (selectorInputs scratch) shared.selector).depth
      (fun _ => 1) path.2 ≤ 4 := by
    rw [selected]
    split <;> omega
  change (prefixBody (model := model) sample proposal shared scratch).depth (fun _ => 1) path.1 +
    (FirstAccepted.circuit (model := model)
      (selectorInputs scratch) shared.selector).depth (fun _ => 1) path.2 ≤ _
  omega

/-- Every original slot contributes its actual serial instruction dependencies. -/
lemma proposalFold_unit_depth_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) :
    ∀ path : (foldSlots (model := model) sample shared scratch proposals).Path,
      (foldSlots (model := model) sample shared scratch proposals).depth (fun _ => 1) path ≤
        proposals.length * (2 * width + 8) := by
  induction proposals with
  | nil => intro path; exact Nat.zero_le _
  | cons proposal remaining ih =>
      intro path
      have first := proposalSlot_unit_depth_le (model := model)
        sample proposal shared scratch path.1
      have later := ih path.2
      change (slot (model := model) sample proposal shared scratch).depth (fun _ => 1) path.1 +
        (foldSlots (model := model) sample shared scratch remaining).depth (fun _ => 1) path.2 ≤ _
      exact (Nat.add_le_add first later).trans_eq
        ((Nat.add_comm _ _).trans (Nat.succ_mul remaining.length (2 * width + 8)).symm)

/-- The complete finite source scan has the explicit serial-depth bound for its proposal count. -/
lemma proposalScan_unit_depth_le (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (path : (scan (model := model) sample shared scratch).Path) :
    (scan (model := model)
      sample shared scratch).depth (fun _ => 1) path ≤ count * (2 * width + 8) := by
  simpa only [scan, List.length_ofFn] using proposalFold_unit_depth_le (model := model)
    sample shared scratch
    (List.ofFn (fun proposal : Fin count => proposal)) path

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
