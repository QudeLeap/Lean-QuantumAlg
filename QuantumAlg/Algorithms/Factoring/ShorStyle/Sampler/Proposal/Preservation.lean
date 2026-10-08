/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Semantics
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!
# Structural reads through the actual proposal scan

The addressed decoder and comparison suffix write only their five supplied
cells. Selection additionally writes its four supplied latch and scratch
cells. Every structural read outside these actual keys survives every slot
and the complete finite scan, independently of all initial scratch values.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- The actual writable keys of the decoder and comparison instructions. -/
def prefixKeys (scratch : ScratchRefs ctx width) : List StorageKey :=
  [scratch.candidate.key, scratch.extended.key, scratch.positive.key,
    scratch.belowModulus.key, scratch.eligible.key]

/-- All keys that the actual proposal slot can write along either selector arm. -/
def slotKeys (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) : List StorageKey :=
  prefixKeys scratch ++ [shared.selector.available.key, shared.selector.take.key,
    shared.selector.accepted.key, shared.selector.selected.key]

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The exact prefix store preserves every structural read outside its five written cells. -/
theorem proposalPrefix_read_other
    (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : ∀ key ∈ prefixKeys scratch, key ∉ other.storageKeys) (store : Store ctx) :
    (prefixStep (model := model) sample proposal shared scratch store).1.read other =
      store.read other := by
  have decoded := TerminalDecode.terminalDecode_fold_read_other (model := model) scratch.candidate
    (List.ofFn (fun index => PackedSample.proposalRefs sample proposal
      (TerminalDecode.sourceIndex .littleEndian index))) store other
        (separate _ (by simp [prefixKeys]))
  change (comparisonStore shared scratch
    (decodedStep (model := model) sample proposal scratch store).1).read other = _
  unfold comparisonStore
  exact (Store.read_applyOp_of_not_mem_storageKeys _ (eligibleOp scratch) other
    (separate scratch.eligible.key (by simp [prefixKeys]))).trans
      ((Store.read_applyOp_of_not_mem_storageKeys _ (belowOp shared scratch) other
        (separate scratch.belowModulus.key (by simp [prefixKeys]))).trans
          ((Store.read_applyOp_of_not_mem_storageKeys _ (positiveOp shared scratch) other
            (separate scratch.positive.key (by simp [prefixKeys]))).trans
              ((Store.read_applyOp_of_not_mem_storageKeys _ (extendOp scratch) other
                (separate _ (by simp [prefixKeys, extendOp]))).trans decoded)))

/-- The actual selected arm introduces no writes beyond the nine supplied cells. -/
theorem proposalSlot_read_other
    (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : ∀ key ∈ slotKeys shared scratch, key ∉ other.storageKeys) (store : Store ctx) :
    (slotStep (model := model) sample proposal shared scratch store).1.read other =
      store.read other := by
  change (FirstAccepted.step (model := model) (selectorInputs scratch) shared.selector
    (prefixStep (model := model) sample proposal shared scratch store).1).1.read other = _
  refine (FirstAccepted.firstAccepted_read_other (model := model)
    (selectorInputs scratch) shared.selector other
    (separate _ (by simp [slotKeys])) (separate _ (by simp [slotKeys]))
    (separate _ (by simp [slotKeys])) (separate _ (by simp [slotKeys])) _).trans ?_
  exact proposalPrefix_read_other sample proposal shared scratch other
    (fun key member => separate key (List.mem_append_left _ member)) store

/-- Every ordered finite proposal scan preserves all structural reads outside its actual writes. -/
theorem proposalFold_read_other
    (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : ∀ key ∈ slotKeys shared scratch, key ∉ other.storageKeys) (store : Store ctx) :
    (foldSteps (model := model) sample shared scratch proposals store).1.read other =
      store.read other := by
  induction proposals generalizing store with
  | nil => rfl
  | cons proposal remaining ih =>
      change (foldSteps (model := model) sample shared scratch remaining
        (slotStep (model := model) sample proposal shared scratch store).1).1.read other = _
      exact (ih _).trans
        (proposalSlot_read_other sample proposal shared scratch other separate store)

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
