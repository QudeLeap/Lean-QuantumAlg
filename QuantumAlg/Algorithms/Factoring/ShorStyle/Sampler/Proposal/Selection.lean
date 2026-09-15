/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Comparison
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Preservation
import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics

/-!
# Source-valued latches of one actual proposal slot

The real packed-bit decoder, four comparison instructions and stored-condition
selector return the original source slice on first acceptance. Earlier
acceptance keeps its complete selected word. The statements allow arbitrary
initial candidate and scratch values, and arbitrary stored interval endpoints.
The enclosing layout supplies the structural cell separation below.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- Structural facts supplied by the sampler's actual fresh cells. -/
structure SlotSeparated (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) : Prop where
  /-- The literal comparison and selector wiring satisfy their local read contracts. -/
  comparison : ComparisonSeparated shared scratch
  selector : FirstAccepted.Separated (selectorInputs scratch) shared.selector
  /-- Candidate decoding preserves the sample and both stored endpoints. -/
  candidateSample : scratch.candidate.key ∉ sample.storageKeys
  candidateZero : scratch.candidate.key ∉ shared.zero.storageKeys
  candidateModulus : scratch.candidate.key ∉ shared.modulus.storageKeys
  /-- The complete prefix preserves the two persistent selection latches. -/
  prefixAccepted : ∀ key ∈ prefixKeys scratch, key ≠ shared.selector.accepted.key
  prefixSelected : ∀ key ∈ prefixKeys scratch, key ≠ shared.selector.selected.key

private theorem word_eq_of_toNat_eq (actual : CShape.Value (.unsignedWord width))
    (expected : Fin (2 ^ width)) (same : actual.toNat = expected.val) :
    actual = .unsignedWord expected := by
  cases actual with
  | unsignedWord word =>
      congr 1
      exact Fin.ext same

/-- The prefix returns the full source candidate word and its exact interval predicate. -/
theorem proposalPrefix_values
    (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (separated : SlotSeparated sample shared scratch) (store : Store ctx)
    (value : Fin (2 ^ (count * width)))
    (sampled : store.read sample = .bits (PackedSample.storedBits value)) :
    let candidate := RSA.decodeFixedWidthWords width count value proposal
    let final := (prefixStep sample proposal shared scratch store).1
    final.read (FirstAccepted.cellRead scratch.candidate) = .unsignedWord candidate ∧
      (final.read (FirstAccepted.cellRead scratch.eligible)).toBool =
        decide ((store.read shared.zero).toNat < candidate.val ∧
          candidate.val < (store.read shared.modulus).toNat) := by
  let decoded := (decodedStep sample proposal scratch store).1
  have decodedValue := proposalDecoded_read_source sample proposal scratch store value
    separated.candidateSample sampled
  have decodedZero : decoded.read shared.zero = store.read shared.zero :=
    TerminalDecode.terminalDecode_fold_read_other scratch.candidate _ store shared.zero
      separated.candidateZero
  have decodedModulus : decoded.read shared.modulus = store.read shared.modulus :=
    TerminalDecode.terminalDecode_fold_read_other scratch.candidate _ store shared.modulus
      separated.candidateModulus
  have candidate := proposalComparison_candidate shared scratch separated.comparison decoded
  have eligible := proposalComparison_eligible shared scratch separated.comparison decoded
  rw [decodedZero, decodedModulus, decodedValue] at eligible
  refine ⟨?_, eligible⟩
  exact candidate.trans (word_eq_of_toNat_eq _ _ decodedValue)

/-- One actual slot latches the first eligible source proposal and preserves an earlier choice. -/
theorem proposalSlot_latches
    (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (separated : SlotSeparated sample shared scratch) (store : Store ctx)
    (value : Fin (2 ^ (count * width)))
    (sampled : store.read sample = .bits (PackedSample.storedBits value)) :
    let candidate := RSA.decodeFixedWidthWords width count value proposal
    let eligible := decide ((store.read shared.zero).toNat < candidate.val ∧
      candidate.val < (store.read shared.modulus).toNat)
    let accepted := (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool
    let final := (slotStep sample proposal shared scratch store).1
    (final.read (FirstAccepted.cellRead shared.selector.accepted)).toBool =
        (accepted || eligible) ∧
      final.read (FirstAccepted.cellRead shared.selector.selected) =
        if (!accepted) && eligible then .unsignedWord candidate
          else store.read (FirstAccepted.cellRead shared.selector.selected) := by
  let prefixed := (prefixStep sample proposal shared scratch store).1
  have values := proposalPrefix_values sample proposal shared scratch separated store value sampled
  have acceptedRead : prefixed.read (FirstAccepted.cellRead shared.selector.accepted) =
      store.read (FirstAccepted.cellRead shared.selector.accepted) :=
    proposalPrefix_read_other sample proposal shared scratch
      (FirstAccepted.cellRead shared.selector.accepted)
      (fun key member => by
        simpa only [FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton] using
          separated.prefixAccepted key member) store
  have selectedRead : prefixed.read (FirstAccepted.cellRead shared.selector.selected) =
      store.read (FirstAccepted.cellRead shared.selector.selected) :=
    proposalPrefix_read_other sample proposal shared scratch
      (FirstAccepted.cellRead shared.selector.selected)
      (fun key member => by
        simpa only [FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton] using
          separated.prefixSelected key member) store
  have selected := FirstAccepted.firstAccepted_latches (selectorInputs scratch)
    shared.selector separated.selector prefixed
  dsimp only at values selected ⊢
  change _ = (_ || (prefixed.read (FirstAccepted.cellRead scratch.eligible)).toBool) ∧
    _ = if (!(prefixed.read (FirstAccepted.cellRead shared.selector.accepted)).toBool) &&
      (prefixed.read (FirstAccepted.cellRead scratch.eligible)).toBool then
        prefixed.read (FirstAccepted.cellRead scratch.candidate)
      else prefixed.read (FirstAccepted.cellRead shared.selector.selected) at selected
  rw [acceptedRead, selectedRead, values.1, values.2] at selected
  exact selected

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
