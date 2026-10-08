/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite

/-!
# Actual selector geometry through preparation and every retained round

The producer's five genuinely distinct retained storage identities survive
quantum preparation and all later source allocations. The complete recovery
visits therefore discharge their own selector separation conditions.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution ClassicalRoutines

noncomputable section

private theorem separated_of_keys {ctx : RuntimeCtx .quantum} {N : Nat}
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (scratchCandidate : cells.scratch.key ≠ cells.candidate.key)
    (scratchAccepted : cells.scratch.key ≠ cells.accepted.key)
    (scratchSelected : cells.scratch.key ≠ cells.selected.key)
    (acceptedSelected : cells.accepted.key ≠ cells.selected.key)
    (candidateAccepted : cells.candidate.key ≠ cells.accepted.key)
    (candidateSelected : cells.candidate.key ≠ cells.selected.key)
    (resultAccepted : result.key ≠ cells.accepted.key)
    (resultSelected : result.key ≠ cells.selected.key) :
    NativeFactorScan.Separated cells result := by
  have selector : FirstAccepted.Separated (NativeFactorScan.selectorInputs cells)
      (NativeFactorScan.selectorRefs cells) := by
    refine ⟨?_, ?_, ?_, scratchAccepted, scratchAccepted,
      scratchSelected, scratchSelected, acceptedSelected⟩
    all_goals exact fun member => scratchCandidate (List.mem_singleton.mp member)
  exact ⟨selector, candidateAccepted, candidateSelected, resultAccepted, resultSelected⟩

private theorem separated_transfer {ctx post : RuntimeCtx .quantum} {N : Nat}
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (later : NativeFactorScan.Cells post N)
    (destination : CWriteRef post (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated original result)
    (candidate : later.candidate.key = original.candidate.key)
    (accepted : later.accepted.key = original.accepted.key)
    (selected : later.selected.key = original.selected.key)
    (scratch : later.scratch.key = original.scratch.key)
    (output : destination.key = result.key) :
    NativeFactorScan.Separated later destination := by
  have scratchCandidate : original.scratch.key ≠ original.candidate.key :=
    fun same => separated.selector.availableCandidate (List.mem_singleton.mpr same)
  have scratchAccepted : original.scratch.key ≠ original.accepted.key :=
    separated.selector.availableAccepted
  have scratchSelected : original.scratch.key ≠ original.selected.key :=
    separated.selector.availableSelected
  have acceptedSelected : original.accepted.key ≠ original.selected.key :=
    separated.selector.acceptedSelected
  apply separated_of_keys later destination
  · simpa only [scratch, candidate] using scratchCandidate
  · simpa only [scratch, accepted] using scratchAccepted
  · simpa only [scratch, selected] using scratchSelected
  · simpa only [accepted, selected] using acceptedSelected
  · simpa only [candidate, accepted] using separated.candidateAccepted
  · simpa only [candidate, selected] using separated.candidateSelected
  · simpa only [output, accepted] using separated.resultAccepted
  · simpa only [output, selected] using separated.resultSelected

/-- One actual complete round preserves all internal selector separation conditions. -/
theorem Completion.separated (ctx : RuntimeCtx .quantum) (N : Nat)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated original result) :
    NativeFactorScan.Separated (Completion.cells ctx N original)
      (Completion.liftWrite ctx N result) :=
  separated_transfer original result (Completion.cells ctx N original)
    (Completion.liftWrite ctx N result) separated
    (Completion.liftWrite_key ctx N original.candidate)
    (Completion.liftWrite_key ctx N original.accepted)
    (Completion.liftWrite_key ctx N original.selected)
    (Completion.liftWrite_key ctx N original.scratch)
    (Completion.liftWrite_key ctx N result)

/-- Real quantum preparation preserves the producer's own distinct selector identities. -/
theorem Initialized.separated (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) :
    NativeFactorScan.Separated (Initialized.cells base noQuantum N)
      (Initialized.result base noQuantum N) :=
  separated_transfer (Persistent.cells base N) (Persistent.resultRef base N)
    (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)
    (Persistent.separated base N) rfl rfl rfl rfl rfl

/-- Every finite actual allocation keeps each original destination's real storage identity. -/
theorem Finite.liftWrite_key {shape : CShape} (ctx : RuntimeCtx .quantum) (N count : Nat)
    (original : CWriteRef ctx shape) :
    (Finite.liftWrite ctx N count original).key = original.key := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact (induction (Iteration.context ctx N) (Completion.liftWrite ctx N original)).trans
        (Completion.liftWrite_key ctx N original)

/-- The arbitrary-count producer discharges all recovery separation from its real allocations. -/
theorem Finite.separated (ctx : RuntimeCtx .quantum) (N count : Nat)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated original result) :
    NativeFactorScan.Separated (Finite.cells ctx N count original)
      (Finite.liftWrite ctx N count result) :=
  separated_transfer original result (Finite.cells ctx N count original)
    (Finite.liftWrite ctx N count result) separated
    (Finite.liftWrite_key ctx N count original.candidate)
    (Finite.liftWrite_key ctx N count original.accepted)
    (Finite.liftWrite_key ctx N count original.selected)
    (Finite.liftWrite_key ctx N count original.scratch)
    (Finite.liftWrite_key ctx N count result)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
