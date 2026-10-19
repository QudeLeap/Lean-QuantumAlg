/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Scan.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Semantics

/-!
# Original first-success source fold of actual finite candidate execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScanFold

open Execution
open LatticeCandidateSlotFrames

noncomputable section

/-- The canonical offset fold is the selector projection of the sealed source trace. -/
lemma canonical_fold_none_eq_recoverShortLogFromPair {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    (LatticeCandidateScan.offsets.toList.map
      (RSA.shortLogCandidateAtOffset m ell generator samples)).foldl
        RSA.retainFirstShortLogCandidate none =
      RSA.recoverShortLogFromPair m ell generator samples := by
  rw [RSA.recoverShortLogFromPair_eq_selector,
    RSA.shortLogPairRecoveryTrace_selected_fold,
    RSA.shortLogCandidateChecks_eq_map]
  simp only [LatticeCandidateScan.offsets,
    NumberTheory.toList_coefficientOffsetVector3]

/-- Original retained inputs, ordered candidate fold and full caller frame of an actual scan. -/
structure Outcome {N m ell : Nat} {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (items : List NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (before after : Store ctx) : Prop where
  initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs after
  selected : LatticeCandidateSlotMachine.selectedOption refs.selector.selection after =
    (items.map (RSA.shortLogCandidateAtOffset m ell generator samples)).foldl
      RSA.retainFirstShortLogCandidate
      (LatticeCandidateSlotMachine.selectedOption refs.selector.selection before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- Actual finite scan execution composes the unchanged source checks in their original order. -/
lemma scanOffsetsInto_correct {N m ell : Nat} {model : ExecutionModel}
    [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (items : List NumberTheory.IntegerPoint3)
    (inWindow : ∀ offset ∈ items, offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (separation : LatticeCandidateSlotMachine.Separation refs)
    (frameSeparation : FrameSeparation refs) (store : Store ctx)
    (initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs store) :
    Outcome input generator samples items refs store
      (LatticeCandidateScan.scanOffsetsStep (model := model)
        (LatticeCandidateModularSetup.modulusSpec input)
        refs items store).1 := by
  induction items generalizing store with
  | nil => exact ⟨initial, rfl, fun _ _ => rfl⟩
  | cons offset tail inductionHypothesis =>
    have first := LatticeCandidateSlotSemantics.candidateSlotInto_correct (model := model)
      input generator samples
      offset (inWindow offset (List.mem_cons_self)) refs separation frameSeparation store initial
    have rest := inductionHypothesis
      (fun candidate present => inWindow candidate (List.mem_cons_of_mem offset present))
      (LatticeCandidateSlotMachine.candidateSlotStep (model := model)
        (LatticeCandidateModularSetup.modulusSpec input) offset refs store).1 first.initial
    refine ⟨rest.initial, ?_, fun other avoids =>
      (rest.callerFrame other avoids).trans (first.callerFrame other avoids)⟩
    exact rest.selected.trans (by rw [List.map_cons, List.foldl_cons, first.selected])

/-- The actual canonical scan realizes the original ordered first-success fold from any latch. -/
lemma scanInto_correct {N m ell : Nat} {model : ExecutionModel}
    [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (separation : LatticeCandidateSlotMachine.Separation refs)
    (frameSeparation : FrameSeparation refs) (store : Store ctx)
    (initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs store) :
    Outcome input generator samples LatticeCandidateScan.offsets.toList refs store
      (LatticeCandidateScan.scanStep (model := model)
        (LatticeCandidateModularSetup.modulusSpec input) refs store).1 := by
  unfold LatticeCandidateScan.scanStep
  exact scanOffsetsInto_correct (model := model)
    input generator samples LatticeCandidateScan.offsets.toList
    (fun _ present => by
      simpa only [LatticeCandidateScan.offsets, NumberTheory.toList_coefficientOffsetVector3]
        using present) refs separation frameSeparation store initial

/-- With no earlier accepted value, the actual source fold is exactly the original pair recovery. -/
lemma Outcome.recoverShortLogFromPair_of_none {N m ell : Nat} {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (before after : Store ctx)
    (outcome : Outcome input generator samples LatticeCandidateScan.offsets.toList
      refs before after)
    (empty : LatticeCandidateSlotMachine.selectedOption refs.selector.selection before = none) :
    LatticeCandidateSlotMachine.selectedOption refs.selector.selection after =
      RSA.recoverShortLogFromPair m ell generator samples := by
  rw [outcome.selected, empty]
  exact canonical_fold_none_eq_recoverShortLogFromPair m ell generator samples

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScanFold
