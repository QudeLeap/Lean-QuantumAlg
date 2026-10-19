/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Scan

/-!
# Independent native allowances and reusable space for actual finite candidate scans
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScan

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {coordinateWidth modulusWidth : Nat}

/-- Independent sum of the original per-offset instruction allowances. -/
def offsetsEventEnvelope (execution : ExecutionModel) [BitWord.Selected execution]
    (coordinateWidth modulusWidth : Nat) :
    List NumberTheory.IntegerPoint3 → ResourcePool execution
  | [] => 0
  | offset :: tail =>
      LatticeCandidateSlotMachine.candidateSlotEventEnvelope execution coordinateWidth
        modulusWidth offset + offsetsEventEnvelope execution coordinateWidth modulusWidth tail

/-- Independent chronological sum of the original per-offset unit-duration bounds. -/
def offsetsDepthBound (coordinateWidth modulusWidth : Nat) :
    List NumberTheory.IntegerPoint3 → Nat
  | [] => 0
  | offset :: tail =>
      LatticeCandidateSlotMachine.candidateSlotDepthBound coordinateWidth modulusWidth offset +
        offsetsDepthBound coordinateWidth modulusWidth tail

/-- Every actual finite scan fits the independent sum of the original slot allowances. -/
lemma scanOffsetsInto_pool_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (path : (scanOffsetsInto spec refs items).Path) :
    (scanOffsetsInto spec refs items).resourcePool path ≤
      offsetsEventEnvelope model coordinateWidth modulusWidth items := by
  induction items with
  | nil => exact le_rfl
  | cons offset tail inductionHypothesis =>
    change ResourcePool.ofList (_ ++ _) ≤ _
    rw [ResourcePool.ofList_append]
    exact add_le_add (LatticeCandidateSlotMachine.candidateSlotInto_pool_le
      spec offset refs path.1) (inductionHypothesis path.2)

/-- The actual finite scan counts every sequential initialization and selected check dependency. -/
lemma scanOffsetsInto_depth_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (path : (scanOffsetsInto spec refs items).Path) :
    (scanOffsetsInto spec refs items).depth (fun _ => 1) path ≤
      offsetsDepthBound coordinateWidth modulusWidth items := by
  induction items with
  | nil => exact le_rfl
  | cons offset tail inductionHypothesis =>
    exact Nat.add_le_add (LatticeCandidateSlotMachine.candidateSlotInto_depth_le
      spec offset refs path.1) (inductionHypothesis path.2)

/-- Each actual scan restores all borrowed correlations after every original candidate slot. -/
lemma scanOffsetsInto_borrowedRestored (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scanOffsetsInto spec refs items).BorrowedRestored Reference state
      ((scanOffsetsInto spec refs items).execute environment Reference state) := by
  induction items generalizing History with
  | nil =>
    exact Circuit.borrowedRestored_id
      (environment := environment) (model := model) (ctx := ctx) state
  | cons offset tail inductionHypothesis =>
    exact Circuit.borrowedRestored_seq (environment := environment) _ _ state
      (LatticeCandidateSlotMachine.candidateSlotInto_borrowedRestored spec offset refs
        Reference state)
      (inductionHypothesis _)

/-- The actual finite scan reuses one power scope while counting all original resident storage. -/
lemma scanOffsetsInto_resident_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (path : (scanOffsetsInto spec refs items).Path) :
    (scanOffsetsInto spec refs items).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind modulusWidth := by
  induction items with
  | nil =>
    refine le_trans ?_ (le_add_of_nonneg_right zero_le)
    apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    change visited ∈ [ctx] at present
    rw [List.mem_singleton.mp present]
  | cons offset tail inductionHypothesis =>
    refine (Circuit.peakResidentSpace_seq
      (LatticeCandidateSlotMachine.candidateSlotInto spec offset refs)
      (scanOffsetsInto spec refs tail) path).le.trans ?_
    exact SpacePool.max_le (LatticeCandidateSlotMachine.candidateSlotInto_resident_le
      spec offset refs path.1) (inductionHypothesis path.2)

/-- The actual finite scan reuses one power scope while counting all original auxiliary storage. -/
lemma scanOffsetsInto_auxiliary_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (path : (scanOffsetsInto spec refs items).Path) :
    (scanOffsetsInto spec refs items).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind modulusWidth := by
  induction items with
  | nil =>
    refine le_trans ?_ (le_add_of_nonneg_right zero_le)
    apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    change visited ∈ [ctx] at present
    rw [List.mem_singleton.mp present]
  | cons offset tail inductionHypothesis =>
    refine (Circuit.peakAuxiliarySpace_seq
      (LatticeCandidateSlotMachine.candidateSlotInto spec offset refs)
      (scanOffsetsInto spec refs tail) path).le.trans ?_
    exact SpacePool.max_le (LatticeCandidateSlotMachine.candidateSlotInto_auxiliary_le
      spec offset refs path.1) (inductionHypothesis path.2)

/-- Independent complete canonical scan allowance from its original public offset order. -/
def scanEventEnvelope (execution : ExecutionModel) [BitWord.Selected execution]
    (coordinateWidth modulusWidth : Nat) : ResourcePool execution :=
  offsetsEventEnvelope execution coordinateWidth modulusWidth offsets.toList

/-- Independent complete canonical scan unit-duration bound. -/
def scanDepthBound (coordinateWidth modulusWidth : Nat) : Nat :=
  offsetsDepthBound coordinateWidth modulusWidth offsets.toList

/-- The actual canonical scan meets its independent native-operation budget. -/
lemma scanInto_pool_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (path : (scanInto spec refs).Path) :
    (scanInto spec refs).resourcePool path ≤ scanEventEnvelope model coordinateWidth
      modulusWidth :=
  scanOffsetsInto_pool_le spec refs offsets.toList path

/-- The actual canonical scan meets its independent chronological depth bound. -/
lemma scanInto_depth_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (path : (scanInto spec refs).Path) :
    (scanInto spec refs).depth (fun _ => 1) path ≤ scanDepthBound coordinateWidth modulusWidth :=
  scanOffsetsInto_depth_le spec refs offsets.toList path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScan
