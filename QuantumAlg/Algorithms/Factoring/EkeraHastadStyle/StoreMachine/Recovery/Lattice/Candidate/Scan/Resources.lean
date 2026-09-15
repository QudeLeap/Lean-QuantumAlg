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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {coordinateWidth modulusWidth : Nat}

/-- Independent sum of the original per-offset instruction allowances. -/
def offsetsEventEnvelope (kind : ProblemKind) (coordinateWidth modulusWidth : Nat) :
    List NumberTheory.IntegerPoint3 → ResourcePool kind
  | [] => 0
  | offset :: tail =>
      LatticeCandidateSlotMachine.candidateSlotEventEnvelope kind coordinateWidth modulusWidth
        offset + offsetsEventEnvelope kind coordinateWidth modulusWidth tail

/-- Independent chronological sum of the original per-offset unit-duration bounds. -/
def offsetsDepthBound (coordinateWidth modulusWidth : Nat) :
    List NumberTheory.IntegerPoint3 → Nat
  | [] => 0
  | offset :: tail =>
      LatticeCandidateSlotMachine.candidateSlotDepthBound coordinateWidth modulusWidth offset +
        offsetsDepthBound coordinateWidth modulusWidth tail

/-- Every actual finite scan fits the independent sum of the original slot allowances. -/
theorem scanOffsetsInto_pool_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (path : (scanOffsetsInto spec refs items).Path) :
    (scanOffsetsInto spec refs items).resourcePool path ≤
      offsetsEventEnvelope kind coordinateWidth modulusWidth items := by
  induction items with
  | nil => exact le_rfl
  | cons offset tail inductionHypothesis =>
    change ResourcePool.ofList (_ ++ _) ≤ _
    rw [ResourcePool.ofList_append]
    exact add_le_add (LatticeCandidateSlotMachine.candidateSlotInto_pool_le
      spec offset refs path.1) (inductionHypothesis path.2)

/-- The actual finite scan counts every sequential initialization and selected check dependency. -/
theorem scanOffsetsInto_depth_le (spec : ModulusSpec modulusWidth)
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
theorem scanOffsetsInto_borrowedRestored (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scanOffsetsInto spec refs items).BorrowedRestored Reference state
      ((scanOffsetsInto spec refs items).execute Reference state) := by
  induction items generalizing History with
  | nil =>
    change (Circuit.id ctx).BorrowedRestored Reference state
      ((Circuit.id ctx).execute Reference state)
    rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, Circuit.execute_id]
    exact observeBorrowed_mapHistory state _
  | cons offset tail inductionHypothesis =>
    exact Circuit.borrowedRestored_seq _ _ state
      (LatticeCandidateSlotMachine.candidateSlotInto_borrowedRestored spec offset refs
        Reference state)
      (inductionHypothesis _)

/-- The actual finite scan reuses one power scope while counting all original resident storage. -/
theorem scanOffsetsInto_resident_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (path : (scanOffsetsInto spec refs items).Path) :
    (scanOffsetsInto spec refs items).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace kind modulusWidth := by
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
theorem scanOffsetsInto_auxiliary_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (path : (scanOffsetsInto spec refs items).Path) :
    (scanOffsetsInto spec refs items).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace kind modulusWidth := by
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
def scanEventEnvelope (kind : ProblemKind) (coordinateWidth modulusWidth : Nat) :
    ResourcePool kind :=
  offsetsEventEnvelope kind coordinateWidth modulusWidth offsets.toList

/-- Independent complete canonical scan unit-duration bound. -/
def scanDepthBound (coordinateWidth modulusWidth : Nat) : Nat :=
  offsetsDepthBound coordinateWidth modulusWidth offsets.toList

/-- The actual canonical scan meets its independent native-operation budget. -/
theorem scanInto_pool_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (path : (scanInto spec refs).Path) :
    (scanInto spec refs).resourcePool path ≤ scanEventEnvelope kind coordinateWidth modulusWidth :=
  scanOffsetsInto_pool_le spec refs offsets.toList path

/-- The actual canonical scan meets its independent chronological depth bound. -/
theorem scanInto_depth_le (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (path : (scanInto spec refs).Path) :
    (scanInto spec refs).depth (fun _ => 1) path ≤ scanDepthBound coordinateWidth modulusWidth :=
  scanOffsetsInto_depth_le spec refs offsets.toList path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScan
