/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Resources
import Mathlib.Data.Vector.Mem

/-!
# Actual finite scan of the original nearest-plane coefficient-offset list
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScan

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Exact public work of the fixed three-dimensional nearest-plane window. -/
abbrev Work : Nat :=
  NumberTheory.coefficientOffsetBoxWork3 NumberTheory.nearestPlaneCoefficientBounds3

/-- Canonical finite enumeration of every coefficient offset scanned here. -/
def offsets : List.Vector NumberTheory.IntegerPoint3 Work :=
  NumberTheory.coefficientOffsetVector3 NumberTheory.nearestPlaneCoefficientBounds3

/-- The canonical offset assigned to one public scan index. -/
def offsetAt (index : Fin Work) : NumberTheory.IntegerPoint3 :=
  offsets.get index

/-- Every scan index is drawn from the canonical offset list. -/
theorem offsetAt_mem_list (index : Fin Work) :
    offsetAt index ∈
      NumberTheory.coefficientOffsetList3 NumberTheory.nearestPlaneCoefficientBounds3 := by
  simpa only [offsetAt, offsets, NumberTheory.toList_coefficientOffsetVector3] using
    List.Vector.get_mem index offsets

/-- Every scan index denotes an offset in the fixed nearest-plane box. -/
theorem offsetAt_mem (index : Fin Work) :
    offsetAt index ∈
      NumberTheory.coefficientOffsetBox3 NumberTheory.nearestPlaneCoefficientBounds3 := by
  rw [← NumberTheory.mem_coefficientOffsetList3]
  exact offsetAt_mem_list index

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {coordinateWidth modulusWidth : Nat}

/-- Execute the original candidate instructions in the supplied finite offset order. -/
def scanOffsetsInto (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth) :
    List NumberTheory.IntegerPoint3 → Circuit model ctx ctx
  | [] => .id ctx
  | offset :: tail => .seq (LatticeCandidateSlotMachine.candidateSlotInto spec offset refs)
      (scanOffsetsInto spec refs tail)

/-- The actual complete store and chronological paths for a finite list of original slots. -/
def scanOffsetsStep (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth) :
    (items : List NumberTheory.IntegerPoint3) → Store ctx →
      Store ctx × (scanOffsetsInto spec refs items).Path
  | [], store => (store, ())
  | offset :: tail, store =>
      let first := LatticeCandidateSlotMachine.candidateSlotStep spec offset refs store
      let rest := scanOffsetsStep spec refs tail first.1
      (rest.1, (first.2, rest.2))

/-- The actual complete finite scan retains every incoming history and quantum-reference block. -/
theorem scanOffsetsInto_execute (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scanOffsetsInto spec refs items).execute Reference state = state.mapClassical (fun entry =>
      let actual := scanOffsetsStep spec refs items entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  induction items generalizing Reference History with
  | nil =>
    refine (Circuit.execute_id_mapClassical Reference state).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  | cons offset tail inductionHypothesis =>
    refine (Circuit.execute_seq_mapClassical
      (LatticeCandidateSlotMachine.candidateSlotInto spec offset refs)
      (scanOffsetsInto spec refs tail)
      (fun before =>
        let actual := LatticeCandidateSlotMachine.candidateSlotStep spec offset refs before.1
        ((actual.1, before.2), actual.2))
      (fun before =>
        let actual := scanOffsetsStep spec refs tail before.1
        ((actual.1, before.2), actual.2))
      (fun Reference _history _ current =>
        LatticeCandidateSlotMachine.candidateSlotInto_execute spec offset refs
          Reference current)
      (fun Reference _history _ current => inductionHypothesis (Reference := Reference) current)
      Reference state).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Run one actual candidate slot for every offset in the original canonical finite order. -/
def scanInto (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth) :
    Circuit model ctx ctx :=
  scanOffsetsInto spec refs offsets.toList

/-- The actual complete output and path of the canonical candidate scan.

Keep the canonical 404685-slot record folded during downstream elaboration;
`scanInto_execute` supplies its complete interpreter equation. -/
@[irreducible] def scanStep (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth) (store : Store ctx) :
    Store ctx × (scanInto spec refs).Path := scanOffsetsStep spec refs offsets.toList store

/-- The canonical actual scan preserves the complete state and records each selected slot path. -/
theorem scanInto_execute (spec : ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scanInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := scanStep spec refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  by
    unfold scanStep
    exact scanOffsetsInto_execute spec refs offsets.toList Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScan
