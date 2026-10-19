/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Program

/-!
# Actual candidate-slot write inventory and full caller frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotFrames

open Execution
open ClassicalRoutines

noncomputable section

/-- The two persistent original first-success outputs. -/
inductive SelectionCell where
  | accepted
  | selected
deriving DecidableEq

/-- Every physical caller-owned cell written by one literal candidate slot. -/
inductive MutableCell where
  | offset (cell : LatticeOffsetMaterializer.MutableCell)
  | candidate (cell : LatticeCandidatePointMachine.MutableCell)
  | difference (cell : LatticePointDifferenceMachine.DifferenceCell)
  | squaredDistance
  | distanceProduct
  | nearTarget (cell : LatticeNearTargetScale.MutableCell)
  | exponent (cell : LatticeCandidateExponent.MutableCell)
  | power
  | powerAccepted
  | selectorIntermediate
  | selectorEligible
  | selection (cell : SelectionCell)
deriving DecidableEq

/-- The five stages of a literal candidate slot. -/
inductive Stage where
  | distance
  | near
  | exponent
  | power
  | selector
deriving DecidableEq

/-- Storage identity of one physical mutable slot cell. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth) :
    MutableCell → StorageKey
  | .offset cell =>
      LatticeOffsetMaterializer.mutableKey refs.distance.materializer cell
  | .candidate cell =>
      LatticeCandidatePointMachine.mutableKey
        (LatticeShortLogCandidatePoint.candidateRefs refs.distance.candidate) cell
  | .difference cell =>
      LatticePointDifferenceMachine.differenceKey refs.distance.distance.difference cell
  | .squaredDistance => refs.distance.distance.squaredDistance.toCStorageRef.key
  | .distanceProduct => refs.distance.distance.product.toCStorageRef.key
  | .nearTarget cell => LatticeNearTargetScale.mutableKey refs.nearTarget cell
  | .exponent cell => LatticeCandidateExponent.mutableKey refs.exponent cell
  | .power => refs.power.power.toCStorageRef.key
  | .powerAccepted => refs.power.accepted.toCStorageRef.key
  | .selectorIntermediate => refs.selector.intermediate.toCStorageRef.key
  | .selectorEligible => refs.selector.eligible.toCStorageRef.key
  | .selection .accepted => refs.selector.selection.accepted.key
  | .selection .selected => refs.selector.selection.selected.key

/-- External source reads whose structural references need not be single cells. -/
inductive ExternalSourceCell where
  | candidateEntry (cell : LatticeCandidateDistancePrefix.CandidateEntryCell)
  | originalTarget (cell : LatticeCandidateDistancePrefix.PointCoordinate)
  | zero
  | upperBound
  | modulus
  | generator
  | targetPower
deriving DecidableEq

/-- Shape of one named external source read. -/
def externalSourceShape (coordinateWidth modulusWidth : Nat) :
    ExternalSourceCell → CShape
  | .candidateEntry _ => .unsignedWord coordinateWidth
  | .originalTarget _ => .unsignedWord coordinateWidth
  | .zero => .unsignedWord coordinateWidth
  | .upperBound => .unsignedWord coordinateWidth
  | .modulus => .unsignedWord (modulusWidth + 1)
  | .generator => .canonicalResidue modulusWidth
  | .targetPower => .unsignedWord modulusWidth

/-- Resolve one named external source to the literal structural input it reads. -/
def externalSourceInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth) :
    (source : ExternalSourceCell) →
      CInputRef ctx (externalSourceShape coordinateWidth modulusWidth source)
  | .candidateEntry cell =>
      LatticeCandidateDistancePrefix.candidateEntryInput refs.distance cell
  | .originalTarget cell =>
      LatticeCandidateDistancePrefix.originalTargetInput refs.distance cell
  | .zero => refs.zero
  | .upperBound => refs.upperBound
  | .modulus => refs.power.modulus
  | .generator => refs.power.generator
  | .targetPower => refs.power.targetPower

/-- The exact physical write footprint of one stage. -/
def isStageWrite : Stage → MutableCell → Prop
  | .distance, .offset _ => True
  | .distance, .candidate _ => True
  | .distance, .difference _ => True
  | .distance, .squaredDistance => True
  | .distance, .distanceProduct => True
  | .near, .nearTarget _ => True
  | .exponent, .exponent _ => True
  | .power, .power => True
  | .power, .powerAccepted => True
  | .selector, .selectorIntermediate => True
  | .selector, .selectorEligible => True
  | .selector, .selection _ => True
  | _, _ => False

/-- A structural input avoids every physical cell written by one named stage. -/
def AvoidsStageWrites {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    {shape : CShape} (other : CInputRef ctx shape) (stage : Stage) : Prop :=
  ∀ cell, isStageWrite stage cell → mutableKey refs cell ∉ other.storageKeys

/-- One caller read avoids every physical write of a complete candidate slot. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    {shape : CShape} (other : CInputRef ctx shape) : Prop where
  distance : AvoidsStageWrites refs other .distance
  near : AvoidsStageWrites refs other .near
  exponent : AvoidsStageWrites refs other .exponent
  power : AvoidsStageWrites refs other .power
  selector : AvoidsStageWrites refs other .selector

/-- Compact separation for all frames needed by one candidate slot.

The injectivity field handles a value produced by one stage and read by a later
stage. The second field is necessary because the public source inputs are
general structural references, not necessarily one storage cell each.
-/
structure FrameSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth) : Prop where
  mutableKeyInjective : Function.Injective (mutableKey refs)
  externalAvoidsMutable : ∀ source target,
    mutableKey refs target ∉ (externalSourceInput refs source).storageKeys

/-- Different named mutable cells have different storage identities. -/
lemma FrameSeparation.mutableKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    {refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth}
    (separation : FrameSeparation refs) {left right : MutableCell}
    (different : left ≠ right) : mutableKey refs left ≠ mutableKey refs right := by
  intro equal
  exact different (separation.mutableKeyInjective equal)

/-- One named external source avoids one named mutable cell. -/
lemma FrameSeparation.externalAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    {refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth}
    (separation : FrameSeparation refs) (source : ExternalSourceCell)
    (target : MutableCell) :
    mutableKey refs target ∉ (externalSourceInput refs source).storageKeys :=
  separation.externalAvoidsMutable source target

/-- Every named external input avoids the whole write footprint of one stage. -/
lemma FrameSeparation.externalAvoidsStage {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {coordinateWidth modulusWidth : Nat}
    {refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth}
    (separation : FrameSeparation refs) (source : ExternalSourceCell)
    (stage : Stage) : AvoidsStageWrites refs (externalSourceInput refs source) stage := by
  intro cell _
  exact separation.externalAvoids source cell

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {coordinateWidth modulusWidth : Nat}

omit [BitWord.Selected model] in
/-- A named live mutable read survives every stage that does not write that physical cell. -/
lemma mutableWrite_avoids_stage
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) {shape : CShape} (source : CWriteRef ctx shape)
    (sourceCell : MutableCell) (stage : Stage) (sourceKey : source.key = mutableKey refs sourceCell)
    (notWritten : ¬ isStageWrite stage sourceCell) :
    AvoidsStageWrites refs (LatticeCandidateSlotMachine.writeInput source) stage := by
  intro target targetWrite
  change mutableKey refs target ∉ [source.key]
  simp only [List.mem_singleton]
  rw [sourceKey]
  intro equal
  have same := separation.mutableKeyInjective equal
  exact notWritten (same ▸ targetWrite)

/-- Actual distance execution retains reads outside the unified distance-stage footprint. -/
lemma candidateDistancePrefixInto_callerFrame (offset : NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : AvoidsStageWrites refs other .distance) :
    (LatticeCandidateDistancePrefix.prefixStep offset refs.distance store).1.read other =
      store.read other := by
  apply LatticeCandidateDistancePrefix.candidateDistancePrefixInto_callerFrame offset
    refs.distance store other
  · exact fun cell => avoids (.offset cell) (by trivial)
  · exact fun cell => avoids (.candidate cell) (by trivial)
  · exact ⟨avoids (.difference .first) (by trivial),
      avoids (.difference .second) (by trivial), avoids (.difference .third) (by trivial),
      avoids .squaredDistance (by trivial), avoids .distanceProduct (by trivial)⟩

/-- Actual near-target execution retains reads outside its four original destinations. -/
lemma scaleInto_callerFrame
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : AvoidsStageWrites refs other .near) :
    (LatticeNearTargetScale.scaleStep refs.nearTarget store).1.read other = store.read other :=
  LatticeNearTargetScale.scaleInto_callerFrame refs.nearTarget store other
    (fun cell => avoids (.nearTarget cell) (by trivial))

/-- Actual exponent execution retains reads outside its seven original destinations. -/
lemma candidateExponentInto_callerFrame
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : AvoidsStageWrites refs other .exponent) :
    (LatticeCandidateExponent.exponentStep refs.exponent store).1.read other = store.read other :=
  LatticeCandidateExponent.candidateExponentInto_callerFrame refs.exponent store other
    (fun cell => avoids (.exponent cell) (by trivial))

/-- Actual power execution retains caller reads outside its result and equality predicate. -/
lemma candidatePowerInto_callerFrame
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : AvoidsStageWrites refs other .power) :
    (LatticeCandidatePowerMachine.candidateStep spec refs.power store).1.read other =
      store.read other :=
  LatticeCandidatePowerMachine.candidatePowerInto_callerFrame spec refs.power store other
    (avoids .power (by trivial)) (avoids .powerAccepted (by trivial))

/-- Actual conjunctions and first-success selection retain all other caller reads. -/
lemma candidateSelectorInto_callerFrame
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : AvoidsStageWrites refs other .selector) :
    (LatticeCandidateSelector.selectorStep refs.selector store).1.read other =
      store.read other := by
  apply LatticeCandidateSelector.candidateSelectorInto_callerFrame refs.selector store other
  intro cell
  cases cell with
  | intermediate => exact avoids .selectorIntermediate (by trivial)
  | eligible => exact avoids .selectorEligible (by trivial)
  | accepted => exact avoids (.selection .accepted) (by trivial)
  | selected => exact avoids (.selection .selected) (by trivial)

/-- Every actual stage retains a caller read outside the complete slot footprint. -/
lemma candidateSlotInto_callerFrame
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : CallerFrameAvoids refs other) :
    (LatticeCandidateSlotMachine.candidateSlotStep spec offset refs store).1.read other =
      store.read other := by
  dsimp only [LatticeCandidateSlotMachine.candidateSlotStep,
    LatticeCandidateSlotMachine.rangeChecksStep, LatticeCandidateSlotMachine.exponentChecksStep,
    LatticeCandidateSlotMachine.powerSelectionStep]
  rw [candidateSelectorInto_callerFrame refs _ other avoids.selector,
    candidatePowerInto_callerFrame spec refs _ other avoids.power,
    candidateExponentInto_callerFrame refs _ other avoids.exponent,
    scaleInto_callerFrame refs _ other avoids.near,
    candidateDistancePrefixInto_callerFrame offset refs store other avoids.distance]

/-- Each original external source survives the complete actual slot execution. -/
lemma candidateSlotInto_external_frame
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) (store : Store ctx) (source : ExternalSourceCell) :
    (LatticeCandidateSlotMachine.candidateSlotStep spec offset refs store).1.read
      (externalSourceInput refs source) = store.read (externalSourceInput refs source) :=
  candidateSlotInto_callerFrame spec offset refs store (externalSourceInput refs source)
    ⟨separation.externalAvoidsStage source .distance, separation.externalAvoidsStage source .near,
      separation.externalAvoidsStage source .exponent, separation.externalAvoidsStage source .power,
      separation.externalAvoidsStage source .selector⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotFrames
