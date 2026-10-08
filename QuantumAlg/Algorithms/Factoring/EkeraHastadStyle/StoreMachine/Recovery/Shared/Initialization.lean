/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Initialization
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual shared modular and quadratic initialization

The existing shared setup computes its original target power, then four actual
classical instructions initialize the persistent quadratic constants. Both
stages retain their complete stores, native paths and quantum-reference blocks.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSharedQuadraticInitialization

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Original shared modular outputs and the independent quadratic package. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  setup : LatticeCandidateModularSetup.Refs ctx N
  quadratic : QuadraticScratchLayout.Cells ctx N

/-- The actual shared modulus retains its original widened word shape. -/
def modulusSource {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : CInputRef ctx (.unsignedWord (modulusBits N + 1)) :=
  LatticeCandidateModularSetup.writeInput refs.setup.modulus

/-- Entry assumptions are exactly the original sampled-parameter and base-domain contract. -/
def InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (input : Input N) (store : Store ctx) (refs : Refs ctx N) : Prop :=
  LatticeCandidateModularSetup.InitialConditions input store refs.setup

/-- The three exact persistent constants read from the actual initialized quadratic store. -/
structure QuadraticConstants {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (N : Nat) (cells : QuadraticScratchLayout.Cells ctx N) (store : Store ctx) : Prop where
  modulus : (store.read (QuadraticScratchViews.modulusInput cells)).toNat = N
  one : (store.read (QuadraticScratchViews.oneInput cells)).toNat = 1
  zero : (store.read (QuadraticScratchViews.zeroInput cells)).toNat = 0

/-- Original component separation plus preservation of all live shared outputs. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  setup : LatticeCandidateModularSetup.Separation refs.setup
  quadratic : QuadraticScratchInitialization.Separation (modulusSource refs) refs.quadratic
  parameterQuadratic : QuadraticScratchInitialization.CallerFrameAvoids
    refs.quadratic refs.setup.parameter
  baseQuadratic : QuadraticScratchInitialization.CallerFrameAvoids refs.quadratic
    (LatticeCandidateModularSetup.parameterBaseInput refs.setup)
  generatorQuadratic : QuadraticScratchInitialization.CallerFrameAvoids refs.quadratic
    (LatticeCandidateModularSetup.writeInput refs.setup.generator)
  exponentQuadratic : QuadraticScratchInitialization.CallerFrameAvoids refs.quadratic
    (LatticeCandidateModularSetup.writeInput refs.setup.targetExponent)
  targetPowerQuadratic : QuadraticScratchInitialization.CallerFrameAvoids refs.quadratic
    (LatticeCandidateModularSetup.writeInput refs.setup.targetPower)

/-- All original shared writes and all three quadratic destinations avoided by a caller read. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop where
  setup : ∀ cell, LatticeCandidateModularSetup.mutableKey refs.setup cell ∉ other.storageKeys
  quadratic : QuadraticScratchInitialization.CallerFrameAvoids refs.quadratic other

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Execute actual shared target powering and then initialize all persistent quadratic constants. -/
def into (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (LatticeCandidateModularSetup.setupInto input refs.setup)
    (QuadraticScratchInitialization.into (modulusSource refs) refs.quadratic)

/-- Record the actual intermediate store and both chronological paths of the shared prefix. -/
def step (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (into input refs).Path :=
  Circuit.sequenceStoreRecord (LatticeCandidateModularSetup.setupInto input refs.setup)
    (QuadraticScratchInitialization.into (modulusSource refs) refs.quadratic)
    (LatticeCandidateModularSetup.setupStep input refs.setup)
    (QuadraticScratchInitialization.step (modulusSource refs) refs.quadratic) store

/-- The quadratic initializer consumes the actual shared setup output store. -/
theorem step_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (step input refs store).1 =
      (QuadraticScratchInitialization.step (modulusSource refs) refs.quadratic
        (LatticeCandidateModularSetup.setupStep input refs.setup store).1).1 :=
  rfl

/-- Complete shared-prefix execution preserves actual quantum-reference blocks and history. -/
theorem into_execute (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into input refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord _ _ _ _
    (LatticeCandidateModularSetup.setupInto_execute input refs.setup)
    (QuadraticScratchInitialization.into_execute (modulusSource refs) refs.quadratic)
    Reference state

/-- Reads outside every actual write survive without initialization or domain premises. -/
theorem into_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step input refs store).1.read other = store.read other := by
  rw [step_store]
  exact (QuadraticScratchInitialization.into_callerFrame (modulusSource refs) refs.quadratic
    _ other avoids.quadratic).trans
      (LatticeCandidateModularSetup.setupInto_callerFrame input refs.setup store other avoids.setup)

/-- All shared outputs, the retained parameter domain, quadratic constants and caller frame. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (input : Input N) (refs : Refs ctx N) (before after : Store ctx) : Prop where
  initial : InitialConditions input after refs
  generator : after.read (LatticeCandidateModularSetup.writeInput refs.setup.generator) =
    CShape.packCanonicalResidue (modulusBits N)
      (before.read (LatticeCandidateModularSetup.parameterBaseInput refs.setup))
  generatorValue : (after.read (LatticeCandidateModularSetup.writeInput
    refs.setup.generator)).residueEncoding.val =
      LatticeCandidateModularSetup.parameterBase refs.setup before
  modulus : (after.read (modulusSource refs)).toNat = N
  exponent : (after.read (LatticeCandidateModularSetup.writeInput
    refs.setup.targetExponent)).toNat = RSA.targetExponent N
  targetPower : (after.read (LatticeCandidateModularSetup.writeInput
    refs.setup.targetPower)).toNat =
      LatticeCandidateModularSetup.parameterBase refs.setup before ^ RSA.targetExponent N % N
  quadratic : QuadraticConstants N refs.quadratic after
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- Real initialization preserves the sampled parameter and establishes every shared result. -/
theorem into_correct (input : Input N) (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions input store refs) :
    Relation input refs store (step input refs store).1 := by
  let middle := (LatticeCandidateModularSetup.setupStep input refs.setup store).1
  have setup := LatticeCandidateModularSetup.setupInto_correct
    input refs.setup separation.setup store initial
  have initialized := QuadraticScratchInitialization.into_correct input
    (modulusSource refs) refs.quadratic separation.quadratic middle setup.modulus
  have frame {shape : CShape} (other : CInputRef ctx shape)
      (avoids : QuadraticScratchInitialization.CallerFrameAvoids refs.quadratic other) :
      (step input refs store).1.read other = middle.read other := by
    rw [step_store]
    exact initialized.callerFrame other avoids
  have parameterFrame := into_callerFrame input refs store refs.setup.parameter
    ⟨separation.setup.parameterAvoidsMutable, separation.parameterQuadratic⟩
  have baseFrame : (step input refs store).1.read
      (LatticeCandidateModularSetup.parameterBaseInput refs.setup) =
      store.read (LatticeCandidateModularSetup.parameterBaseInput refs.setup) :=
    congrArg CShape.Value.first parameterFrame
  have modulusFrame := frame (modulusSource refs)
    ⟨separation.quadratic.sourceAvoidsModulus, separation.quadratic.sourceAvoidsOne,
      separation.quadratic.sourceAvoidsZero⟩
  refine ⟨?_, (frame _ separation.generatorQuadratic).trans setup.generator,
    (congrArg (fun value => value.residueEncoding.val)
      (frame _ separation.generatorQuadratic)).trans setup.generatorValue,
    (congrArg CShape.Value.toNat modulusFrame).trans setup.modulus,
    (congrArg CShape.Value.toNat (frame _ separation.exponentQuadratic)).trans setup.exponent,
    (congrArg CShape.Value.toNat (frame _ separation.targetPowerQuadratic)).trans setup.targetPower,
    ?_, into_callerFrame input refs store⟩
  · refine ⟨?_, ?_⟩
    · obtain ⟨sample, sampled⟩ := initial.sampled
      exact ⟨sample, parameterFrame.trans sampled⟩
    · change ((step input refs store).1.read
        (LatticeCandidateModularSetup.parameterBaseInput refs.setup)).toNat < N
      rw [baseFrame]
      exact initial.baseLt
  · rw [step_store]
    exact ⟨initialized.modulus, initialized.one, initialized.zero⟩

/-- Initialized physical constants establish guarded recovery for both canonical selector types. -/
theorem guardedInitialConditions_of_relation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} (input : Input N) (refs : Refs ctx N)
    (shortLogSelection : FirstAccepted.Direct.Refs ctx (QuadraticScratchLayout.ShortWidth N))
    (factorSelection : FirstAccepted.Refs ctx (QuadraticScratchLayout.CandidateWidth N))
    (before after : Store ctx) (holds : Relation input refs before after) :
    QuadraticRecoveryGuarded.InitialConditions N after
      (QuadraticScratchViews.guardedRefs refs.quadratic shortLogSelection factorSelection) :=
  QuadraticScratchInitialization.guardedInitialConditions_of_values input refs.quadratic
    shortLogSelection factorSelection after
    holds.quadratic.modulus holds.quadratic.one holds.quadratic.zero

/-- Independent original setup allowance plus the four literal quadratic initialization events. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  LatticeCandidateModularSetup.setupEventEnvelope model (modulusBits N) +
    QuadraticScratchInitialization.eventEnvelope N

/-- Independent dependency depth includes both target powering and the four constant operations. -/
def depthBound (N : Nat) : Nat := 12 * modulusBits N + 12

/-- Every actual path meets the independent complete native-event allowance. -/
theorem into_pool_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).resourcePool path ≤ eventEnvelope N := by
  change ResourcePool.ofList
    ((LatticeCandidateModularSetup.setupInto input refs.setup).eventTrace path.1 ++
      (QuadraticScratchInitialization.into (modulusSource refs) refs.quadratic).eventTrace
        path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (LatticeCandidateModularSetup.setupInto_pool_le input refs.setup path.1)
    (QuadraticScratchInitialization.into_resourcePool (modulusSource refs) refs.quadratic path.2).le

/-- Actual unit-duration depth includes both original setup and the four-operation suffix. -/
theorem into_depth_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).depth (fun _ => 1) path ≤ depthBound N := by
  have setup := LatticeCandidateModularSetup.setupInto_depth_le input refs.setup path.1
  have quadratic := QuadraticScratchInitialization.into_depth
    (modulusSource refs) refs.quadratic path.2
  change (LatticeCandidateModularSetup.setupInto input refs.setup).depth (fun _ => 1) path.1 +
    (QuadraticScratchInitialization.into (modulusSource refs) refs.quadratic).depth
      (fun _ => 1) path.2 ≤ _
  unfold depthBound
  omega

/-- Actual resident space includes all caller cells and the real native-power temporary scope. -/
theorem into_resident_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakResidentSpace path ≤
      ctx.residentSpace + Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq (LatticeCandidateModularSetup.setupInto input refs.setup)
    (QuadraticScratchInitialization.into (modulusSource refs) refs.quadratic) path).le.trans ?_
  exact SpacePool.max_le
    (LatticeCandidateModularSetup.setupInto_resident_le input refs.setup path.1)
    ((QuadraticScratchInitialization.into_resident_le
      (modulusSource refs) refs.quadratic path.2).trans
      (le_add_of_nonneg_right zero_le))

/-- Actual auxiliary space counts the same live native-power scratch and all existing roles. -/
theorem into_auxiliary_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq (LatticeCandidateModularSetup.setupInto input refs.setup)
    (QuadraticScratchInitialization.into (modulusSource refs) refs.quadratic) path).le.trans ?_
  exact SpacePool.max_le
    (LatticeCandidateModularSetup.setupInto_auxiliary_le input refs.setup path.1)
    ((QuadraticScratchInitialization.into_auxiliary_le
      (modulusSource refs) refs.quadratic path.2).trans
      (le_add_of_nonneg_right zero_le))

/-- The complete shared prefix restores every borrowed correlation with arbitrary references. -/
theorem into_borrowedRestored (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into input refs).BorrowedRestored Reference state
      ((into input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeCandidateModularSetup.setupInto_borrowedRestored input refs.setup Reference state)
    (QuadraticScratchInitialization.into_borrowedRestored
      (modulusSource refs) refs.quadratic Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSharedQuadraticInitialization
