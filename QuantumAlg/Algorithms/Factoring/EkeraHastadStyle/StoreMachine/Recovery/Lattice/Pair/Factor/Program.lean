/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Resources.Budget
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program.Guarded

/-!
# Actual pair-to-factor recovery

The complete actual pair-to-short-log circuit runs before guarded quadratic
recovery. The direct short-log selector and persistent factor selector keep
their original distinct roles. Every later pair still executes after a factor
has been selected, while the first factor and complete caller frame persist.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairFactorRecovery

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Pair recovery and quadratic recovery wired through one short-log latch. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the pair stage. -/
  pair : LatticePairCandidateRecovery.Refs ctx N
  /-- Nested references for the quadratic stage. -/
  quadratic : QuadraticRecoveryGuarded.Refs ctx
    (LatticePairCandidateRecovery.Width N)
  sharedShortLog :
    quadratic.shortLogSelection = pair.scan.selector.selection

/-- Entry facts for the pair machine and persistent quadratic constants. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (input : Input N) (generator : (ZMod N)ˣ)
    (before : Store ctx) (refs : Refs ctx N) : Prop where
  pair : LatticePairCandidateRecovery.InitialConditions input generator before refs.pair
  quadratic : QuadraticRecoveryGuarded.InitialConditions N before refs.quadratic

/-- Both local certificates and pair-prefix frames of quadratic constants. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  pair : LatticePairCandidateRecovery.Separation refs.pair
  quadratic : QuadraticRecoveryGuarded.Separation refs.quadratic
  modulusFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    refs.quadratic.quadratic.recovery.candidates.quadraticPrefix.modulus
  firstOneFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    refs.quadratic.quadratic.recovery.pair.first.check.one
  firstModulusFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    refs.quadratic.quadratic.recovery.pair.first.check.positiveCheck.modulus
  firstZeroFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    refs.quadratic.quadratic.recovery.pair.first.check.positiveCheck.zero
  secondOneFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    refs.quadratic.quadratic.recovery.pair.second.check.one
  secondModulusFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    refs.quadratic.quadratic.recovery.pair.second.check.positiveCheck.modulus
  secondZeroFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    refs.quadratic.quadratic.recovery.pair.second.check.positiveCheck.zero
  factorAcceptedFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    (FirstAccepted.cellRead
      (QuadraticRecoveryGuarded.factorSelection refs.quadratic).accepted)
  factorSelectedFrame : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair
    (FirstAccepted.cellRead
      (QuadraticRecoveryGuarded.factorSelection refs.quadratic).selected)

/-- One caller read avoids every write of pair and quadratic recovery. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : Refs ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  pair : LatticePairCandidateRecovery.CallerFrameAvoids refs.pair other
  quadratic : QuadraticRecoveryGuarded.CallerFrameAvoids refs.quadratic other

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Optional quadratic projection is precisely the original pair factor result. -/
theorem recoveryOption_recoverShortLogFromPair (m ell : Nat) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    QuadraticRecoveryGuarded.recoveryOption N
        (RSA.recoverShortLogFromPair m ell generator samples) =
      RSA.recoverFactorFromShortLogPair m ell generator samples := by
  rw [RSA.recoverFactorFromShortLogPair_eq_run]
  cases RSA.recoverShortLogFromPair m ell generator samples <;> rfl

/-- Execute the complete pair short-log recovery before optional quadratic factor recovery. -/
def into (input : Input N) (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs.pair)
    (QuadraticRecoveryGuarded.into refs.quadratic)

/-- Actual full store and both chronological component paths of pair-to-factor recovery. -/
def step (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (into input refs).Path :=
  Circuit.sequenceRecord
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs.pair)
    (QuadraticRecoveryGuarded.into refs.quadratic)
    (LatticePairCandidateRecovery.recoveryStep input refs.pair)
    (QuadraticRecoveryGuarded.step refs.quadratic) store

/-- Project the actual final store while keeping the finite candidate scan folded. -/
theorem step_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (step input refs store).1 = (QuadraticRecoveryGuarded.step refs.quadratic
      (LatticePairCandidateRecovery.recoveryStep input refs.pair store).1).1 :=
  Circuit.sequenceRecord_store _ _ _ _ store

/-- The actual composition executes its whole record on all histories and external references. -/
theorem into_execute (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into input refs).execute Reference state = state.mapClassical (fun entry =>
      ((step input refs entry.1).1, (entry.2, (step input refs entry.1).2))) := by
  dsimp only [into, step]
  exact Circuit.execute_sequenceRecord _ _ _ _
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto_execute input refs.pair)
    (QuadraticRecoveryGuarded.into_execute refs.quadratic) Reference state

private theorem scanOffsets_frame {coordinateWidth modulusWidth : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (items : List NumberTheory.IntegerPoint3) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : LatticeCandidateSlotFrames.CallerFrameAvoids refs other) :
    (LatticeCandidateScan.scanOffsetsStep spec refs items store).1.read other =
      store.read other := by
  induction items generalizing store with
  | nil => rfl
  | cons offset tail ih =>
      exact (ih (LatticeCandidateSlotMachine.candidateSlotStep spec offset refs store).1).trans
        (LatticeCandidateSlotFrames.candidateSlotInto_callerFrame
          spec offset refs store other avoids)

private theorem scan_frame {coordinateWidth modulusWidth : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : LatticeCandidateSlotFrames.CallerFrameAvoids refs other) :
    (LatticeCandidateScan.scanStep spec refs store).1.read other = store.read other := by
  unfold LatticeCandidateScan.scanStep
  exact scanOffsets_frame spec refs _ store other avoids

private theorem pair_frame (input : Input N) (refs : LatticePairCandidateRecovery.Refs ctx N)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : LatticePairCandidateRecovery.CallerFrameAvoids refs other) :
    (LatticePairCandidateRecovery.recoveryStep input refs store).1.read other =
      store.read other := by
  rw [LatticePairCandidateRecovery.recoveryStep_store,
    LatticeCandidateScanInitialized.initializedStep_store]
  exact (scan_frame _ refs.scan _ other avoids.scan).trans
    ((LatticeCandidateSelectorInit.clearAcceptedInto_callerFrame refs.scan.selector.selection
      _ other (avoids.scan.selector (.selection .accepted) (by trivial))).trans
      (LatticePairCandidateRecovery.pairCandidatePrefix_callerFrame input refs store other avoids))

/-- All structural reads outside both complete footprints survive, on every numerical input. -/
theorem into_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step input refs store).1.read other = store.read other := by
  rw [step_store]
  exact (QuadraticRecoveryGuarded.into_callerFrame refs.quadratic _ other avoids.quadratic).trans
    (pair_frame input refs.pair store other avoids.pair)

/-- Exact source pair result with persistent first-factor retention and complete caller frame. -/
structure Relation (generator : (ZMod N)ˣ) (refs : Refs ctx N)
    (before after : Store ctx) : Prop where
  selected : QuadraticCandidateSelect.selectedOption
      (QuadraticRecoveryGuarded.factorSelection refs.quadratic) after =
    FirstAccepted.retainFirst
      (QuadraticCandidateSelect.selectedOption
        (QuadraticRecoveryGuarded.factorSelection refs.quadratic) before)
      (RSA.recoverFactorFromShortLogPair (shortLogBits N) (tradeoffBits N) generator
        (LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair.pair before))
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

private theorem guardedInitial_afterPair (input : Input N) (generator : (ZMod N)ˣ)
    (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input generator store refs) :
    QuadraticRecoveryGuarded.InitialConditions N
      (LatticePairCandidateRecovery.recoveryStep input refs.pair store).1 refs.quadratic := by
  have modulus := pair_frame input refs.pair store _ separation.modulusFrame
  have one₁ := pair_frame input refs.pair store _ separation.firstOneFrame
  have modulus₁ := pair_frame input refs.pair store _ separation.firstModulusFrame
  have zero₁ := pair_frame input refs.pair store _ separation.firstZeroFrame
  have one₂ := pair_frame input refs.pair store _ separation.secondOneFrame
  have modulus₂ := pair_frame input refs.pair store _ separation.secondModulusFrame
  have zero₂ := pair_frame input refs.pair store _ separation.secondZeroFrame
  refine ⟨?_, (congrArg CShape.Value.toNat modulus).trans initial.quadratic.modulusValue⟩
  unfold QuadraticCandidatePairSelect.InitialConditions
    QuadraticCandidateCheck.TotalInitialConditions
  rw [one₁, modulus₁, zero₁, one₂, modulus₂, zero₂]
  exact initial.quadratic.pair

/-- Actual pair recovery and guarded projection compute the first original factor candidate. -/
theorem into_correct (input : Input N) (generator : (ZMod N)ˣ) (refs : Refs ctx N)
    (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input generator store refs) :
    Relation generator refs store (step input refs store).1 := by
  let middle := (LatticePairCandidateRecovery.recoveryStep input refs.pair store).1
  have pairResult := LatticePairCandidateRecovery.pairCandidateRecoveryInto_correct
    input generator refs.pair separation.pair store initial.pair
  have sourceValue : QuadraticRecoveryGuarded.sourceOption
      refs.quadratic.shortLogSelection middle =
      RSA.recoverShortLogFromPair (shortLogBits N) (tradeoffBits N) generator
        (LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair.pair store) := by
    rw [refs.sharedShortLog]
    exact pairResult.selected
  have accepted := pair_frame input refs.pair store _ separation.factorAcceptedFrame
  have selected := pair_frame input refs.pair store _ separation.factorSelectedFrame
  have factorFrame : QuadraticCandidateSelect.selectedOption
      (QuadraticRecoveryGuarded.factorSelection refs.quadratic) middle =
      QuadraticCandidateSelect.selectedOption
        (QuadraticRecoveryGuarded.factorSelection refs.quadratic) store := by
    unfold QuadraticCandidateSelect.selectedOption FirstAccepted.selectedOption
    rw [accepted, selected]
  have guardedInitial := guardedInitial_afterPair input generator refs separation store initial
  have guarded := QuadraticRecoveryGuarded.into_correct N refs.quadratic separation.quadratic
    middle guardedInitial
  refine ⟨?_, into_callerFrame input refs store⟩
  rw [step_store]
  have result := guarded.selected
  rw [factorFrame, sourceValue, recoveryOption_recoverShortLogFromPair] at result
  exact result

/-- Independent native allowance of complete pair recovery and its guarded quadratic projection. -/
def eventEnvelope (N : Nat) : ResourcePool kind :=
  LatticePairCandidateRecovery.recoveryEventEnvelope N +
    QuadraticRecoveryGuarded.eventEnvelope (LatticePairCandidateRecovery.Width N)

/-- Independent sequential unit-duration depth allowance for the complete pair-to-factor circuit. -/
def depthBound (N : Nat) : Nat :=
  LatticePairCandidateRecovery.recoveryDepthBound N +
    (7 * QuadraticPrefix.discriminantWidth (LatticePairCandidateRecovery.Width N) + 38)

/-- The actual chronological event trace executes pair recovery before its guarded projection. -/
theorem into_events (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).eventTrace path =
      (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs.pair).eventTrace path.1 ++
        (QuadraticRecoveryGuarded.into refs.quadratic).eventTrace path.2 := rfl

/-- Native multiplicities add both actual component ledgers from the same chronological path. -/
theorem into_resourcePool (input : Input N) (refs : Refs ctx N)
    (path : (into input refs).Path) :
    (into input refs).resourcePool path =
      (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs.pair).resourcePool path.1 +
        (QuadraticRecoveryGuarded.into refs.quadratic).resourcePool path.2 :=
  ResourcePool.ofList_append _ _

private theorem guarded_pool_le
    (refs : QuadraticRecoveryGuarded.Refs ctx (LatticePairCandidateRecovery.Width N))
    (path : (QuadraticRecoveryGuarded.into refs).Path) :
    (QuadraticRecoveryGuarded.into refs).resourcePool path ≤
      QuadraticRecoveryGuarded.eventEnvelope (LatticePairCandidateRecovery.Width N) := by
  generalize widthEq : LatticePairCandidateRecovery.Width N = width at refs path ⊢
  exact QuadraticRecoveryGuarded.into_pool_le refs path

private theorem sequence_pool_le (first second : Circuit ctx ctx)
    (firstBudget secondBudget : ResourcePool kind)
    (firstBound : ∀ path, first.resourcePool path ≤ firstBudget)
    (secondBound : ∀ path, second.resourcePool path ≤ secondBudget)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path ≤ firstBudget + secondBudget := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (firstBound path.1) (secondBound path.2)

/-- All native event coordinates satisfy the independent complete component allowances. -/
theorem into_pool_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).resourcePool path ≤ eventEnvelope N := by
  unfold into at path ⊢
  unfold eventEnvelope
  with_reducible
    exact sequence_pool_le
      (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs.pair)
      (QuadraticRecoveryGuarded.into refs.quadratic)
      (LatticePairCandidateRecovery.recoveryEventEnvelope N)
      (QuadraticRecoveryGuarded.eventEnvelope (LatticePairCandidateRecovery.Width N))
      (LatticePairCandidateRecovery.pairCandidateRecoveryInto_pool_le input refs.pair)
      (guarded_pool_le (N := N) refs.quadratic) path

/-- Every actual path includes both component dependency depths within the independent sum. -/
theorem into_depth_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).depth (fun _ => 1) path ≤ depthBound N :=
  Nat.add_le_add
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto_depth_le input refs.pair path.1)
    (QuadraticRecoveryGuarded.into_depth_le refs.quadratic path.2)

/-- Resident space includes every original cell and the reusable native-power scope. -/
theorem into_resident_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakResidentSpace path ≤ ctx.residentSpace +
      Modular.NativePower.powerSpace kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs.pair)
    (QuadraticRecoveryGuarded.into refs.quadratic) path).le.trans ?_
  exact SpacePool.max_le
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto_resident_le input refs.pair path.1)
    ((QuadraticRecoveryGuarded.into_resident_le refs.quadratic path.2).trans
      (le_add_of_nonneg_right zero_le))

/-- Auxiliary space reuses one native-power scope and retains all existing workspace roles. -/
theorem into_auxiliary_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      Modular.NativePower.powerSpace kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto input refs.pair)
    (QuadraticRecoveryGuarded.into refs.quadratic) path).le.trans ?_
  exact SpacePool.max_le
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto_auxiliary_le input refs.pair path.1)
    ((QuadraticRecoveryGuarded.into_auxiliary_le refs.quadratic path.2).trans
      (le_add_of_nonneg_right zero_le))

/-- Both actual component circuits restore the full borrowed-reference joint state. -/
theorem into_borrowedRestored (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into input refs).BorrowedRestored Reference state
      ((into input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticePairCandidateRecovery.pairCandidateRecoveryInto_borrowedRestored input refs.pair
      Reference state)
    (QuadraticRecoveryGuarded.into_borrowedRestored refs.quadratic Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairFactorRecovery
