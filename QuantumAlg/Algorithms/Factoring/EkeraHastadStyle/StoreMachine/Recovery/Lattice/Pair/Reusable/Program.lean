/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Reset

/-!
# Actual reusable recovery for one retained terminal pair

All thirteen original reset writes execute before the complete pair-to-factor
circuit, even when an earlier pair has already supplied a factor. Actual reset
establishes the required LLL source zeros and preserves the original parameter,
measurement cells, quadratic constants and persistent factor selection.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairReusableRecovery

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The first terminal source consumed by the reusable pair package. -/
abbrev firstTerminal {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) :=
  BatchMachine.terminalInput
    (LatticePairRecoveryReset.wideRefs refs).initialization.pair.first

/-- The second terminal source consumed by the reusable pair package. -/
abbrev secondTerminal {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) :=
  BatchMachine.terminalInput
    (LatticePairRecoveryReset.wideRefs refs).initialization.pair.second

/-- Persistent entry facts; the pair scratch zero facts are supplied by the
literal reset rather than assumed from the caller. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (input : Input N) (generator : (ZMod N)ˣ)
    (before : Store ctx)
    (refs : LatticePairFactorRecovery.Refs ctx N) : Prop where
  setup : LatticeCandidateModularSetup.InitialConditions input before refs.pair.setup
  generatorAtEntry : generator =
    parameterUnit (before.read refs.pair.setup.parameter)
  quadratic : QuadraticRecoveryGuarded.InitialConditions N before refs.quadratic

/-- Every original persistent parameter, terminal bit and selector read framed by reset. -/
structure ResetFrames {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) : Prop where
  firstTerminalBits : ∀ index,
    LatticePairRecoveryReset.CallerFrameAvoids refs
      (.bitsGet (firstTerminal refs) index)
  secondTerminalBits : ∀ index,
    LatticePairRecoveryReset.CallerFrameAvoids refs
      (.bitsGet (secondTerminal refs) index)
  setupParameter : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.pair.setup.parameter
  setupBase : LatticePairRecoveryReset.CallerFrameAvoids refs
    (LatticeCandidateModularSetup.parameterBaseInput refs.pair.setup)
  quadraticModulus : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.quadratic.quadratic.recovery.candidates.quadraticPrefix.modulus
  firstOne : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.quadratic.quadratic.recovery.pair.first.check.one
  firstModulus : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.quadratic.quadratic.recovery.pair.first.check.positiveCheck.modulus
  firstZero : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.quadratic.quadratic.recovery.pair.first.check.positiveCheck.zero
  secondOne : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.quadratic.quadratic.recovery.pair.second.check.one
  secondModulus : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.quadratic.quadratic.recovery.pair.second.check.positiveCheck.modulus
  secondZero : LatticePairRecoveryReset.CallerFrameAvoids refs
    refs.quadratic.quadratic.recovery.pair.second.check.positiveCheck.zero
  factorAccepted : LatticePairRecoveryReset.CallerFrameAvoids refs
    (FirstAccepted.cellRead
      (QuadraticRecoveryGuarded.factorSelection refs.quadratic).accepted)
  factorSelected : LatticePairRecoveryReset.CallerFrameAvoids refs
    (FirstAccepted.cellRead
      (QuadraticRecoveryGuarded.factorSelection refs.quadratic).selected)

/-- Local certificates for reset and recovery, plus their cross-stage frames. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) : Prop where
  reset : LatticePairRecoveryReset.Separation refs
  recovery : LatticePairFactorRecovery.Separation refs
  resetFrames : ResetFrames refs

/-- One caller read avoids both stages of reusable pair recovery. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : LatticePairFactorRecovery.Refs ctx N)
    {shape : CShape} (other : CInputRef ctx shape) : Prop where
  reset : LatticePairRecoveryReset.CallerFrameAvoids refs other
  recovery : LatticePairFactorRecovery.CallerFrameAvoids refs other

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Always execute the complete paid reset and the complete next pair recovery. -/
def into (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticePairRecoveryReset.into refs) (LatticePairFactorRecovery.into input refs)

/-- One actual full-store record connects reset to the original finite pair-recovery circuit. -/
def step (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N) (store : Store ctx) :
    Store ctx × (into input refs).Path :=
  Circuit.sequenceRecord (LatticePairRecoveryReset.into refs)
    (LatticePairFactorRecovery.into input refs) (LatticePairRecoveryReset.step refs)
    (LatticePairFactorRecovery.step input refs) store

/-- The complete final store is the actual pair result on the reset store. -/
theorem step_store (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (store : Store ctx) :
    (step input refs store).1 = (LatticePairFactorRecovery.step input refs
      (LatticePairRecoveryReset.step refs store).1).1 := Circuit.sequenceRecord_store _ _ _ _ store

/-- The chronological reset-and-recovery record executes on all histories and references. -/
theorem into_execute (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into input refs).execute Reference state = state.mapClassical (fun entry =>
      ((step input refs entry.1).1, (entry.2, (step input refs entry.1).2))) := by
  dsimp only [into, step]
  exact Circuit.execute_sequenceRecord _ _ _ _ (LatticePairRecoveryReset.into_execute refs)
    (LatticePairFactorRecovery.into_execute input refs) Reference state

/-- All original structural reads outside both footprints survive on every numerical input. -/
theorem into_callerFrame (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : CallerFrameAvoids refs other) :
    (step input refs store).1.read other = store.read other := by
  rw [step_store]
  exact (LatticePairFactorRecovery.into_callerFrame input refs _ other avoids.recovery).trans
    (LatticePairRecoveryReset.into_callerFrame refs store other avoids.reset)

private theorem quadraticInitial_afterReset (refs : LatticePairFactorRecovery.Refs ctx N)
    (store : Store ctx) (frames : ResetFrames refs)
    (initial : QuadraticRecoveryGuarded.InitialConditions N store refs.quadratic) :
    QuadraticRecoveryGuarded.InitialConditions N (LatticePairRecoveryReset.step refs store).1
      refs.quadratic := by
  have firstOne := LatticePairRecoveryReset.into_callerFrame refs store _ frames.firstOne
  have firstModulus := LatticePairRecoveryReset.into_callerFrame refs store _ frames.firstModulus
  have firstZero := LatticePairRecoveryReset.into_callerFrame refs store _ frames.firstZero
  have secondOne := LatticePairRecoveryReset.into_callerFrame refs store _ frames.secondOne
  have secondModulus := LatticePairRecoveryReset.into_callerFrame refs store _ frames.secondModulus
  have secondZero := LatticePairRecoveryReset.into_callerFrame refs store _ frames.secondZero
  have modulus := LatticePairRecoveryReset.into_callerFrame refs store _ frames.quadraticModulus
  refine ⟨?_, (congrArg CShape.Value.toNat modulus).trans initial.modulusValue⟩
  unfold QuadraticCandidatePairSelect.InitialConditions
    QuadraticCandidateCheck.TotalInitialConditions
  rw [firstOne, firstModulus, firstZero, secondOne, secondModulus, secondZero]
  exact initial.pair

/-- The actual reset supplies all needed LLL initialization, with no caller premise. -/
theorem factorInitial_afterReset (input : Input N) (generator : (ZMod N)ˣ)
    (refs : LatticePairFactorRecovery.Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input generator store refs) :
    LatticePairFactorRecovery.InitialConditions input generator
      (LatticePairRecoveryReset.step refs store).1 refs := by
  have reset := LatticePairRecoveryReset.into_correct refs separation.reset store
  have parameterFrame := reset.callerFrame _ separation.resetFrames.setupParameter
  have setup := LatticePairCandidateRecovery.setupInitial_transport input refs.pair.setup
    store _ initial.setup parameterFrame
  have generatorAtReset : generator =
      parameterUnit
        ((LatticePairRecoveryReset.step refs store).1.read refs.pair.setup.parameter) := by
    rw [parameterFrame]
    exact initial.generatorAtEntry
  exact ⟨⟨reset.initial, setup, generatorAtReset⟩,
    quadraticInitial_afterReset refs store separation.resetFrames initial.quadratic⟩

/-- The original pair measurement values survive all thirteen actual reset writes. -/
theorem sourceSamples_afterReset (refs : LatticePairFactorRecovery.Refs ctx N)
    (frames : ResetFrames refs) (store : Store ctx) :
    LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair.pair
        (LatticePairRecoveryReset.step refs store).1 =
      LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair.pair store := by
  have firstBits : BatchMachine.sourceBits N (LatticePairRecoveryReset.step refs store).1
      (firstTerminal refs) = BatchMachine.sourceBits N store (firstTerminal refs) := by
    funext index
    unfold BatchMachine.sourceBits
    exact congrArg CShape.Value.toBool
      (LatticePairRecoveryReset.into_callerFrame refs store _ (frames.firstTerminalBits index))
  have secondBits : BatchMachine.sourceBits N (LatticePairRecoveryReset.step refs store).1
      (secondTerminal refs) = BatchMachine.sourceBits N store (secondTerminal refs) := by
    funext index
    unfold BatchMachine.sourceBits
    exact congrArg CShape.Value.toBool
      (LatticePairRecoveryReset.into_callerFrame refs store _ (frames.secondTerminalBits index))
  change (BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N (LatticePairRecoveryReset.step refs store).1 (firstTerminal refs)),
    BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N (LatticePairRecoveryReset.step refs store).1
        (secondTerminal refs))) =
    (BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N store (firstTerminal refs)),
    BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N store (secondTerminal refs)))
  rw [firstBits, secondBits]

/-- Reset retains the optional factor from every preceding pair. -/
theorem factorOption_afterReset (refs : LatticePairFactorRecovery.Refs ctx N)
    (frames : ResetFrames refs) (store : Store ctx) :
    QuadraticCandidateSelect.selectedOption
        (QuadraticRecoveryGuarded.factorSelection refs.quadratic)
        (LatticePairRecoveryReset.step refs store).1 =
      QuadraticCandidateSelect.selectedOption
        (QuadraticRecoveryGuarded.factorSelection refs.quadratic) store := by
  have accepted := LatticePairRecoveryReset.into_callerFrame refs store _ frames.factorAccepted
  have selected := LatticePairRecoveryReset.into_callerFrame refs store _ frames.factorSelected
  unfold QuadraticCandidateSelect.selectedOption FirstAccepted.selectedOption
  rw [accepted, selected]

/-- The original source pair updates the persistent factor and preserves outside caller reads. -/
structure Relation (generator : (ZMod N)ˣ) (refs : LatticePairFactorRecovery.Refs ctx N)
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

/-- Actual reset and complete pair recovery realize the original retained-factor update. -/
theorem into_correct (input : Input N) (generator : (ZMod N)ˣ)
    (refs : LatticePairFactorRecovery.Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input generator store refs) :
    Relation generator refs store (step input refs store).1 := by
  have recoveryInitial := factorInitial_afterReset input generator refs separation store initial
  have recovery := LatticePairFactorRecovery.into_correct input generator refs separation.recovery
    (LatticePairRecoveryReset.step refs store).1 recoveryInitial
  refine ⟨?_, into_callerFrame input refs store⟩
  rw [step_store]
  have result := recovery.selected
  rw [factorOption_afterReset refs separation.resetFrames store,
    sourceSamples_afterReset refs separation.resetFrames store] at result
  exact result

/-- Independent native allowance includes all thirteen resets and the complete next pair. -/
def eventEnvelope (N : Nat) : ResourcePool kind :=
  LatticePairRecoveryReset.resetEventEnvelope N + LatticePairFactorRecovery.eventEnvelope N

/-- Independent sequential depth includes the entire paid reset before every pair. -/
def depthBound (N : Nat) : Nat := 13 + LatticePairFactorRecovery.depthBound N

private theorem sequence_pool_le (first second : Circuit ctx ctx)
    (firstBound secondBound : ResourcePool kind) (path : (Circuit.seq first second).Path)
    (firstLe : first.resourcePool path.1 ≤ firstBound)
    (secondLe : second.resourcePool path.2 ≤ secondBound) :
    (Circuit.seq first second).resourcePool path ≤ firstBound + secondBound := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add firstLe secondLe

/-- The actual reset and complete pair execution contribute to the same native resource ledger. -/
theorem into_pool_le (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (path : (into input refs).Path) : (into input refs).resourcePool path ≤ eventEnvelope N :=
  sequence_pool_le _ _ _ _ path (LatticePairRecoveryReset.into_pool_le refs path.1)
    (LatticePairFactorRecovery.into_pool_le input refs path.2)

/-- Every actual pair still incurs its reset and full sequential recovery depth. -/
theorem into_depth_le (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (path : (into input refs).Path) : (into input refs).depth (fun _ => 1) path ≤ depthBound N := by
  change (LatticePairRecoveryReset.into refs).depth (fun _ => 1) path.1 +
    (LatticePairFactorRecovery.into input refs).depth (fun _ => 1) path.2 ≤ _
  rw [LatticePairRecoveryReset.into_depth]
  exact Nat.add_le_add_left (LatticePairFactorRecovery.into_depth_le input refs path.2) 13

/-- Resident accounting includes the existing context and the real reusable native-power scope. -/
theorem into_resident_le (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (path : (into input refs).Path) : (into input refs).peakResidentSpace path ≤
      ctx.residentSpace + Modular.NativePower.powerSpace kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq (LatticePairRecoveryReset.into refs)
    (LatticePairFactorRecovery.into input refs) path).le.trans ?_
  exact SpacePool.max_le ((LatticePairRecoveryReset.into_resident_le refs path.1).trans
    (le_add_of_nonneg_right zero_le)) (LatticePairFactorRecovery.into_resident_le input refs path.2)

/-- Auxiliary accounting includes the same actual native-power allocation and existing roles. -/
theorem into_auxiliary_le (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (path : (into input refs).Path) : (into input refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + Modular.NativePower.powerSpace kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq (LatticePairRecoveryReset.into refs)
    (LatticePairFactorRecovery.into input refs) path).le.trans ?_
  exact SpacePool.max_le ((LatticePairRecoveryReset.into_auxiliary_le refs path.1).trans
    (le_add_of_nonneg_right zero_le))
    (LatticePairFactorRecovery.into_auxiliary_le input refs path.2)

/-- Reset and full pair recovery restore borrowed systems jointly with arbitrary references. -/
theorem into_borrowedRestored (input : Input N) (refs : LatticePairFactorRecovery.Refs ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into input refs).BorrowedRestored Reference state
      ((into input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (LatticePairRecoveryReset.into_borrowedRestored refs
    Reference state) (LatticePairFactorRecovery.into_borrowedRestored input refs Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairReusableRecovery
