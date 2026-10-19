/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Data
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Parameter
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Frames

/-!
# Original scan entry facts established by the actual complete pair prefix
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Actual pair reduction and shared initialization establish the original scan invariant. -/
lemma pairCandidatePrefix_correct (input : Input N) (generator : (ZMod N)ˣ)
    (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input generator store refs) :
    LatticeCandidateSlotOutcome.InitialConditions input generator
      (LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair store) refs.scan
      (prefixStep input refs store).1 := by
  rw [prefixStep_store, sharedStep_store]
  let afterPair := (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair store).1
  let afterConstants :=
    (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants afterPair).1
  let afterSetup := (LatticeCandidateModularSetup.setupStep input refs.setup afterConstants).1
  let samples := LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair store
  have pairData : PairScanData samples refs afterPair :=
    pairScanData_of_outcome refs store afterPair
      (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_correct
        refs.pair separation.pair store initial.pair)
  have parameterFrame : afterConstants.read refs.setup.parameter =
      store.read refs.setup.parameter :=
    (LatticeCandidateConstants.loadInto_callerFrame (shortLogBits N) refs.constants afterPair
      refs.setup.parameter separation.constantsPreservesSetupParameter.1
      separation.constantsPreservesSetupParameter.2).trans
      (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_callerFrame
        refs.pair store refs.setup.parameter separation.pairPreservesSetupParameter)
  have setupInitial := setupInitial_transport input refs.setup store afterConstants
    initial.setup parameterFrame
  have constants := LatticeCandidateConstants.loadInto_correct (shortLogBits N)
    refs.constants separation.constants afterPair
  have setup := LatticeCandidateModularSetup.setupInto_correct input refs.setup
    separation.setup afterConstants setupInitial
  have dataAtConstants : PairScanData samples refs afterConstants :=
    pairScanData_transport samples refs afterPair afterConstants pairData fun source isPair =>
      LatticeCandidateConstants.loadInto_callerFrame (shortLogBits N) refs.constants afterPair
        (LatticeCandidateSlotFrames.externalSourceInput refs.scan source)
        (separation.constantsPreservesPairSources source isPair).1
        (separation.constantsPreservesPairSources source isPair).2
  have dataAtSetup : PairScanData samples refs afterSetup :=
    pairScanData_transport samples refs afterConstants afterSetup dataAtConstants
      fun source isPair =>
        LatticeCandidateModularSetup.setupInto_callerFrame input refs.setup afterConstants
          (LatticeCandidateSlotFrames.externalSourceInput refs.scan source)
          (separation.setupPreservesPairSources source isPair)
  have generatorBase := parameterBase_eq_generatorValue input generator refs store
    afterConstants initial parameterFrame
  have zeroFrame := LatticeCandidateModularSetup.setupInto_callerFrame input refs.setup
    afterConstants (LatticeCandidateSlotMachine.writeInput refs.constants.zero)
    separation.setupPreservesZero
  have upperFrame := LatticeCandidateModularSetup.setupInto_callerFrame input refs.setup
    afterConstants (LatticeCandidateSlotMachine.writeInput refs.constants.upperBound)
    separation.setupPreservesUpperBound
  refine ⟨dataAtSetup.basis, dataAtSetup.center, dataAtSetup.originalTarget, ?_, ?_, ?_, ?_, ?_⟩
  · change RawSignedRepresents (afterSetup.read refs.scan.zero) 0
    rw [refs.scanZero, zeroFrame]
    exact constants.zero
  · change RawSignedRepresents (afterSetup.read refs.scan.upperBound) _
    rw [refs.scanUpperBound, upperFrame]
    exact constants.upperBound
  · change (afterSetup.read refs.scan.power.modulus).toNat = N
    rw [refs.scanModulus]
    exact setup.modulus
  · change (afterSetup.read refs.scan.power.generator).residueEncoding.val = _
    rw [refs.scanGenerator]
    exact setup.generatorValue.trans generatorBase
  · change (afterSetup.read refs.scan.power.targetPower).toNat = _
    rw [refs.scanTargetPower, setup.targetPower, generatorBase]
    exact LatticeCandidatePowerBridge.targetUnit_val_eq_modularPower input generator

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
