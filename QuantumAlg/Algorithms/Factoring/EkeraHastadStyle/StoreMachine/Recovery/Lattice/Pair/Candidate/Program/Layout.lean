/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Constants
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Scan.Initialized

/-!
# Actual pair-candidate references and original caller contracts
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution

noncomputable section

/-- The common raw-word width of the pair reduction and candidate scan. -/
abbrev Width (N : Nat) : Nat := LatticeWideLllMachine.Width N

/-- Caller-owned references and all real data-flow equalities of pair recovery. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the pair stage. -/
  pair : LatticePairNearestPlaneSavedTarget.Refs ctx N
  /-- Nested references for the constants stage. -/
  constants : LatticeCandidateConstants.Refs ctx (Width N)
  /-- Nested references for the setup stage. -/
  setup : LatticeCandidateModularSetup.Refs ctx N
  /-- Nested references for the scan stage. -/
  scan : LatticeCandidateSlotMachine.Refs ctx (Width N) (modulusBits N)
  scanNearest :
    scan.distance.candidate.nearest = LatticePairNearestPlaneSavedTarget.nearestRefs pair
  scanOriginalTarget : scan.distance.originalTarget = pair.savedTarget
  scanZero : scan.zero = LatticeCandidateSlotMachine.writeInput constants.zero
  scanUpperBound : scan.upperBound = LatticeCandidateSlotMachine.writeInput constants.upperBound
  scanModulus : scan.power.modulus = LatticeCandidateModularSetup.writeInput setup.modulus
  scanGenerator : scan.power.generator = LatticeCandidateModularSetup.writeInput setup.generator
  scanTargetPower :
    scan.power.targetPower = LatticeCandidateModularSetup.writeInput setup.targetPower

/-- A scan source supplied by the completed pair reduction. -/
def IsPairSource : LatticeCandidateSlotFrames.ExternalSourceCell → Prop
  | .candidateEntry _ => True
  | .originalTarget _ => True
  | _ => False

/-- A structural read avoids both writes of the shared-constant initializer. -/
def AvoidsConstantWrites {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  refs.constants.zero.key ∉ other.storageKeys ∧
    refs.constants.upperBound.key ∉ other.storageKeys

/-- A structural read avoids every visible write of the modular setup prefix. -/
def AvoidsSetupWrites {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  ∀ cell, LatticeCandidateModularSetup.mutableKey refs.setup cell ∉ other.storageKeys

/-- Local and cross-stage separation for the four literal component packages. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  pair : LatticePairNearestPlaneSavedTarget.Separation refs.pair
  constants : LatticeCandidateConstants.Separation refs.constants
  setup : LatticeCandidateModularSetup.Separation refs.setup
  scan : LatticeCandidateSlotMachine.Separation refs.scan
  scanFrames : LatticeCandidateSlotFrames.FrameSeparation refs.scan
  pairPreservesSetupParameter :
    LatticePairNearestPlaneSavedTarget.CallerFrameAvoids refs.pair refs.setup.parameter
  pairPreservesSetupBase :
    LatticePairNearestPlaneSavedTarget.CallerFrameAvoids refs.pair
      (LatticeCandidateModularSetup.parameterBaseInput refs.setup)
  constantsPreservesPairSources : ∀ source, IsPairSource source →
    AvoidsConstantWrites refs (LatticeCandidateSlotFrames.externalSourceInput refs.scan source)
  constantsPreservesSetupParameter : AvoidsConstantWrites refs refs.setup.parameter
  constantsPreservesSetupBase :
    AvoidsConstantWrites refs (LatticeCandidateModularSetup.parameterBaseInput refs.setup)
  setupPreservesPairSources : ∀ source, IsPairSource source →
    AvoidsSetupWrites refs (LatticeCandidateSlotFrames.externalSourceInput refs.scan source)
  setupPreservesZero :
    AvoidsSetupWrites refs (LatticeCandidateSlotMachine.writeInput refs.constants.zero)
  setupPreservesUpperBound :
    AvoidsSetupWrites refs (LatticeCandidateSlotMachine.writeInput refs.constants.upperBound)

/-- Entry facts for the pair prefix and retained canonical generator. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (input : Input N) (generator : (ZMod N)ˣ) (before : Store ctx)
    (refs : Refs ctx N) : Prop where
  pair : LatticePairNearestPlaneSavedTarget.InitialConditions before refs.pair
  setup : LatticeCandidateModularSetup.InitialConditions input before refs.setup
  generatorAtEntry : generator = parameterUnit (before.read refs.setup.parameter)

/-- A caller read avoids every write of the complete pair-recovery pipeline. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop where
  pair : LatticePairNearestPlaneSavedTarget.CallerFrameAvoids refs.pair other
  constants : AvoidsConstantWrites refs other
  setup : AvoidsSetupWrites refs other
  scan : LatticeCandidateSlotFrames.CallerFrameAvoids refs.scan other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
