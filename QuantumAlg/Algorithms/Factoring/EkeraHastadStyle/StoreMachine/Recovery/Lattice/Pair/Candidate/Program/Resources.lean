/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Constants.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Scan.Initialized.Resources

/-!
# Native cost and dependency depth of actual pair-candidate recovery

The complete pool decomposition counts each actually executed component.
Independent depth formulas charge all sequential initialization dependencies.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Independent duration of zero/upper-bound loading and original modular setup. -/
def sharedDepthBound (N : Nat) : Nat := shortLogBits N + 3 + (12 * modulusBits N + 8)

/-- Independent duration of original pair reduction and both shared initializers. -/
def prefixDepthBound (N : Nat) : Nat :=
  LatticePairNearestPlaneSavedTarget.operationBound N + sharedDepthBound N

/-- Independent full duration includes the original sequential candidate scan. -/
def recoveryDepthBound (N : Nat) : Nat := prefixDepthBound N +
  LatticeCandidateScanInitialized.initializedScanDepthBound N (shortLogBits N) (tradeoffBits N)

/-- Actual native accounting adds the two chronological component ledgers. -/
theorem sharedInto_resourcePool (input : Input N) (refs : Refs ctx N)
    (path : (sharedInto input refs).Path) :
    (sharedInto input refs).resourcePool path =
      (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants).resourcePool path.1 +
        (LatticeCandidateModularSetup.setupInto input refs.setup).resourcePool path.2 := by
  change ResourcePool.ofList (_ ++ _) = _
  exact ResourcePool.ofList_append _ _

/-- Every actual path satisfies the independent complete sequential duration. -/
theorem sharedInto_depth_le (input : Input N) (refs : Refs ctx N)
    (path : (sharedInto input refs).Path) :
    (sharedInto input refs).depth (fun _ => 1) path ≤ sharedDepthBound N :=
  Nat.add_le_add
    ((LatticeCandidateConstants.loadInto_depth (shortLogBits N) refs.constants path.1).le)
    (LatticeCandidateModularSetup.setupInto_depth_le input refs.setup path.2)

/-- Actual native accounting adds the two chronological component ledgers. -/
theorem pairCandidatePrefix_resourcePool (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidatePrefix input refs).Path) :
    (pairCandidatePrefix input refs).resourcePool path =
      (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair).resourcePool
          path.1 +
        (sharedInto input refs).resourcePool path.2 := by
  change ResourcePool.ofList (_ ++ _) = _
  exact ResourcePool.ofList_append _ _

/-- Every actual path satisfies the independent complete sequential duration. -/
theorem pairCandidatePrefix_depth_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidatePrefix input refs).Path) :
    (pairCandidatePrefix input refs).depth (fun _ => 1) path ≤ prefixDepthBound N :=
  Nat.add_le_add
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_depth_le
      refs.pair path.1)
    (sharedInto_depth_le input refs path.2)

/-- Actual native accounting adds the two chronological component ledgers. -/
theorem pairCandidateRecoveryInto_resourcePool (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidateRecoveryInto input refs).Path) :
    (pairCandidateRecoveryInto input refs).resourcePool path =
      (pairCandidatePrefix input refs).resourcePool path.1 +
        (LatticeCandidateScanInitialized.initializedScanInto input refs.scan).resourcePool
          path.2 := by
  change ResourcePool.ofList (_ ++ _) = _
  exact ResourcePool.ofList_append _ _

/-- Every actual path satisfies the independent complete sequential duration. -/
theorem pairCandidateRecoveryInto_depth_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidateRecoveryInto input refs).Path) :
    (pairCandidateRecoveryInto input refs).depth (fun _ => 1) path ≤ recoveryDepthBound N :=
  Nat.add_le_add
    (pairCandidatePrefix_depth_le input refs path.1)
    (LatticeCandidateScanInitialized.initializedScanInto_depth_le input refs.scan path.2)

/-- Every actual stage restores the full borrowed-reference joint state. -/
theorem sharedInto_borrowedRestored (input : Input N) (refs : Refs ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (sharedInto input refs).BorrowedRestored Reference state
      ((sharedInto input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeCandidateConstants.loadInto_borrowedRestored (shortLogBits N)
      refs.constants Reference state)
    (LatticeCandidateModularSetup.setupInto_borrowedRestored input refs.setup Reference _)

/-- Sequential scopes reuse one native-power allocation while retaining all caller storage. -/
theorem sharedInto_resident_le (input : Input N) (refs : Refs ctx N)
    (path : (sharedInto input refs).Path) :
    (sharedInto input refs).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq
    (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup) path).le.trans ?_
  exact SpacePool.max_le
    ((LatticeCandidateConstants.loadInto_resident_le (shortLogBits N)
      refs.constants path.1).trans (le_add_of_nonneg_right zero_le))
    (LatticeCandidateModularSetup.setupInto_resident_le input refs.setup path.2)

/-- Sequential scopes reuse one native-power allocation while retaining all caller storage. -/
theorem sharedInto_auxiliary_le (input : Input N) (refs : Refs ctx N)
    (path : (sharedInto input refs).Path) :
    (sharedInto input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup) path).le.trans ?_
  exact SpacePool.max_le
    ((LatticeCandidateConstants.loadInto_auxiliary_le (shortLogBits N)
      refs.constants path.1).trans (le_add_of_nonneg_right zero_le))
    (LatticeCandidateModularSetup.setupInto_auxiliary_le input refs.setup path.2)

/-- Every actual stage restores the full borrowed-reference joint state. -/
theorem pairCandidatePrefix_borrowedRestored (input : Input N) (refs : Refs ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pairCandidatePrefix input refs).BorrowedRestored Reference state
      ((pairCandidatePrefix input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_borrowedRestored
      refs.pair Reference state)
    (sharedInto_borrowedRestored input refs Reference _)

/-- Sequential scopes reuse one native-power allocation while retaining all caller storage. -/
theorem pairCandidatePrefix_resident_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidatePrefix input refs).Path) :
    (pairCandidatePrefix input refs).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs) path).le.trans ?_
  exact SpacePool.max_le
    ((LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_resident_le
      refs.pair path.1).trans (le_add_of_nonneg_right zero_le))
    (sharedInto_resident_le input refs path.2)

/-- Sequential scopes reuse one native-power allocation while retaining all caller storage. -/
theorem pairCandidatePrefix_auxiliary_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidatePrefix input refs).Path) :
    (pairCandidatePrefix input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs) path).le.trans ?_
  exact SpacePool.max_le
    ((LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_auxiliary_le
      refs.pair path.1).trans (le_add_of_nonneg_right zero_le))
    (sharedInto_auxiliary_le input refs path.2)

/-- Every actual stage restores the full borrowed-reference joint state. -/
theorem pairCandidateRecoveryInto_borrowedRestored (input : Input N) (refs : Refs ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pairCandidateRecoveryInto input refs).BorrowedRestored Reference state
      ((pairCandidateRecoveryInto input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (pairCandidatePrefix_borrowedRestored input refs Reference state)
    (LatticeCandidateScanInitialized.initializedScanInto_borrowedRestored input
      refs.scan Reference _)

/-- Sequential scopes reuse one native-power allocation while retaining all caller storage. -/
theorem pairCandidateRecoveryInto_resident_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidateRecoveryInto input refs).Path) :
    (pairCandidateRecoveryInto input refs).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq
    (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan) path).le.trans ?_
  exact SpacePool.max_le
    (pairCandidatePrefix_resident_le input refs path.1)
    (LatticeCandidateScanInitialized.initializedScanInto_resident_le input refs.scan path.2)

/-- Sequential scopes reuse one native-power allocation while retaining all caller storage. -/
theorem pairCandidateRecoveryInto_auxiliary_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidateRecoveryInto input refs).Path) :
    (pairCandidateRecoveryInto input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan) path).le.trans ?_
  exact SpacePool.max_le
    (pairCandidatePrefix_auxiliary_le input refs path.1)
    (LatticeCandidateScanInitialized.initializedScanInto_auxiliary_le input refs.scan path.2)


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
