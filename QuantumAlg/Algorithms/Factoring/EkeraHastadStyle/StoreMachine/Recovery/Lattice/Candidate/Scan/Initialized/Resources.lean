/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Scan.Initialized

/-!
# Actual initialized candidate scan resources with one reusable native-power scope
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScanInitialized

open Execution

noncomputable section

variable {N m ell : Nat} {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent original initialization instruction plus the complete canonical slot allowance. -/
def initializedScanEventEnvelope (execution : ExecutionModel)
    [BitWord.Selected execution] (N m ell : Nat) : ResourcePool execution :=
  LatticeCandidateSelectorInit.clearAcceptedEventEnvelope execution +
    LatticeCandidateScan.scanEventEnvelope execution
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N)

/-- Independent one-instruction initialization and complete sequential scan duration. -/
def initializedScanDepthBound (N m ell : Nat) : Nat :=
  1 + LatticeCandidateScan.scanDepthBound
    (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N)

/-- Actual latch initialization and selected candidate paths satisfy the full native allowance. -/
lemma initializedScanInto_pool_le (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (path : (initializedScanInto input refs).Path) :
    (initializedScanInto input refs).resourcePool path ≤
      initializedScanEventEnvelope model N m ell := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (LatticeCandidateSelectorInit.clearAcceptedInto_resourcePool
    refs.selector.selection path.1).le
    (LatticeCandidateScan.scanInto_pool_le
      (LatticeCandidateModularSetup.modulusSpec input) refs path.2)

/-- The actual initialized scan includes the latch-clear dependency in its original depth bound. -/
lemma initializedScanInto_depth_le (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (path : (initializedScanInto input refs).Path) :
    (initializedScanInto input refs).depth (fun _ => 1) path ≤ initializedScanDepthBound N m ell :=
  Nat.add_le_add (LatticeCandidateSelectorInit.clearAcceptedInto_depth
    refs.selector.selection path.1).le
    (LatticeCandidateScan.scanInto_depth_le
      (LatticeCandidateModularSetup.modulusSpec input) refs path.2)

/-- Actual initialization and every subsequent scan slot restore arbitrary borrowed correlations. -/
lemma initializedScanInto_borrowedRestored (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (initializedScanInto input refs).BorrowedRestored Reference state
      ((initializedScanInto input refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (LatticeCandidateSelectorInit.clearAcceptedInto_borrowedRestored
      refs.selector.selection Reference state)
    (LatticeCandidateScan.scanOffsetsInto_borrowedRestored
      (LatticeCandidateModularSetup.modulusSpec input) refs LatticeCandidateScan.offsets.toList
        Reference _)

/-- Actual initialized scans count all original resident cells and reused power scratch. -/
lemma initializedScanInto_resident_le (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (path : (initializedScanInto input refs).Path) :
    (initializedScanInto input refs).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq
    (LatticeCandidateSelectorInit.clearAcceptedInto refs.selector.selection)
    (LatticeCandidateScan.scanInto (LatticeCandidateModularSetup.modulusSpec input) refs)
    path).le.trans ?_
  exact SpacePool.max_le
    ((LatticeCandidateSelectorInit.clearAcceptedInto_resident_le
      refs.selector.selection path.1).trans
      (le_add_of_nonneg_right zero_le))
    (LatticeCandidateScan.scanOffsetsInto_resident_le
      (LatticeCandidateModularSetup.modulusSpec input) refs LatticeCandidateScan.offsets.toList
        path.2)

/-- Actual initialized scans count all original auxiliary cells and reused power scratch. -/
lemma initializedScanInto_auxiliary_le (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (path : (initializedScanInto input refs).Path) :
    (initializedScanInto input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (LatticeCandidateSelectorInit.clearAcceptedInto refs.selector.selection)
    (LatticeCandidateScan.scanInto (LatticeCandidateModularSetup.modulusSpec input) refs)
    path).le.trans ?_
  exact SpacePool.max_le
    ((LatticeCandidateSelectorInit.clearAcceptedInto_auxiliary_le
      refs.selector.selection path.1).trans
      (le_add_of_nonneg_right zero_le))
    (LatticeCandidateScan.scanOffsetsInto_auxiliary_le
      (LatticeCandidateModularSetup.modulusSpec input) refs LatticeCandidateScan.offsets.toList
        path.2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScanInitialized
