/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Pool
public import QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Space
public import QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cardinality
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Pool
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Space

/-!
# Complete selected-model resources of actual repeated ECDLP

The budget counts the exact original initialization, all selected sampling
and checked-recovery rounds, and one final option pack. Resident and auxiliary
space use one reused workspace. The same complete event allowance also bounds
critical-path depth at any assigned native event durations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- The run exposes the event pool of its one actual circuit. -/
theorem exponentRepeatedRun_pool_le
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.resourcePool path ≤
        repeatedRunBudget E problem nontrivial count :=
  exponentRepeatedCode_pool_le E fieldTail sameWidth fits odd problem points seed
    nontrivial count path

/-- Its actual critical path is bounded at any native event durations. -/
theorem exponentRepeatedRun_depth_le
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model) → Nat)
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.depth duration path ≤
        ResourcePool.weightedCount duration (repeatedRunBudget E problem nontrivial count) :=
  exponentRepeatedCode_depth_le E fieldTail sameWidth fits odd problem points seed
    nontrivial count duration path

/-- The same run keeps every classical and quantum resident within one reused bank. -/
theorem exponentRepeatedRun_resident_le
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.peakResidentSpace path ≤
        recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
          persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
            (PublicInput.terminal E (orderWidth problem)).residentSpace :=
  exponentRepeatedCode_resident_le E fieldTail sameWidth fits odd problem points seed
    nontrivial count path

/-- The auxiliary roles are counted once independently of the repetition count. -/
theorem exponentRepeatedRun_auxiliary_le
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.peakAuxiliarySpace path ≤
        recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
          persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
            (PublicInput.terminal E (orderWidth problem)).auxiliarySpace :=
  exponentRepeatedCode_auxiliary_le E fieldTail sameWidth fits odd problem points seed
    nontrivial count path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
