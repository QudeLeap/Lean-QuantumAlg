/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.InitialSpace
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources

/-!
# Complete live space of the actual repeated ECDLP code

The one-time selected initialization reaches the original terminal context.
Every checked round reuses that context and the same seven persistent cells.
The peak space is therefore independent of the number of rounds.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- Every actual repeated path keeps one resident bank and reuses recovery scratch. -/
theorem exponentRepeatedCode_resident_le
    (path : (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).Path) :
    (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).peakResidentSpace path ≤
        recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
          persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
            (PublicInput.terminal E (orderWidth problem)).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [selectedInitial_resident E problem path.1]
    exact fun _ => Nat.le_add_left _ _
  · exact sampledRecoveryTail_resident_le
      (BitWord.selectForCircuit (samplingRound E fieldTail sameWidth fits odd problem points seed))
      (BitWord.selectForCircuit_isLocal _
        (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)) count
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _ path.2

/-- Every actual repeated path reuses the same auxiliary roles. -/
theorem exponentRepeatedCode_auxiliary_le
    (path : (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).Path) :
    (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).peakAuxiliarySpace path ≤
        recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
          persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
            (PublicInput.terminal E (orderWidth problem)).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [selectedInitial_auxiliary E problem path.1]
    exact fun _ => Nat.le_add_left _ _
  · exact sampledRecoveryTail_auxiliary_le
      (BitWord.selectForCircuit (samplingRound E fieldTail sameWidth fits odd problem points seed))
      (BitWord.selectForCircuit_isLocal _
        (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)) count
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _ path.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
