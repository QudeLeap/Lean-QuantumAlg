/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Bounds
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec

/-!
# Independent resource contract for the same finite public recovery

The independent budget retains every native event, complete resident storage
and auxiliary role of the original allocated run. Its parameters are only the
curve, original ECDLP instance and retry count. The separate time formula
counts every reset and converted sampler in the same actual Run3.

The four resource obligations hold on every complete Path, so they also hold
on supported paths of any admitted input and external reference extension.
Success, final state promises and mandatory borrowed restoration remain the
separate original problem obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.ResourceContract

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Independent events and reused live storage for the original public ECDLP instance. -/
def resourceBudget (I : ECDLPInstance E) (count : Nat) : ResourceBudget Model where
  events := Events.fullBudget E (ECDLP.Canonical.problem I) I.subgroupOrder_prime.two_le count
  resident := recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
      (orderWidth (ECDLP.Canonical.problem I)) +
    persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
      (orderWidth (ECDLP.Canonical.problem I)) +
    (Recovery.PublicInput.context E (orderWidth (ECDLP.Canonical.problem I))).residentSpace
  auxiliary := recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
      (orderWidth (ECDLP.Canonical.problem I)) +
    persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
      (orderWidth (ECDLP.Canonical.problem I)) +
    (Recovery.PublicInput.context E (orderWidth (ECDLP.Canonical.problem I))).auxiliarySpace

/-- The complete independent reset and converted-sampler quantum-time allowance. -/
def quantumTimeLimit (I : ECDLPInstance E) (count : Nat) : Nat :=
  LogicalResources.Scalar.quantumTime p.size (orderWidth (ECDLP.Canonical.problem I)) count

/-- All four resource fields use the same actual allocation, finite loop and final pack Path. -/
lemma resourceObligations (fieldTail : Nat) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (r : Nat) (coefficient : (ZMod p)ˣ) (count : Nat)
    (path : (run E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
      I.subgroupOrder_prime.two_le count).code.Path) :
    (run E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
        I.subgroupOrder_prime.two_le count).code.resourcePool path ≤
        (resourceBudget E I count).events ∧
      (run E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
        I.subgroupOrder_prime.two_le count).code.peakResidentSpace path ≤
        (resourceBudget E I count).resident ∧
      (run E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
        I.subgroupOrder_prime.two_le count).code.peakAuxiliarySpace path ≤
        (resourceBudget E I count).auxiliary ∧
      (run E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
        I.subgroupOrder_prime.two_le count).code.quantumTime path ≤
        quantumTimeLimit E I count := by
  refine ⟨Events.run_budget E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
    I.subgroupOrder_prime.two_le count path, ?_, ?_, ?_⟩
  · exact run_resident_le E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
      I.subgroupOrder_prime.two_le count path
  · exact run_auxiliary_le E fieldTail (ECDLP.Canonical.problem I) points seed r coefficient
      I.subgroupOrder_prime.two_le count path
  · have bounded := Bounds.run_quantumTime_le E fieldTail (ECDLP.Canonical.problem I)
      points seed r coefficient I.subgroupOrder_prime.two_le count path
    simpa only [Events.terminal_systemCount, quantumTimeLimit,
      LogicalResources.Scalar.quantumTime, LogicalResources.Scalar.streamingQubits,
      LogicalResources.Scalar.multiplierTime_eq, LogicalResources.Scalar.pointDepth_eq,
      Recovery.PublicInput.Allocation.Events.bankWidth] using bounded

end

end ExecutionContract.ResourceContract
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
