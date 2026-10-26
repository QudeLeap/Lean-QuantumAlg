/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Probability.FixedOffset
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Borrowed.NoQuantum
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec

/-!
# The original measured ECDLP problem and one complete streaming solver

The independent problem retains the original accepted equation, calibrated
finite-retry success target and all native resource limits. The algorithm
construction and mathematical field proofs are in implementation modules.
The entry assembles their complete Solves record for the same actual run.
Both resource storage roles and the full borrowed/reference state are retained.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Measured ECDLP with finite repetition and independent streaming resource budgets.

**Input.**
- A prime-field curve, an affine generator of known prime subgroup order and
  an affine public target in that subgroup. The two borrowed classical point
  encodings are fixed. The quantum bank is allocated internally; every external
  reference extension of the public input is admitted.
**Output.**
- An optional bounded scalar satisfying the original public group equation.
**Resource budget.**
- Native events: the complete initial quantum-bank preparation, then `count`
  measured resets, converted Fourier samplers and checked native recovery
  attempts, followed by one paid optional-result pack.
- Resident and auxiliary space: the borrowed public points, the owned quantum
  bank, seven persistent destinations and the maximum successive recovery
  scratch scope. Repetition reuses this space without multiplying it by `count`.
- Quantum time: the independent per-attempt reset and sampling gate/query
  allowance multiplied by `count`. Preparation, measurement and classical work
  remain in the native-event budget and carry zero quantum duration. Complete
  unit-duration event depth is a separate resource theorem.
**Success.**
- At least `1 - failure`, under the original affine-addend and fixed-offset
  exceptional-error finite-repetition conditions.
- No final purity or zero-state promise is imposed on the owned bank. All
  borrowed data and their external-reference correlations are restored jointly.
**Source.**
- [PZ03, ecc.tex:448-556] for group shifts, measured Fourier readout and the
  exceptional addition cases; finite Fourier and classical recovery use the
  original registered finite-cyclic DLP analysis.
-/
public def problem (I : ECDLPInstance E) (count : Nat) (failure : ℝ) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) (Execution.inputContext E I)
      (Execution.outputContext E I)
      (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))) where
  Witness := Unit
  valid := fun _ _ => ECDLP.Measured.Recovery.PublicInput.Support.inputDomain E
    (orderWidth (ECDLP.Canonical.problem I))
    (ECDLP.Canonical.problem I)
  initialization := fun _ _ _ => True
  accepts := fun _ _ _stored output => LogicalResources.AcceptedOutput E I output
  successLB := fun _ _ => LogicalResources.successLowerBound failure
  states := fun _ _ => []
  resources := ECDLP.Measured.Recovery.ExecutionContract.ResourceContract.resourceBudget E I count
  quantumTimeLimit :=
    ECDLP.Measured.Recovery.ExecutionContract.ResourceContract.quantumTimeLimit E I count

private lemma complete_correct (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : LogicalResources.AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : LogicalResources.RepetitionCondition E I points seed count failure) :
    (algorithm E fieldTail sameWidth fits odd I points seed count).Solves
      (problem E I count failure) where
  success := fun environment witness Reference supplied valid _initialized =>
    ECDLP.Measured.Recovery.ExecutionContract.FixedOffsetSuccess.actual_run_relational_success
      (environment := environment)
      E fieldTail sameWidth fits odd I points seed
      addends count failure calibrated supplied valid
  states := by
    intro environment witness Reference supplied valid initialized requirement member
    cases member
  borrowed := by
    intro environment witness Reference supplied valid initialized
    exact AlgorithmRun.restoresBorrowed_of_noBorrowedQuantum
      (environment := environment)
      (algorithm E fieldTail sameWidth fits odd I points seed count).run
      (show
        (Execution.inputContext E I).borrowedQuantumWires = []
        from rfl) supplied
  events := by
    intro environment witness Reference supplied valid initialized path supported
    exact (ECDLP.Measured.Recovery.ExecutionContract.ResourceContract.resourceObligations
      E fieldTail I points seed I.subgroupOrder
      (Semantics.radixUnit p fieldTail.succ odd) count path).1
  resident := by
    intro environment witness Reference supplied valid initialized path supported
    exact (ECDLP.Measured.Recovery.ExecutionContract.ResourceContract.resourceObligations
      E fieldTail I points seed I.subgroupOrder
      (Semantics.radixUnit p fieldTail.succ odd) count path).2.1
  auxiliary := by
    intro environment witness Reference supplied valid initialized path supported
    exact (ECDLP.Measured.Recovery.ExecutionContract.ResourceContract.resourceObligations
      E fieldTail I points seed I.subgroupOrder
      (Semantics.radixUnit p fieldTail.succ odd) count path).2.2.1
  time := by
    intro environment witness Reference supplied valid initialized path supported
    exact (ECDLP.Measured.Recovery.ExecutionContract.ResourceContract.resourceObligations
      E fieldTail I points seed I.subgroupOrder
      (Semantics.radixUnit p fieldTail.succ odd) count path).2.2.2

/-- The public conclusion is solely existence of an Algorithm solving the independent problem. -/
public theorem main (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : LogicalResources.AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : LogicalResources.RepetitionCondition E I points seed count failure) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
        (Execution.inputContext E I) (Execution.outputContext E I)
        (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))),
      candidate.Solves (problem E I count failure) :=
  ⟨algorithm E fieldTail sameWidth fits odd I points seed count,
    complete_correct E fieldTail sameWidth fits odd I points seed addends count failure calibrated⟩

end

end QuantumAlg.EllipticCurve.LogicalResources
