/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Solves
public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.Initialized.Depth

/-!
# Original generic ECC cycle certificates for every finite attempt count

Zero attempts still execute the original initialization and packing. One
attempt has one actual completed computation, with no fictitious terminal
reset. Their fixed plans retain the complete single computation. At least
two attempts use the physically certified first/reused/terminal plan instead
of treating the whole retry loop as one cycle. Each case retains the same
original outcome, success calibration and complete run.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
  (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
  (seed : AffinePoint E) (addends : AddendEncoding E I points)

/-- Fixed original-caller protocols for zero, one and multiple actual attempts. -/
public def completeCycleProblem (count : Nat) (failure : ℝ) : CycleProblem
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (inputContext E I) (outputContext E I)
    (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))) where
  outcome := problem E I count failure
  plan := match count with
    | 0 => .cycle (problem E I 0 failure)
    | 1 => .cycle (problem E I 1 failure)
    | count + 2 => initializedRepeatedPlan E fieldTail sameWidth fits
        (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends count

/-- The same named original algorithm implements the fixed physically
admissible plan for every count, including the real zero/one executions. -/
public def completeCycleCertificate (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure) :
    Algorithm.CycleSolves (algorithm E fieldTail sameWidth fits odd I points seed count)
      (completeCycleProblem E fieldTail sameWidth fits I points seed addends count failure) := by
  cases count with
  | zero =>
      have correct := algorithm_solves E fieldTail sameWidth fits odd I points seed addends
        0 failure calibrated
      exact
        { correctness := correct
          schedule := .complete _
            { output := (algorithm E fieldTail sameWidth fits odd I points seed 0).run.output
              certified := correct }
          entry := fun _ _ admitted => admitted }
  | succ count =>
      cases count with
      | zero =>
          have correct := algorithm_solves E fieldTail sameWidth fits odd I points seed addends
            1 failure calibrated
          exact
            { correctness := correct
              schedule := .complete _
                { output := (algorithm E fieldTail sameWidth fits odd I points seed 1).run.output
                  certified := correct }
              entry := fun _ _ admitted => admitted }
      | succ count =>
          exact initializedCycleCertificate E fieldTail sameWidth fits odd I points seed
            addends count failure calibrated

/-- A uniform independent cycle allowance; only the two small symbolic cases
retain their whole computation, and later counts use the certified maximum. -/
def completeCycleDepthBudget : Nat :=
  max (depthLimit E I 0)
    (max (depthLimit E I 1) (initializedRepeatedDepthBudget E (ECDLP.Canonical.problem I)
      I.subgroupOrder_prime.two_le))

/-- Every actual original algorithm path has the certified complete-cycle
maximum, independently of the finite count and without evaluating a fixed width. -/
theorem algorithm_completeMaximumCycleDepth_le (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure)
    (path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path) :
    (completeCycleCertificate E fieldTail sameWidth fits odd I points seed addends count
      failure calibrated).maximumCycleDepth (fun _ => 1) path ≤ completeCycleDepthBudget E I := by
  cases count with
  | zero =>
      change (algorithm E fieldTail sameWidth fits odd I points seed 0).run.code.depth
        (fun _ => 1) path ≤ _
      exact (exponentRepeatedRun_depth_le E fieldTail sameWidth fits odd
        (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le 0
        (fun _ => 1) path).trans (Nat.le_max_left _ _)
  | succ count =>
      cases count with
      | zero =>
          change (algorithm E fieldTail sameWidth fits odd I points seed 1).run.code.depth
            (fun _ => 1) path ≤ _
          exact (exponentRepeatedRun_depth_le E fieldTail sameWidth fits odd
            (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le 1
            (fun _ => 1) path).trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
      | succ count =>
          exact (algorithm_initializedMaximumCycleDepth_le E fieldTail sameWidth fits odd
            I points seed addends count failure calibrated path).trans
              ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

end

end QuantumAlg.EllipticCurve.LogicalResources
