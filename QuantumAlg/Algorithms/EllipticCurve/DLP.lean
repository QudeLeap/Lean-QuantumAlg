/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.SevenCoordinates
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.SevenCoordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Calibrated

/-!
# Original-input declared ECDLP with complete physical cycles and scalar resources

The one named algorithm allocates its own bank, executes every original native
sampling and checked-recovery round, and packs the retained optional result once.
Its ordinary public theorem includes calibrated success, complete final state,
borrowed restoration, actual physical cycles and all seven scalar resources.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP

noncomputable section

open Canonical.QueryModel Canonical.QueryModel.Recovery

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Original affine public ECDLP inputs with the actual complete declared execution.

**Input.** A prime-field curve with the original $p > 3$ assumptions, affine
points $P,Q$, prime subgroup order $r$, and $Q$ in the subgroup of $P$. The
certified increasing order expansion has at least one term, including powers
of two. Ordinary opaque access acts on the full identity-inclusive point bank.
The well-formed rational failure target satisfies $0 < eta <= 1$. Every
reference extension of the original classical point inputs is admitted; the
caller supplies no candidate, secret scalar or prepared quantum bank.
**Output.** An optional canonical scalar below $r$ multiplying $P$ to $Q$.
All original points, measured cells and recovery destinations survive. Every
result fiber has the fixed zero owned bank and restored borrowed correlations.
**Resource budget.** Put $f = ceil(log_2 p)$, $t = ceil(log_2(12r))$,
$W = 2t+1+2f$, and $C = 42t+t(248f+644)+119$. The original logarithmic failure
calibration chooses $k$ actual rounds. Put
$S = 2W+1+22t+2(t+3 choose(t,2))$,
$D = 6t+2(2 choose(t,2)+3 floor(t/2))$, and $M = 2W+2t$.
The same full run has at most $kS$ single-qubit events, $kD$ CNOTs, zero
Toffolis, $k$ ordinary opaque queries, $kM$ two-dimensional measurements,
$W$ initial preparation events and $kC+1$ classical instructions. Both complete
physical resets are charged in every round. For $c(u)=(u+1)(2(u+1)+1)+3$,
put $B=max(25t+9c(t)+16,27f+9c(f)+15)$. Resident storage is bounded by $W$
qubits and $B+6f+4t+8$ classical bits; auxiliary storage by $W$ qubits and
$B+2f+4t+6$ classical bits. Other quantum dimensions have zero allowance.
Assign every native event unit duration. Maximum complete-cycle depth is at
most $W+S+D+1+M+C+1$, independently of $k$. Separate chronological full-run
depth is at most $W+k(S+D+1+M+C)+1$.
**Success.** The accepted event has probability at least $1-eta$ for every
admitted normalized input and arbitrary reference extension. Success, full
state, restoration and every resource observation belong to the same run.
**Source.** [PZ03, ecc.tex:448-462,525-640]; [Sho95, source.tex:1704-1740];
[SV24, Uniform.tex:622-664,775-805,996-1024]; [RNSL17, ECDLP.tex:483-510,649-709].
Native event allowances are proved from the actual implementation, not asserted
as constants supplied by these papers.
-/
public abbrev problem (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) (A : Canonical.Access I)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    Problem (Sampling.executionModel I A) (Sampling.pre I) (Recovery.post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  calibratedWholeProblem I A expansion I.subgroupOrder_prime.two_le budget wellFormed

/-- The original public budget selects the complete actual run; no execution witness is supplied. -/
public abbrev algorithm (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) (A : Canonical.Access I)
    (budget : Factoring.FailureBudget) :
    Algorithm (Sampling.executionModel I A) (Sampling.pre I) (Recovery.post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  calibratedWholeAlgorithm I A expansion I.subgroupOrder_prime.two_le budget

/-- The same independent original-input outcome carries its actual complete finite cycle plan. -/
public abbrev completeCycleProblem (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) (A : Canonical.Access I)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :=
  calibratedCycleProblem I A expansion I.subgroupOrder_prime.two_le budget wellFormed

/-- One complete original ECDLP theorem includes success, state, cycles and all scalar resources. -/
public theorem main (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) (A : Canonical.Access I)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    ∃ cycles : Algorithm.CycleSolves (algorithm I expansion A budget)
        (completeCycleProblem I expansion A budget wellFormed),
      (algorithm I expansion A budget).Solves (problem I expansion A budget wellFormed) ∧
        (∀ path : (algorithm I expansion A budget).run.code.Path,
          SevenCoordinateBounds I A expansion I.subgroupOrder_prime.two_le budget wellFormed
            cycles path) ∧
        (∀ path : (algorithm I expansion A budget).run.code.Path,
          PeripheralBounds I A expansion I.subgroupOrder_prime.two_le budget path) ∧
        (∀ path : (algorithm I expansion A budget).run.code.Path,
          (algorithm I expansion A budget).run.code.depth (fun _ => 1) path ≤
            Scalar.wholeRunEvents (fieldWidth E) (scalarWidth I)
              (Canonical.retryCountForBudget I budget)) :=
  ⟨calibratedCycleCertificate I A expansion I.subgroupOrder_prime.two_le budget wellFormed,
    calibratedWholeAlgorithm_solves I A expansion I.subgroupOrder_prime.two_le budget wellFormed,
    calibrated_sevenCoordinates I A expansion I.subgroupOrder_prime.two_le budget wellFormed,
    calibrated_peripheralBounds I A expansion I.subgroupOrder_prime.two_le budget,
    calibrated_wholeRunDepth_scalar I A expansion I.subgroupOrder_prime.two_le budget⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP
