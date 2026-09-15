/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Unitary
public import QuantumAlg.Algorithms.EllipticCurve.DLP.OrderPreparation
public import QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.PublicInput
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.PrimeOrderTailBound
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent contract for actual opaque ECDLP recovery

The original public points, prime subgroup, literal order preparation and
rational failure parameter determine this specification. Budgets are the
independent native coordinate formulas, including actual reset and complete
checked recovery. They do not inspect a candidate run. The resource theorem
then bounds the same actual circuit for every path, without input assumptions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native.Specification

open Execution

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The two original borrowed classical points are present at the input boundary. -/
public def inputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  Runtime.Context.pre I

/-- Every original input, the one bank, all finite cells and the final result remain listed. -/
public def outputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  recoveryContext (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I

/-- Admissibility constrains the original local classical values, not an external reference. -/
public def inputDomain (I : ECDLPInstance E)
    (state : ExecutionState (Store (inputContext I)) (inputContext I).register) : Prop :=
  ∀ store, 0 < (state.block store).mass → store = Runtime.Context.inputStore I

/-- The original optional-word acceptance predicate uses the scalar residue modulo the order. -/
public def accepts (I : ECDLPInstance E)
    (output : CShape.Value (.option (.unsignedWord (FiniteCyclicDLP.orderWidth (problem I))))) :
    Prop :=
  ∃ word : CShape.Word (FiniteCyclicDLP.orderWidth (problem I)),
    output = .optionSome word ∧ I.CandidateScalar (word.toNat : ZMod I.subgroupOrder)

/-- The original encoded rational failure target requires success at least `1 - eta`. -/
public def successLowerBound (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    ProbabilityLowerBound where
  value := budget.successThreshold
  le_one := ENNReal.ofReal_le_one.mpr
    (sub_le_self 1 (Factoring.FailureBudget.value_nonneg budget wellFormed))

/-- Independent native pools include reset alternatives and every surviving storage role. -/
public def resourceBudget (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (budget : Factoring.FailureBudget) : ResourceBudget .quantum where
  events := recoveryEnvelope I B (retryCountForBudget I budget)
  resident := recoverySpace I + (Runtime.Context.pre I).residentSpace
  auxiliary := recoverySpace I + (Runtime.Context.pre I).auxiliarySpace

/-- The chosen path pays for only its actual correction, while the pool includes both choices. -/
public def eventCountLimit (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (budget : Factoring.FailureBudget) : Nat :=
  recoveryEventLimit I B (retryCountForBudget I budget)

/-- Unit depth includes real measurement dependencies and the full classical recovery. -/
public def depthLimit (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (budget : Factoring.FailureBudget) : Nat :=
  recoveryDepthLimit I B (retryCountForBudget I budget)

/-- Complete source-domain ECDLP with actual finite sampling and checked recovery.

**Input.**
- The original finite affine public points on a prime-field curve, a prime
  subgroup of order `r`, and the promise that the target lies in that subgroup.
  The original binary expansion `r = sum j, 2^(ell j)` permits `s = 0`.
- The original opaque group action on the entire identity-inclusive point
  encoding. A rational parameter `eta` satisfies `0 < eta <= 1`.
  Local positive classical blocks contain the prescribed two public points;
  every normalized input and every external reference extension are admitted.
**Output.**
- An optional `t`-bit word whose residue modulo `r` multiplies the base to the
  target. The complete output retains both public points, the quantum bank,
  every measurement and persistent cell, and the optional result.
**Resource budget.**
- Put $f = ceil(log_2 p)$, $t = ceil(log_2(12r))$, $q = 2^t$,
  $k = max(1,ceil(log(1/eta)/log(4q^2/(4q^2-r(r-1)))))$,
  $W = 2t+1+2f$, and $C = 42t+t(248f+644)+119$.
- The same complete run uses one computational-basis preparation, exactly
  $k$ opaque queries, at most $2kt+2k(5s+6ell_s-5ell_0)+2kW$ single-qubit
  gates, exactly $kt(t-1)$ controlled-phase gates, at most
  $2k(ell_s-ell_0+2s)$ CNOT gates, exactly $2k floor(t/2)$ SWAP gates,
  exactly $k(W+2t)$ computational-basis measurements, and at most $kC+1$
  width-tagged classical-operation events. Actual reset gates and
  measurements are included even in the first round.
- Assign every native event unit duration. Maximal event depth is at most
  $2+k(3W+5(ell_s-ell_0)+5s+2+t+t(t-1)/2+floor(t/2)+2t+C)$.
- For $u >= 0$, let $c(u)$ be two plus the larger binary length of the
  maximum absolute canonical final Bezout coefficient and the maximum
  absolute coefficient at any active or final extended-Euclidean state,
  over all pairs of $(u+1)$-bit unsigned operands. Include all four
  coefficients, start from coefficient pairs $(1,0),(0,1)$, and run until
  the first remainder is zero, within $2u+3$ steps.
  Put $B = max(25t+9c(t)+16,27f+9c(f)+15)$.
  Resident storage is bounded by $W$ logical qubits and $B+6f+4t+7$
  classical bits; auxiliary storage by the same $W$ qubits and
  $B+2f+4t+5$ classical bits, included in the resident count. No systems
  of other dimensions are required. These space bounds are independent
  of $k$ and include all surviving output cells.
**Success.**
- The original success threshold is at least `1 - eta`. No final zero-state
  promise is imposed; full borrowed restoration remains a separate obligation.
**Source.**
- [PZ03, ecc.tex:448-462] for the elliptic-curve group action.
- [SV24, Uniform.tex:640-663] for the literal multi-term preparation; the
  original one-term branch is its separately retained Hadamard preparation.
- The finite Fourier floor and retry count use the original prime-order analysis.
- Costs here describe the actual native program, including paid reuse and
  checked recovery, rather than an expanded implementation of the opaque query.
-/
def specification (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    Problem .quantum (inputContext I) (outputContext I)
      (.option (.unsignedWord (FiniteCyclicDLP.orderWidth (problem I)))) where
  valid := inputDomain I
  accepts := fun _ output => accepts I output
  successLB := successLowerBound budget wellFormed
  states := []
  resources := resourceBudget I B budget
  depth := .quantum (fun _ => 1) (depthLimit I B budget)

/-- A candidate circuit must fit the independent limits on every one of its actual paths. -/
public structure ClosedResourceContract (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (budget : Factoring.FailureBudget)
    (code : Circuit (inputContext I) (outputContext I)) : Prop where
  /-- All native declaration coordinates, including the opaque query, are bounded. -/
  events : ∀ path, code.resourcePool path ≤ (resourceBudget I B budget).events
  /-- The actual path excludes unused reset alternatives. -/
  eventCount : ∀ path, (code.eventTrace path).length ≤ eventCountLimit I B budget
  /-- All live storage, including borrowed points and the retained bank, is charged. -/
  resident : ∀ path, code.peakResidentSpace path ≤ (resourceBudget I B budget).resident
  /-- Auxiliary storage follows the same actual contexts and declared roles. -/
  auxiliary : ∀ path, code.peakAuxiliarySpace path ≤ (resourceBudget I B budget).auxiliary
  /-- Real measurement and classical dependencies contribute to this unit depth. -/
  depth : ∀ path, code.depth (fun _ => 1) path ≤ depthLimit I B budget

private theorem originalWidth (I : ECDLPInstance E) :
    FiniteCyclicDLP.orderWidth (problem I) = Nat.clog 2 (12 * I.subgroupOrder) := rfl

/-- The original literal Fourier width is unchanged at this public boundary. -/
public theorem nativeECDLP_specification_orderWidth (I : ECDLPInstance E) :
    FiniteCyclicDLP.orderWidth (problem I) = Nat.clog 2 (12 * I.subgroupOrder) :=
  originalWidth I

/-- The public rational target selects the same original prime-order closed repetition count. -/
public theorem nativeECDLP_specification_retryCount
    (I : ECDLPInstance E) (budget : Factoring.FailureBudget) :
    retryCountForBudget I budget = max 1 (Nat.ceil
      (Real.log ((budget.failureDenominator : Real) / budget.failureNumerator) /
        Real.log (((4 * (2 ^ FiniteCyclicDLP.orderWidth (problem I)) ^ 2 : Nat) : Real) /
          ((4 * (2 ^ FiniteCyclicDLP.orderWidth (problem I)) ^ 2 -
            I.subgroupOrder * (I.subgroupOrder - 1) : Nat) : Real)))) := by
  unfold retryCountForBudget
  rw [FiniteCyclicDLP.Concrete.Amplification.retryCountForBudget_eq_primeOrder
    (problem I) budget I.subgroupOrder_prime]
  exact FiniteCyclicDLP.PrimeOrderTailBound.retryCount_eq_closedForm
    (problem I).order (FiniteCyclicDLP.fourierModulus (problem I)) budget

/-- The sole actual complete recovery circuit satisfies every independent resource obligation. -/
theorem nativeECDLP_recovery_closedResourceContract
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I)
    (budget : Factoring.FailureBudget) :
    ClosedResourceContract I B budget
      (recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I)
        I B A (retryCountForBudget I budget)
        (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)).code where
  events := nativeECDLP_recovery_pool_le _ _ I B A _ _ _
  eventCount := nativeECDLP_recovery_eventCount_le _ _ I B A _ _ _
  resident := nativeECDLP_recovery_resident_le _ _ I B A _ _ _
  auxiliary := nativeECDLP_recovery_auxiliary_le _ _ I B A _ _ _
  depth := nativeECDLP_recovery_depth_le _ _ I B A _ _ _

end

end GateLevelAttempt.Native.Specification
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
