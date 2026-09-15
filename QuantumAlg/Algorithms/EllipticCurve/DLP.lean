/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Unitary
public import QuantumAlg.Algorithms.EllipticCurve.DLP.OrderPreparation
public import QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Specification
public import QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources.Space
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Endpoint
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources.Gates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources.Classical
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Specification
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Original elliptic-curve discrete logarithms with one complete native execution

The literal order preparations, opaque group-action queries, inverse Fourier
transforms, finite measurements, paid reuse and checked classical recovery
belong to the same run. Its complete output lists every surviving system and
cell, and its independent specification admits all reference extensions of
the original public input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP

noncomputable section

open Canonical.GateLevelAttempt.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Original opaque elliptic-curve discrete logarithms with finite checked recovery.

**Input.**
- A prime-field curve with the original $p > 3$ assumptions, finite affine
  public points $P,Q$, prime subgroup order $r$, and $Q$ in the subgroup of $P$.
  The certified increasing expansion $r = sum j, 2^(ell j)$ admits $s = 0$.
- Opaque access acts as $U(P,Q)|a,b,R> = |a,b,R + [a]P - [b]Q>$ on the
  entire identity-inclusive point encoding. The classical rational failure
  target satisfies $0 < eta <= 1$. Positive local input blocks contain the
  prescribed public points; arbitrary external reference extensions are allowed.
**Output.**
- An optional $t$-bit word, accepted exactly when its residue modulo $r$
  multiplies $P$ to $Q$. The actual successful word is the canonical scalar
  less than $r$. Complete output also retains both borrowed points, the bank,
  finite measurement cells and seven persistent recovery cells.
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
- The actual accepted event has probability at least $1 - eta$ for every
  admitted normalized input and reference extension. Borrowed public data
  and all its joint correlations are restored. No final zero-state promise
  is imposed, and no implementation of the opaque query is assumed.
**Source.**
- [PZ03, ecc.tex:448-462,525-640] and [Sho95, source.tex:1704-1740].
- [SV24, Uniform.tex:622-664,775-805,996-1024] for the literal expansion;
  its one-term branch is the original Hadamard preparation.
- [RNSL17, ECDLP.tex:483-510,649-709] supplies the arithmetic context;
  the event units here belong to the actual native execution.
-/
public def problem (I : ECDLPInstance E)
    (B : Canonical.OrderExpansion (Canonical.problem I).order) (_A : Canonical.Access I)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    Problem .quantum (Specification.inputContext I) (Specification.outputContext I)
      (.option (.unsignedWord (FiniteCyclicDLP.orderWidth (Canonical.problem I)))) :=
  Specification.specification I B budget wellFormed

/-- The sole named implementation allocates once and executes the actual finite recovery run. -/
public def algorithm (I : ECDLPInstance E)
    (B : Canonical.OrderExpansion (Canonical.problem I).order) (A : Canonical.Access I)
    (budget : Factoring.FailureBudget) :
    Algorithm .quantum (Specification.inputContext I) (Specification.outputContext I)
      (.option (.unsignedWord (FiniteCyclicDLP.orderWidth (Canonical.problem I)))) where
  run := recoveryRun (Canonical.Runtime.Context.pre I)
    (PublicInput.nativeECDLP_input_quantumWires I) I B A (Canonical.retryCountForBudget I budget)
    (Canonical.Runtime.Context.baseRef I) (Canonical.Runtime.Context.targetRef I)

/-- The original public inputs determine one algorithm satisfying the complete ECDLP contract. -/
public theorem main (I : ECDLPInstance E)
    (B : Canonical.OrderExpansion (Canonical.problem I).order) (A : Canonical.Access I)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    (algorithm I B A budget).Solves (problem I B A budget wellFormed) :=
  Canonical.GateLevelEndpoint.nativeECDLP_recovery_solves I B A budget wellFormed

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP
