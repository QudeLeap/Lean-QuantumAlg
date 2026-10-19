/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Real.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Real.Execution

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Scalar
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.ClassicalSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model

/-!
# Full declared ECDLP recovery at arbitrary positive real failure targets

The public order determines its own certified preparation expansion. One
complete named execution supplies success, all output/reference fibers,
borrowed restoration, complete-run quantum time and the original scalar resources.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget

noncomputable section
open Canonical.QueryModel Canonical.QueryModel.Recovery
variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Original point inputs and real failure target for one complete declared ECDLP execution.

**Input.** A prime-field short Weierstrass curve, a known point of known prime
order, a known nonidentity point in its subgroup, and a positive real failure
target. The input includes the ordinary group-action oracle and every external
reference extension of the original classical points. No prepared bank,
secret scalar or preparation expansion is supplied by the caller.
**Output.** An optional canonical scalar multiplying the base to the target,
with all measured cells retained, the owned bank reset to zero, and every
borrowed correlation restored in the complete returned state.
**Resource budget.** At widths f=ceil(log2 p), t=ceil(log2(12r)) and the direct
logarithmic repeat count k, the run uses 2t+2f+1 qubits, k queries,
k(2t^2+4t+6 floor(t/2)) CNOTs and k(3t^2+25t+4f+3) single-qubit gates.
Quantum time is bounded by the independent complete-run formula
`Scalar.wholeRunEvents f t k`. Classical memory is at most
max(18t^2+70t+70,18f^2+72f+69)+6f+4t+8 bits; classical work is at most
k(248ft+686t+119)+1 operations. The full mixed chronological execution,
both actual resets per round, preparation and readout remain accounted.
**Success.** Recovery succeeds with probability at least 1-eta. A unit
failure target selects a genuine zero-round initialization-and-packing run.
**Source.** [PZ03, ecc.tex:448-462,525-640]; [Sho95, source.tex:1704-1740];
[SV24, Uniform.tex:622-664,775-805,996-1024]; [RNSL17, ECDLP.tex:483-510,649-709].
-/
public abbrev problem (I : ECDLPInstance E)
    (η : Real) (positive : 0 < η) :=
  realWholeProblem I (sourceExpansion I) I.subgroupOrder_prime.two_le η positive

/-- The actual initialized run meets the full original input/output contract. -/
private lemma complete_correct (I : ECDLPInstance E)
    (η : Real) (positive : 0 < η) :
    (algorithm I η).Solves (problem I η positive) :=
  realWholeAlgorithm_solves I (sourceExpansion I) I.subgroupOrder_prime.two_le η positive

/-- One complete execution solves the independent original real-target ECDLP problem. -/
public theorem main (I : ECDLPInstance E)
    (η : Real) (positive : 0 < η) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem I η positive) :=
  ⟨algorithm I η, complete_correct I η positive⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget
