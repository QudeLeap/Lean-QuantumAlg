/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Restart
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint.Time
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.SpaceCoordinates
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Statistics
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Restart
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.KeyAverage
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.PrimeAcceptance
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.SpaceCoordinates

/-!
# Ekerå–Håstad factoring with the actual original-width oracle bank

One internally prepared bank carries the original two exponent registers and
modulus-width XOR target. Sixteen actual samples share each retained parameter;
later samples reset the same bank. Actual recovery and first-accepted selection
operate on the stored observations. The external reference and every borrowed
caller entry are preserved jointly. Key generation is a theorem-side average
of this same execution, outside the circuit resource ledger.

The RSA reduction is [EH17, source.tex:878-966]. The source quantum state and
measurement law are [E23, arxiv-v5.tex:218-299]; lattice post-processing is
[E23, arxiv-v5.tex:329-355]. The exact named query and QFT construction observations survive
bank reuse. Actual resets, result packing and reused classical storage have
separate complete native allowances, not the former oracle-only depth ledger.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle

open Canonical Canonical.OracleModel

open Native.Declared.Retry

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Completed declared-oracle factoring at a shared real failure target.

**Input.**
- The original modulus input and a real target $0 < \eta < 1$.
- All normalized caller, service and external-reference states remain admitted.
**Output.**
- The original retained optional factor and complete quantum bank,
  with the same state and borrowed-restoration requirements.
**Resource budget.**
- The independent completed natural-count formulas at
  $k = \lceil\log(\eta/2)/\log(147/256)\rceil_{\mathbb N}$,
  with all initialization, recovery and resets.
**Success.**
- The exact per-input source lower bound is $1 - q(\mathrm{input})^k$,
  where $q$ is the original conditional batch failure.
- On good keys, a separate theorem gives $1 - \eta / 2$. The original
  ordered-key average charges the one-time key loss outside that retry power.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
-/
@[expose] public def problem {N : Nat} (input : Canonical.Input N)
    (η : Real) :
    Problem (Native.Declared.model N) base
      (Finite.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  Finite.completedAllProblem base noQuantum input (NativeFiniteRetry.Calibration.retryCount η)

/-- A complete original-width algorithm solves the independent EH problem. -/
public theorem main {N : Nat} (input : Canonical.Input N)
    (η : Real) (_etaPositive : 0 < η) (_etaLessOne : η < 1) :
    ∃ candidate : Algorithm (Native.Declared.model N) base
      (Finite.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N),
      candidate.Solves (problem base noQuantum input η) :=
  ⟨Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η),
    Finite.completedAlgorithm_solves base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle
