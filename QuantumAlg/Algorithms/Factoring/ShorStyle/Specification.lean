/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Execution.CycleSchedule
public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Util.NumberTheory.Factoring
public import Mathlib.Data.Nat.Prime.Defs
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Calibrated
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Placement
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Model
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters

/-!
# Original-input declared modular-exponentiation Shor factoring specification

The known modulus and original rational failure target determine the real run.
Unknown factors occur only in its mathematical accepted event. The complete
independent contract includes all native classical and quantum events, the
owned physical bank, every live retained result, the full reference promise
and the actual chronological depth. Its separate complete-cycle plan includes
initialization in the first actual attempt.
-/

namespace QuantumAlg.Factoring.ShorStyle

noncomputable section

open Canonical.DeclaredSource.Runtime

/-- The original zero-width borrowed unit anchor carries no factor or prepared quantum bank. -/
public def pre : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput (RuntimeCtx.empty : RuntimeCtx .quantum).canonicalFreshKey
    .unit (RuntimeCtx.empty : RuntimeCtx .quantum).canonicalFreshKey_fresh

private theorem pre_quantumWires : pre.quantumWires = [] := rfl

/-- The optional original modulus-width factor word. -/
public def OutputShape (N : Nat) : CShape := .option (.unsignedWord (Canonical.modulusBits N))

/-- The original declaration grants ordinary XOR modular-exponentiation queries. -/
public def queryModel {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) : OracleModel :=
  Canonical.DeclaredSource.model
    (Canonical.DeclaredSource.sourceBounds (Canonical.Probability.Input.ofSemiprimeModel model))
    (Canonical.phaseBits N)

/-- The fixed declaration-owned query model includes selected native gates and classical work. -/
@[expose, reducible]
public def executionModel {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) : ExecutionModel :=
  .quantum AlgorithmGate.model (queryModel model) BitWord.model .empty

/-- Every genuine retained result and the one actual bank survive in the complete output. -/
public def post {N : Nat} (_model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) : RuntimeCtx .quantum :=
  Machine.context pre pre_quantumWires N (Canonical.retryCount N budget)

/-- The original executable input has only the zero-width unit anchor. -/
public def inputStore : Execution.Store pre := ⟨(.unit, ())⟩

/-- Distinct unknown prime proofs certify the known product without entering runtime storage. -/
public def semiprimeModelOfDistinctPrimes {N p q : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hN : N = p * q) : NumberTheory.Factoring.SemiprimeFactorModel N := by
  subst N
  exact NumberTheory.Factoring.SemiprimeFactorModel.ofDistinctPrimes hp hq hpq

/-- Shor factoring from the original caller in the declared XOR query model.

**Input.** A known product $N=pq$ of unknown distinct primes and the original
rational failure target $0<eta<=1$. The executable input is the zero-width unit
anchor, with every normalized external reference extension admitted. Put
$m=ceil(log_2 N)$ and $t=2m$. The original logarithmic calibration selects a
positive retry count $k$ from $N$ and $eta$; no count or factor is supplied.
**Output.** An optional $m$-bit word naming $p$ or $q$. The full live manifest
retains every true sampled parameter, phase measurement, recovery destination
and selector head. Every result fiber, including zero-mass fibers, has the
fixed full zero bank jointly with the incoming reference.
**Resource budget.** One physical $3m$-qubit bank is initialized once. Each
complete round includes actual random source preparation, one selected ordinary
modular-exponentiation query, native Hadamards and inverse QFT, measured readout,
full native recovery, first-success feedback and paid physical reset. One actual
terminal option pack completes the whole run. The independent event allowance
is initialization plus $k$ complete-round allowances plus the terminal pack.
Both live-space budgets include all five selector heads, every surviving source
cell and the full simultaneous native scratch. Unit-duration chronological
depth counts the entire real path; maximum complete-cycle depth additionally
uses the independently prescribed first initialized attempt and reused rounds.
For $S=2t+3\binom{t}{2}+3m$, $D=2\binom{t}{2}+3\lfloor t/2\rfloor$,
$M=t+3m$ and the width-only complete classical allowance $C(N)$ in
`Scalar.roundClassicalOperations`, the same computation has scalar bounds
$3m$ qubits, zero Toffoli gates, $kD$ CNOTs, $kS$ single-qubit gates,
$3m+1+S+D+1+M+C(N)$ maximum complete-cycle depth,
$k(22m+1)+70m+42$ bits in each live-space role and $kC(N)+2$ classical
operations. Queries are bounded by $k$, preparations by $3m$ and measurements
by $kM$, all at their original coordinates and actual system dimensions.
The separate whole chronological bound is $3m+k(S+D+1+M+C(N))+2$.
**Success.** A declared prime factor is returned with probability at least
$1-eta$. Borrowed joint correlations and the complete original reference are
preserved by the same execution that supplies all resource observations.
**Source.** [Sho95, source.tex:1124-1169,1183-1245] for original sampling,
checked recovery and amplification; [dW19, qcnotes.tex:2203-2225] for the
ordinary XOR query interpretation. Native event, space and depth allowances
are proved for the actual composition, rather than supplied by these sources.
-/
public def problem {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Problem (executionModel model) pre (post model budget) (OutputShape N) :=
  Machine.problem pre pre_quantumWires model budget wellFormed (fun _ => 1) (fun _ => rfl)

/-- The same original-input outcome and its fixed complete physically initialized cycle plan. -/
public def completeCycleProblem {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    CycleProblem (executionModel model) pre (post model budget) (OutputShape N) :=
  Machine.calibratedCycleProblem pre pre_quantumWires model budget wellFormed
    (fun _ => 1) (fun _ => rfl)

/-- Independent unit-duration maximum allowance for one full initialized attempt. -/
public def maximumCycleDepthLimit {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) : Nat :=
  ResourcePool.weightedCount (fun _ => 1)
    (Initialized.firstEnvelope (Canonical.Probability.Input.ofSemiprimeModel model))

/-- Complete chronological event allowance, including every round and the final paid pack. -/
public def wholeRunDepthLimit {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) : Nat :=
  ResourcePool.weightedCount (fun _ => 1)
    (Machine.eventEnvelope (Canonical.Probability.Input.ofSemiprimeModel model)
      (Canonical.retryCount N budget))

end

end QuantumAlg.Factoring.ShorStyle
