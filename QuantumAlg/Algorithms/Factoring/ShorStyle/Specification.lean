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
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Util.NumberTheory.Factoring
public import Mathlib.Data.Nat.Prime.Defs
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Schedule
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
and quantum time of the complete execution, including initialization and all attempts.
-/

namespace QuantumAlg.Factoring.ShorStyle

noncomputable section

open Canonical.DeclaredSource.Runtime

/-- The original zero-width borrowed unit anchor carries no factor or prepared quantum bank. -/
public def pre : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput (RuntimeCtx.empty : RuntimeCtx .quantum).canonicalFreshKey
    .unit (RuntimeCtx.empty : RuntimeCtx .quantum).canonicalFreshKey_fresh

private lemma pre_quantumWires : pre.quantumWires = [] := rfl

/-- The optional original modulus-width factor word. -/
public def OutputShape (N : Nat) : CShape := .option (.unsignedWord (Canonical.modulusBits N))

/-- The public width grants ordinary XOR modular-exponentiation query syntax. -/
public def queryModel (N : Nat) : OracleModel :=
  Canonical.DeclaredSource.model (Canonical.modulusBits N) (Canonical.phaseBits N)

/-- The query signature and native classical work are independent of unknown factors. -/
@[expose, reducible] public def executionModel (N : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model (queryModel N) BitWord.model .empty

/-- The legal source interpretation is separate from the fixed query program. -/
public def sourceEnvironment (N : Nat) (input : Canonical.Input N) :
    (executionModel N).Environment := Canonical.DeclaredSource.Runtime.environment input

/-- Every retained result and the one actual bank survive in the complete output. -/
public def post (N : Nat) (budget : FailureBudget) : RuntimeCtx .quantum :=
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
cell and the full simultaneous native scratch. Quantum time counts the complete
real path under the fixed quantum event duration.
For $S=2t+3\binom{t}{2}+3m$, $D=2\binom{t}{2}+3\lfloor t/2\rfloor$,
$M=t+3m$ and the width-only complete classical allowance $C(N)$ in
`Scalar.roundClassicalOperations`, the same computation has scalar bounds
$3m$ qubits, zero Toffoli gates, $kD$ CNOTs, $kS$ single-qubit gates,
$3m+k(S+D+1+M+C(N))+2$ quantum time,
$k(22m+1)+70m+42$ bits in each live-space role and $kC(N)+2$ classical
operations. Queries are bounded by $k$, preparations by $3m$ and measurements
by $kM$, all at their original coordinates and actual system dimensions.
The same conservative bound also controls unit-event chronological depth.
**Success.** A declared prime factor is returned with probability at least
$1-eta$. Borrowed joint correlations and the complete original reference are
preserved by the same execution that supplies all resource observations.
**Source.** [Sho95, source.tex:1124-1169,1183-1245] for original sampling,
checked recovery and amplification; [dW19, qcnotes.tex:2203-2225] for the
ordinary XOR query interpretation. Native event, space and depth allowances
are proved for the actual composition, rather than supplied by these sources.
-/
public def problem (N : Nat) (input : Canonical.Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Problem (executionModel N) pre (post N budget) (OutputShape N) :=
  Machine.problem pre pre_quantumWires N input budget wellFormed

/-- Unknown factors enter only the specification witness of the same public problem. -/
public def factorWitness (N : Nat) (input : Canonical.Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) :
    (problem N input budget wellFormed).Witness := witness

/-- Every normalized caller and reference extension admits each legal factor witness. -/
public lemma source_admits (N : Nat) (input : Canonical.Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : Execution.OracleInput (executionModel N).classicalOracles pre Reference) :
    (problem N input budget wellFormed).Admits (sourceEnvironment N input)
      (factorWitness N input budget wellFormed witness) original :=
  ⟨rfl, trivial⟩

/-- The source interpretation satisfies the public local input domain. -/
public lemma source_valid (N : Nat) (input : Canonical.Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : Execution.OracleInput (executionModel N).classicalOracles pre Reference) :
    (problem N input budget wellFormed).valid (sourceEnvironment N input)
      (factorWitness N input budget wellFormed witness) original.caller.localState := by
  rfl

/-- Every original normalized caller satisfies the source initialization contract. -/
public lemma source_initialized (N : Nat) (input : Canonical.Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : Execution.OracleInput (executionModel N).classicalOracles pre Reference) :
    (problem N input budget wellFormed).initialization (sourceEnvironment N input)
      (factorWitness N input budget wellFormed witness) original.localState := by
  trivial

/-- Complete chronological event allowance, including every round and the final paid pack. -/
public def wholeRunDepthLimit (N : Nat)
    (budget : FailureBudget) : Nat :=
  ResourcePool.weightedCount (fun _ => 1)
    (Machine.eventEnvelope N
      (Canonical.retryCount N budget))

end

end QuantumAlg.Factoring.ShorStyle
