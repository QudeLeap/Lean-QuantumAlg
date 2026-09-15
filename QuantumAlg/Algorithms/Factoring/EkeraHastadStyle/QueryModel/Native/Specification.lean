/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.SpaceCoordinates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability

/-!
# Independent contracts for the actual original-width oracle execution

The public modulus data are executable inputs. Original good-key data appear
only in the accepted-factor relation and its numerical success threshold.
Independent event coordinates include the real preparations, measurements,
reset corrections, both packs per sample, recovery and optional selection.
The positive-count bank and fixed classical slots are reused in place.

The original oracle gate clock assigns unit duration to gates and sealed
queries and zero to the other recorded events. Its allowance includes paid
resets; it is not the earlier oracle-only exact-depth formula. The finite
contract also admits arbitrary native event durations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

noncomputable section

/-- The actual final live context depends on total count, never on hidden factors or success. -/
public def outputContext (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N count : Nat) : RuntimeCtx .quantum := Retry.Finite.context base noQuantum N count

/-- The source gate clock charges each actual reset correction as well as every original query. -/
public def circuitDuration : Resource.Event .quantum → Nat
  | .gate _ => 1
  | .quantumSubroutine _ => 1
  | .preparation _ => 0
  | .measurement _ => 0
  | .classicalOperation _ => 0
  | .classicalSubroutine _ => 0

/-- The original rational calibration reserves half the failure target for the key exception. -/
public def calibratedCount (budget : FailureBudget) : Nat :=
  NativeFiniteRetry.Calibration.retryCount budget

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Original oracle factoring at an arbitrary finite total count.

**Input.** The executable input is the original public modulus specification.
The original good-key model certifies two distinct odd equal-width primes,
exact product width and the source's key condition. Every normalized incoming
classical state and arbitrary external reference is admitted.
**Output.** A real optional factor word; acceptance is one of the two declared
primes. Every live cell and the complete original bank remain in the output.
The owned final bank is unrestricted; complete borrowed restoration remains
an independent mandatory obligation.
**Resource budget.** Each real batch samples sixteen times on the same original
bank. The first batch prepares it once; later samples pay for reset. Independent
native coordinates include both real sample packs, original complete recovery,
selection and the final pack. Classical capacity is
21M + 18d + 4 + max(9M + 14, A + 8M + 2), where M is modulus width, d is
measurement width and A is the original complete recovery allocation. Zero
batches allocate only M + 1 result bits. Arbitrary event durations retain the
original tensor critical path; all caller resources retain their actual roles.
**Success.** At count k, success is at least 1 - (1 - beta)^k for the original
conditional batch floor beta. No additional sampling-independence hypothesis
or positive-count restriction is imposed.
**Source.** [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
-/
public def finiteProblem (model : GoodKeyModel N) (count : Nat)
    (duration : Resource.Event .quantum → Nat) :
    Problem .quantum base (outputContext base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  accepts := fun _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts model
  successLB := ⟨1 - (1 - NativeBatchSuccess.successFloor model.bitWidth) ^ count, tsub_le_self⟩
  states := []
  resources :=
    { events := Retry.Finite.eventBudget N count
      resident := Retry.Finite.additionalSpace N count + base.residentSpace
      auxiliary := Retry.Finite.additionalSpace N count + base.auxiliarySpace }
  depth := .quantum duration (Retry.Finite.durationBudget N duration count)

/-- Actual original-width oracle factoring with the explicit rational failure target.

**Input.** The executable input is the original modulus data and 0 < eta <= 1.
The factors, same-bit domain and original good-key condition are proof-side.
Every normalized incoming classical state and external reference is admitted.
**Output.** One actually stored optional word, accepted precisely when it is
one of the declared factors. All live storage and physical systems are listed;
borrowed classical-reference correlations must be restored independently.
**Resource budget.** The total count is
k = max(1, ceil(log(2/eta) / log(256/147))). The same independent finite native
allowance pays for every real sample, reset, recovery and selector. The bank
has the original 3n + 2 floor((n+2)/2) + 1 qubits on same-bit inputs; fixed
classical storage has the finite contract's explicit formula and no k factor.
The gate/query clock charges the real reset corrections. Its independent
upper bound does not assert equality with the former oracle-only depth.
**Success.** Conditional success is at least 1 - eta/2. The separate uniform
key-distribution exception is not treated as another per-round failure event.
**Source.** [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
-/
public def problem (model : GoodKeyModel N) (budget : FailureBudget) :
    Problem .quantum base (outputContext base noQuantum N (calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  { finiteProblem base noQuantum model (calibratedCount budget) circuitDuration with
    successLB := ⟨1 - ENNReal.ofReal (budget.value / 2), tsub_le_self⟩ }

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
