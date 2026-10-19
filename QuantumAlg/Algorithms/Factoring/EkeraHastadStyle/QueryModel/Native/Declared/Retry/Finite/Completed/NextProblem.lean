/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Admission
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.AllKeys
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Space

/-!
# Independent problem for one reused completed EH batch

The next batch operates on the original retained selector and physical bank.
Its input domain is stated on the local caller/service state, without naming
an implementation or assuming independent hidden service state. The actual
prefix supplies this domain through `completed_nextInput_selectedSound`.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- A complete further batch runs recovery, first-success selection, a paid
pack into the factor cell and physical reset on the same retained bank. -/
def nextCompletedRun : AlgorithmRun (model N)
    (Retry.context base noQuantum N) (Retry.context base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N) where
  code := nextCompletedCode base noQuantum N input
  output := Output.all (Retry.context base noQuantum N)
    (.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))

/-- The actual further-batch algorithm consumes the live retained selector. -/
def nextCompletedAlgorithm : Algorithm (model N)
    (Retry.context base noQuantum N) (Retry.context base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N) where
  run := nextCompletedRun base noQuantum N input

/-- The complete reused batch leaves the owned bank in its predetermined zero
state at every optional-factor output. Reference correlations are retained by
the separate physical restart certificate. -/
def nextStateRequirement : StateRequirement
    (Retry.context base noQuantum N) (Retry.context base noQuantum N) :=
  .marginal Finset.univ
    (.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
    (fun _ _ => .pure (NormalizedVector.ket
      ((Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis
        Finset.univ (Retry.context base noQuantum N).quantumLayout.zeroLabel)))

/-- One further batch, with an input-based sound-selector admission domain.

**Input.**
- A normalized live caller/service state whose populated selector is
a nontrivial factor on every positive-mass record; arbitrary references remain admitted.
**Output.**
- The retained optional factor, complete live store, and reset bank.
**Resource budget.**
- One complete later-batch event allowance, fixed live space,
and its own serial duration, including recovery, pack and physical reset.
**Success.**
- At least one minus the independent one-batch source failure mass;
accepted outputs are nontrivial factors.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
-/
def nextCompletedProblem :
    Problem (model N) (Retry.context base noQuantum N)
      (Retry.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := Unit
  valid := fun environment _ _ => environment = sourceEnvironment input
  initialization := fun _ _ => selectedSound base noQuantum N
  accepts := fun _ _ _ output => output ∈ AllKeys.accepts N
  successLB := fun _ _ => ⟨1 - AllKeys.sourceFailure input, tsub_le_self⟩
  states := fun _ _ => [nextStateRequirement base noQuantum N]
  resources :=
    { events := nextCompletedEventBudget N
      resident := Retry.additionalSpace N + base.residentSpace
      auxiliary := Retry.additionalSpace N + base.auxiliarySpace }
  quantumTimeLimit := nextCompletedDurationBudget N Resource.Event.quantumDuration

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
