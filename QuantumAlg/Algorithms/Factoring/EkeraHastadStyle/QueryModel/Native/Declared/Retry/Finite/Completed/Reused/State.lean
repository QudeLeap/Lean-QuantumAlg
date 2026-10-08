/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.NextProblem
import all QuantumAlg.Core.Execution.Basis.Seeded.ReadoutPromise

/-!
# Pure bank state after one physically reused EH batch

The terminal reset fixes the full bank at one seed for every executed record.
The actual factor-cell readout therefore has a pure bank even when the input
is correlated with hidden service state or an external reference. A generic
history projection transfers that result to the algorithm's `finalState`.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The actual further-batch circuit resets every owned wire after the paid
factor pack. Every factor-cell readout, including impossible observations,
has the same predetermined pure bank state. -/
theorem nextCompleted_execution_readout_pure {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.pure (NormalizedVector.ket
      ((Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis Finset.univ
        (Retry.context base noQuantum N).quantumLayout.zeroLabel))).Holds
      (DensityOperator.observeSelection
        (Retry.context base noQuantum N).quantumLayout Finset.univ Reference
        ((((nextCompletedCode base noQuantum N input).execute Reference state).mapClassical
          (fun entry => entry.1.read
            (.storage (Retry.factorRef base noQuantum N).toCStorageRef))).block value)) := by
  exact BasisSeeded.readout_pure_fullSelection
    ((nextCompletedCode base noQuantum N input).execute Reference state)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
    (nextCompleted_seeded base noQuantum N input state)
    (fun store => store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
    value

private irreducible_def sealedNextRun : AlgorithmRun (model input)
    (Retry.context base noQuantum N) (Retry.context base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N) :=
  nextCompletedRun base noQuantum N input

private theorem sealedNextRun_code :
    (sealedNextRun base noQuantum N input).code =
      nextCompletedCode base noQuantum N input := by
  rw [sealedNextRun_def]
  rfl

private theorem sealedNextRun_output :
    (sealedNextRun base noQuantum N input).output =
      (nextCompletedRun base noQuantum N input).output := by
  rw [sealedNextRun_def]

private theorem sealedNextRun_pureReadout {Reference : Register}
    (original : OracleInput (model input).classicalOracles
      (Retry.context base noQuantum N) Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.pure (NormalizedVector.ket
      ((Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis Finset.univ
        (Retry.context base noQuantum N).quantumLayout.zeroLabel))).Holds
      (DensityOperator.observeSelection
        (Retry.context base noQuantum N).quantumLayout Finset.univ Reference
        ((((sealedNextRun base noQuantum N input).finalState Reference original.state).mapClassical
          (sealedNextRun base noQuantum N input).output.eval).block value)) := by
  apply AlgorithmRun.pure_fullSelection_of_executionReadout
    (sealedNextRun base noQuantum N input)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
  intro reference history _ state outcome
  rw [sealedNextRun_code, sealedNextRun_output]
  exact nextCompleted_execution_readout_pure base noQuantum N input state outcome

/-- The sealed run avoids unfolding the complete circuit while the generic
history projection checks the actual factor-cell readout. -/
private theorem sealedNextRun_stateRequirement_holds {Reference : Register}
    (original : OracleInput (model input).classicalOracles
      (Retry.context base noQuantum N) Reference) :
    (nextStateRequirement base noQuantum N).Holds original.caller
      ((sealedNextRun base noQuantum N input).finalState Reference original.state) := by
  intro value
  have pure := sealedNextRun_pureReadout base noQuantum N input original value
  have readEq : (sealedNextRun base noQuantum N input).output.eval =
      (OutputRead.read
        (.storage (Retry.factorRef base noQuantum N).toCStorageRef)).eval := by
    rw [sealedNextRun_output]
    funext store
    rfl
  rw [readEq] at pure
  exact pure

/-- The public next-batch run satisfies the independent pure-bank state
requirement at every optional-factor result. -/
theorem nextCompleted_stateRequirement_holds {Reference : Register}
    (original : OracleInput (model input).classicalOracles
      (Retry.context base noQuantum N) Reference) :
    (nextStateRequirement base noQuantum N).Holds original.caller
      ((nextCompletedRun base noQuantum N input).finalState Reference original.state) := by
  have certified := sealedNextRun_stateRequirement_holds
    base noQuantum N input original
  rw [sealedNextRun_def] at certified
  exact certified

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
