/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.SelectedDistribution
import all QuantumAlg.Core.Execution.Input.Successor.Distribution

/-!
# Input-based admission for subsequent completed EH batches

The later-batch domain reads only the incoming local store state: every
positive-mass retained selector is either empty or a checked nontrivial
factor. The actual predecessor execution supplies this domain for every
original caller, hidden service and external reference input.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- A structural, implementation-independent local entry domain: every
populated selector with positive mass is a valid nontrivial factor. -/
def selectedSound (state : ExecutionState
    (Store (Retry.context base noQuantum N) × (model N).HiddenState)
    (Retry.context base noQuantum N).register) : Prop :=
  ∀ record word, 0 < (state.block record).mass →
    Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection
      record.1 = .optionSome word →
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N

/-- The actual successor input's live selector retains the exact independent
first-success law; only execution histories were forgotten at the cut. -/
lemma completed_nextInput_selectedDistribution (laterCount : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    ((((completedCode base noQuantum N input laterCount).nextInput (sourceEnvironment input)
      original).state.toPMF
      ((completedCode base noQuantum N input laterCount).nextInput (sourceEnvironment input)
        original).normalized).map
        (fun entry => Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1)) =
      Optional.Distribution.selectedDistribution
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        (laterCount + 1) := by
  let entered := original.state.mapClassical
    (fun entry => (entry.1, (entry.2, ())))
  have enteredNormalized : entered.IsNormalized :=
    original.state.mapClassical_normalized original.normalized
      (fun entry => (entry.1, (entry.2, ())))
  exact (Circuit.nextInput_readoutDistribution
    (completedCode base noQuantum N input laterCount) (sourceEnvironment input) original
    (fun store => Optional.selectedValue
      (Retry.selectionRefs base noQuantum N).selection store)).trans
    (completed_selectedDistribution base noQuantum N input laterCount
      entered enteredNormalized)

/-- After any positive number of completed batches, the actual normalized
predecessor output satisfies the next batch's input-based selector domain. -/
lemma completed_nextInput_selectedSound (laterCount : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    selectedSound base noQuantum N
      ((completedCode base noQuantum N input laterCount).nextInput (sourceEnvironment input)
        original).localState := by
  intro record word positive selected
  have supported := Circuit.nextInput_local_readout_support
    (completedCode base noQuantum N input laterCount) (sourceEnvironment input) original
    (fun store => Optional.selectedValue
      (Retry.selectionRefs base noQuantum N).selection store)
    record positive
  rw [completed_nextInput_selectedDistribution base noQuantum N input laterCount original]
    at supported
  rw [selected] at supported
  have source := Optional.Distribution.selectedDistribution_some_support
    ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
    (laterCount + 1) word supported
  exact Batch.Recovery.sourceOutput_some_sound N input word source

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
