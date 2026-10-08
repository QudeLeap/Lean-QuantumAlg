/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Caller
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Reference
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Slots.Caller

/-!
# One complete paid EH retry transition

A later batch redraws the original source, performs sixteen paid observations
and complete recovery, then updates the actual persistent first-success cells.
The selected result follows the original first-success update law in every
external-reference matrix entry.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- One actual paid later retry applies the canonical first-success update
to the previous selected value and one fresh complete batch recovery. -/
theorem next_selected_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((next base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (Optional.retainValue
            (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)
            (Batch.SourceRecovery.packedValue output)))
      left right := by
  let batch := Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input
  have split := Circuit.referenceFiberSum_execute_seq batch
    (select base noQuantum N input) state
    (fun store => weight
      (Optional.selectedValue (selectionRefs base noQuantum N).selection store))
    left right
  have selected := select_reference base noQuantum N input
    (batch.execute Reference state) weight left right
  have recovered := Batch.Recovery.nextRun_caller_reference
    (callerContext base N) (caller_empty base noQuantum N) N input
    (originalSelectionInput base N) state normalized
    (fun old factor => weight (Optional.retainValue (CShape.packOption old) factor))
    left right
  calc
    _ = ExecutionState.referenceFiberSum
        ((select base noQuantum N input).execute Reference (batch.execute Reference state))
        (fun entry _ => weight
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
        left right := split
    _ = ExecutionState.referenceFiberSum (batch.execute Reference state)
        (fun entry _ => weight (Optional.retainValue
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)
          (entry.1.read (.storage (factorRef base noQuantum N).toCStorageRef))))
        left right := selected
    _ = _ := by
      rw [caller_selectionInput base noQuantum N] at recovered
      exact recovered

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
