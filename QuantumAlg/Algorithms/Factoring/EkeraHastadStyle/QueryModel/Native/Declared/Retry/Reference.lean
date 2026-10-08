/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Selection
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Reference-aware declared EH first-success selection

The real unpack and selector update each preserve the complete quantum and
external-reference matrix while updating only their paid classical cells.
The final paid pack copies the selected value into the reused factor cell.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The paid selector realizes the exact first-success update in every
external-reference matrix coefficient, including correlations with history. -/
theorem select_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((select base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (Optional.retainValue
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)
          (entry.1.read (.storage (factorRef base noQuantum N).toCStorageRef))))
        left right := by
  let update := fun entry : Store (context base noQuantum N) ×
      ((model input).HiddenState × History) =>
    ((selectionStep base noQuantum N input entry.1).1,
      (entry.2.1, (entry.2.2, (selectionStep base noQuantum N input entry.1).2)))
  let observe := fun store : Store (context base noQuantum N) =>
    weight (Optional.selectedValue (selectionRefs base noQuantum N).selection store)
  have executed := congrArg
    (fun output : State (context base noQuantum N) Reference
        ((model input).HiddenState × (History × (select base noQuantum N input).Path)) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) left right)
    (select_execute base noQuantum N input Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry.1) left right).trans ?_)
  apply congrArg
    (fun observe : (Store (context base noQuantum N) ×
        ((model input).HiddenState × History)) →
          (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (select_value base noQuantum N input entry.1)

/-- The real final pack reads the chosen factor from the actual selector cells
in every external-reference matrix coefficient. -/
theorem pack_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((pack base noQuantum N input).execute Reference state)
      (fun entry _ => weight (entry.1.read
        (.storage (factorRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
        left right := by
  let update := fun entry : Store (context base noQuantum N) ×
      ((model input).HiddenState × History) =>
    ((packStep base noQuantum N input entry.1).1,
      (entry.2.1, (entry.2.2, (packStep base noQuantum N input entry.1).2)))
  let observe := fun store : Store (context base noQuantum N) =>
    weight (store.read (.storage (factorRef base noQuantum N).toCStorageRef))
  have executed := congrArg
    (fun output : State (context base noQuantum N) Reference
        ((model input).HiddenState × (History × (pack base noQuantum N input).Path)) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) left right)
    (pack_execute base noQuantum N input Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry.1) left right).trans ?_)
  apply congrArg
    (fun observe : (Store (context base noQuantum N) ×
        ((model input).HiddenState × History)) →
          (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (pack_value base noQuantum N input entry.1)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
