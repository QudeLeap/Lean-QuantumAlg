/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Slots.Caller
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Slots.State
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Initialized EH first-success selector in the actual input state

The three real allocations retain every caller, service and external-reference
coefficient. The accepted bit starts false, so the selected optional factor
is empty before the first physical batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (N : Nat) (input : Input N)

/-- Actual selector-cell allocation begins with no accepted factor in each
external-reference matrix coefficient. -/
theorem allocation_selected_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Native.Retry.Slots.allocate (model := model input) base (modulusBits N)).execute
        Reference state)
      (fun entry _ => weight (CShape.packOption
        (entry.1.read (originalSelectionInput base N))))
      left right =
    ExecutionState.referenceFiberSum state (fun _ _ => weight .optionNone) left right := by
  let update := fun entry : Store base × ((model input).HiddenState × History) =>
    (Slots.pushStore base (modulusBits N) entry.1,
      (entry.2.1, (entry.2.2, ((), ((), ())))))
  let observe := fun store : Store (callerContext base N) =>
    weight (CShape.packOption (store.read (originalSelectionInput base N)))
  have executed := congrArg
    (fun output : State (callerContext base N) Reference
        ((model input).HiddenState ×
          (History × (Native.Retry.Slots.allocate
            (model := model input) base (modulusBits N)).Path)) =>
      ExecutionState.referenceFiberSum output
        (fun entry _ => observe entry.1) left right)
    (Slots.allocate_execute (model := model input) base (modulusBits N) Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry.1) left right).trans ?_)
  apply congrArg
    (fun observed : (Store base × ((model input).HiddenState × History)) →
        base.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observed left right)
  funext entry basis
  have initial := Slots.initial base (modulusBits N) entry.1
  change weight (CShape.packOption (.product
    ((Slots.pushStore base (modulusBits N) entry.1).read
      (.storage (Native.Retry.Slots.acceptedRef base (modulusBits N)).toCStorageRef))
    ((Slots.pushStore base (modulusBits N) entry.1).read
      (.storage (Native.Retry.Slots.selectedRef base (modulusBits N)).toCStorageRef)))) =
      weight .optionNone
  rw [initial.1, initial.2]
  rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
