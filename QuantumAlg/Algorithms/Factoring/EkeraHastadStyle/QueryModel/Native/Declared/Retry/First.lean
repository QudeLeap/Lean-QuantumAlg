/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all

QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Caller

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Slots.Probability

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Reference

/-!
# First physical EH retry and initialized selector

Three real persistent selector cells are allocated before the source and
quantum bank. The first complete batch and paid recovery then write the
candidate factor, which the actual first-success update accepts from the
initial empty selector.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The first actual allocated batch, recovery and selection has exactly the
complete source law, with the initially empty selector accepting its result. -/
lemma first_selected_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((first base noQuantum N input).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
      left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (Batch.SourceRecovery.packedValue output))
      left right := by
  let allocate := Native.Retry.Slots.allocate (model := model N) base (modulusBits N)
  let recovery := Batch.Recovery.first (callerContext base N)
    (caller_empty base noQuantum N) N input
  let entered := allocate.execute (sourceEnvironment input) Reference state
  let recoveredState := recovery.execute (sourceEnvironment input) Reference entered
  let observe := fun store : Store (context base noQuantum N) =>
    weight (Optional.selectedValue (selectionRefs base noQuantum N).selection store)
  have selected := select_reference (environment := sourceEnvironment input) base noQuantum N
    recoveredState
    weight left right
  have recovered := Batch.Recovery.run_caller_reference
    (callerContext base N) (caller_empty base noQuantum N) N input
    (originalSelectionInput base N) entered
    ((allocate.execute_mass (sourceEnvironment input) Reference state).trans normalized)
    (fun old factor => weight (Optional.retainValue (CShape.packOption old) factor))
    left right
  rw [caller_selectionInput base noQuantum N] at recovered
  have initialized := allocation_selected_reference (environment := sourceEnvironment input) base N
    state
    (fun previous => ∑ output : (Batch.resultShape N).Value,
      ((Batch.sourceDistribution input output).toReal : ℂ) *
        weight (Optional.retainValue previous (Batch.SourceRecovery.packedValue output)))
    left right
  have result := (Circuit.referenceFiberSum_execute_seq allocate
    (recovery.seq (select base noQuantum N)) (sourceEnvironment input) state observe left
      right).trans
      ((Circuit.referenceFiberSum_execute_seq recovery (select base noQuantum N)
        (sourceEnvironment input) entered observe left right).trans
        (selected.trans (recovered.trans initialized)))
  refine result.trans ?_
  apply congrArg
    (fun scalar : ℂ => ExecutionState.referenceFiberSum state
      (fun _ _ => scalar) left right)
  apply Finset.sum_congr rfl
  intro output _
  simp only [Optional.retainValue]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
