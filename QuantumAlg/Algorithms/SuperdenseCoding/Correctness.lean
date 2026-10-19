/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Admission
import all QuantumAlg.Algorithms.SuperdenseCoding.Admission
import all QuantumAlg.Algorithms.SuperdenseCoding.Channel
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Accepted outputs of actual supported superdense-coding executions

Zero incorrect-output density excludes every positive-probability incorrect
record. The proof follows the actual measurement sequence and history map
of the same complete run [dW19, qcnotes.tex:885-890,5394].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

private lemma measured_output_of_positive
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (pure : state.quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket (finalBasis count bits)))
    (entry : Store (context count) × (ClassicalOracleModel.empty.HiddenState ×
      (History × (Circuit.measurementSequence (allowAllocation := false)
        (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts count)).Path)))
    (positive : 0 < ((((Circuit.measurementSequence (allowAllocation := false)
      (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts count)).execute environment)
        Reference state).block entry).mass) :
    entry.1.read (resultInput count) = messageValue bits := by
  by_contra wrong
  let final := ((Circuit.measurementSequence (allowAllocation := false)
    (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts count)).execute environment)
      Reference state
  let bad := final.filterClassical (fun record =>
    record.1.read (resultInput count) ≠ messageValue bits)
  have zero : bad.mass = 0 := by
    rw [← ExecutionState.quantumMarginal_mass,
      superdense_measurement_wrong_output_zero environment count bits state pure,
        DensityOperator.zero_mass]
  have bound := ExecutionState.block_mass_le bad entry
  change (bad.block entry).mass ≤ bad.mass at bound
  rw [zero] at bound
  have same : bad.block entry = final.block entry := by
    change (final.filterClassical (fun record =>
      record.1.read (resultInput count) ≠ messageValue bits)).block entry = final.block entry
    rw [ExecutionState.filterClassical_block, if_pos wrong]
  rw [same] at bound
  exact (not_lt_of_ge bound) positive

private lemma mapped_positive {A B : Type} [Fintype A] [Fintype B] {R : Register}
    (decision : DecidableEq B) (state : ExecutionState A R) (update : A → B) (value : B) :
    0 < ((@ExecutionState.mapClassical A B _ _ R decision state update).block value).mass ↔
      ∃ original, update original = value ∧ 0 < (state.block original).mass := by
  cases Subsingleton.elim decision (Classical.decEq B)
  exact ExecutionState.mapClassical_block_mass_pos_iff state update value

private lemma seq_output_of_positive {execution : ExecutionModel}
    (environment : execution.Environment) {allowAllocation : Bool}
    {origin middle final : RuntimeCtx execution.kind}
    (first : Circuit execution origin middle allowAllocation)
    (second : Circuit execution middle final allowAllocation)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State origin Reference (execution.HiddenState × History))
    (property : Store final → Prop)
    (holds : ∀ previous,
      0 < (((second.execute environment) Reference ((first.execute environment)
        Reference state)).block previous).mass →
        property previous.1)
    (entry : Store final × (execution.HiddenState × (History × (first.seq second).Path)))
    (positive : 0 < ((((first.seq second).execute environment) Reference state).block entry).mass) :
    property entry.1 := by
  rw [Circuit.execute_seq, State.mapHistory] at positive
  obtain ⟨previous, same, present⟩ := (mapped_positive _ _ _ entry).mp positive
  have stored : previous.1 = entry.1 := congrArg Prod.fst same
  exact stored ▸ holds previous present

/-- Every positive actual path reads the original source message from the measurement cells. -/
public lemma superdense_code_output_of_positive
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (supported : messageSupported count bits state)
    (initial : state.quantumMarginal.marginalLeft = DensityOperator.ofPure (initialState count))
    (entry : Store (context count) ×
      (ClassicalOracleModel.empty.HiddenState × (History × (code count).Path)))
    (positive : 0 < ((((code count).execute environment) Reference state).block entry).mass) :
    entry.1.read (resultInput count) = messageValue bits := by
  exact seq_output_of_positive environment (selected count)
    (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty) (readouts count))
    state (fun store => store.read (resultInput count) = messageValue bits)
    (measured_output_of_positive environment count bits _
      (selected_localState environment count bits state supported initial)) entry positive

/-- Positive records of the standard complete run return the actual decoded message. -/
public lemma superdense_run_output_of_positive
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} (input : OracleInput .empty (context count) Reference)
    (valid : admissible count bits input.caller.localState)
    (entry : (algorithm count).run.Record)
    (positive : 0 < ((((algorithm count).run.execute environment) Reference input.state).block
      entry).mass) :
    (algorithm count).run.result entry = messageValue bits := by
  exact superdense_code_output_of_positive environment count bits (entered count input)
    (admitted_message_supported count bits input valid)
    (admitted_initial_state count bits input valid) entry positive

end
end QuantumAlg.SuperdenseCoding.Execution
