/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Specification
public import QuantumAlg.Algorithms.SuperdenseCoding.Channel
import all QuantumAlg.Algorithms.SuperdenseCoding.Specification
import all QuantumAlg.Algorithms.SuperdenseCoding.Channel
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation

/-!
# Local admission applies to every complete reference extension

The actual input record retains the original caller store as mathematical
history. Positivity transfers its nonzero support back to the local caller
contract, and forgetting that history retains the same admitted Bell state.
No input-dependent quantum or classical result is postulated
[dW19, qcnotes.tex:879-890,5394].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The original store is retained only as mathematical history by the standard run interpreter. -/
def entered (count : Nat) {Reference : Register}
    (input : OracleInput .empty (context count) Reference) :
    State (context count) Reference
      (ClassicalOracleModel.empty.HiddenState × Store (context count)) :=
  input.state.mapClassical fun value => (value.1, (value.2, value.1))

/-- Every actual live branch reads the originally admitted stored message. -/
lemma admitted_message_supported (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} (input : OracleInput .empty (context count) Reference)
    (valid : admissible count bits input.caller.localState) :
    messageSupported count bits (entered count input) := by
  intro entry nonzero
  have positive : 0 < ((entered count input).block entry).mass :=
    lt_of_le_of_ne ((entered count input).block entry).mass_nonneg (Ne.symm nonzero)
  rw [entered, ExecutionState.mapClassical_block_mass_pos_iff] at positive
  obtain ⟨original, same, supported⟩ := positive
  have callerPositive := input.caller_local_mass_pos_of_joint original supported
  have value := valid.2 original.1 (ne_of_gt callerPositive)
  have stores : original.1 = entry.1 := congrArg Prod.fst same
  exact stores ▸ value

/-- Every external-reference extension has the same independently admitted local Bell resource. -/
lemma admitted_initial_state (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} (input : OracleInput .empty (context count) Reference)
    (valid : admissible count bits input.caller.localState) :
    (entered count input).quantumMarginal.marginalLeft =
      DensityOperator.ofPure (initialState count) := by
  rw [entered, ExecutionState.mapClassical_quantumMarginal]
  have promised := valid.1
  rw [Input.localState_quantumMarginal, OracleInput.oracleInput_caller_quantumMarginal] at promised
  exact promised

/-- The actual final state's full matrix equals the source action on the original input. -/
public lemma superdense_finalState_quantumMarginal (environment : model.Environment)
    (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} (input : OracleInput .empty (context count) Reference)
    (valid : admissible count bits input.caller.localState) :
    (((algorithm count).run.finalState environment) Reference input.state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (physicalOperator count bits) (1 : UnitaryOperator Reference))
        input.caller.state.quantumMarginal := by
  rw [AlgorithmRun.finalState_quantumMarginal]
  change (((code count).execute environment) Reference (entered count input)).quantumMarginal = _
  rw [superdense_complete_channel environment count bits _ (admitted_message_supported count bits
    input valid)
    (admitted_initial_state count bits input valid)]
  rw [entered, ExecutionState.mapClassical_quantumMarginal,
    OracleInput.oracleInput_caller_quantumMarginal]

end
end QuantumAlg.SuperdenseCoding.Execution
