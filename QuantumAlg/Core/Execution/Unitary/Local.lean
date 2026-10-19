/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Local.Marginals

/-!
# The actual local marginal after a placed unitary instruction

The interpreter acts by the program's unitary on the local register and by
identity on the external reference. Summing actual classical blocks and
history then gives conjugation of the incoming local marginal. The result
applies to an intermediate instruction in any complete circuit.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

variable {allowAllocation : Bool}

/-- The same instruction conjugates the complete joint input and its external reference. -/
lemma unitary_jointDensity {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : ExecutionModel.Environment (.quantum gates oracles operations services))
    {ctx : RuntimeCtx .quantum} (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (services.HiddenState × H)) :
    ((Circuit.unitary (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := services) program).execute environment
      Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program.matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        state.quantumMarginal := by
  simp only [execute_unitary, ExecutionState.mapClassical_quantumMarginal]
  exact ExecutionState.fixedUnitary_quantumMarginal state
    (UnitaryOperator.prodTensor (program.matrix environment.quantum)
      (1 : UnitaryOperator Reference))

/-- A placed unitary conjugates the actual incoming local quantum marginal. -/
lemma unitary_localDensity {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : ExecutionModel.Environment (.quantum gates oracles operations services))
    {ctx : RuntimeCtx .quantum} (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (services.HiddenState × H)) :
    ((Circuit.unitary (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := services) program).execute environment
      Reference state).quantumMarginal.marginalLeft =
        DensityOperator.applyUnitary (program.matrix environment.quantum)
          state.quantumMarginal.marginalLeft := by
  rw [unitary_jointDensity (allowAllocation := allowAllocation)]
  exact DensityOperator.localUnitary_marginalLeft (program.matrix environment.quantum)
    state.quantumMarginal

end

end QuantumAlg.Circuit
