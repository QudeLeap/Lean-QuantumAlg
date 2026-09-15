/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.State
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

/-- The same instruction conjugates the complete joint input and its external reference. -/
theorem unitary_jointDensity {ctx : RuntimeCtx .quantum}
    (program : UnitaryCircuit ctx.register) (placement : program.physical_idx = ctx.physicalIdx)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    ((Circuit.unitary program placement).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
        state.quantumMarginal :=
  (ExecutionState.mapClassical_quantumMarginal
    (state.applyUnitary fun _ =>
      UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
    (fun value => (value.1, (value.2, ())))).trans
      (ExecutionState.fixedUnitary_quantumMarginal state
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)))

/-- A placed unitary conjugates the actual incoming local quantum marginal. -/
theorem unitary_localDensity {ctx : RuntimeCtx .quantum}
    (program : UnitaryCircuit ctx.register) (placement : program.physical_idx = ctx.physicalIdx)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    ((Circuit.unitary program placement).execute
      Reference state).quantumMarginal.marginalLeft =
        DensityOperator.applyUnitary program.matrix state.quantumMarginal.marginalLeft := by
  rw [unitary_jointDensity]
  exact DensityOperator.localUnitary_marginalLeft program.matrix state.quantumMarginal

end

end QuantumAlg.Circuit
