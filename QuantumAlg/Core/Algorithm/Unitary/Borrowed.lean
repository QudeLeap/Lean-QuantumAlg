/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.Unitary.Laws
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Borrowed observations of complete unitary runs

Recording the initial caller store as mathematical history preserves every
borrowed observation. An actual local unitary with no borrowed runtime cells
or wires therefore restores the complete external reference observation.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A complete local unitary run preserves an empty borrowed interface and its reference. -/
lemma restoresBorrowed_unitary_noBorrowed
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {ctx : RuntimeCtx .quantum} {shape : CShape}
    (noClassical : ctx.borrowedClassicalShape = .unit)
    (noQuantum : ctx.borrowedQuantumWires = [])
    (program : UnitaryCircuit gates oracles ctx.quantumLayout) (output : Output ctx shape)
    {Reference : Register} (input : Execution.OracleInput services ctx Reference) :
    ({ code := Circuit.unitary program, output := output } :
      AlgorithmRun (.quantum gates oracles operations services) ctx ctx shape).RestoresBorrowed
        environment input := by
  let run : AlgorithmRun (.quantum gates oracles operations services) ctx ctx shape :=
    { code := Circuit.unitary program, output := output }
  have marginal : (run.execute environment Reference input.state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program.matrix environment.quantum)
        (1 : UnitaryOperator Reference))
        input.state.quantumMarginal := by
    exact (ExecutionState.mapClassical_quantumMarginal
      (run.execute environment Reference input.state) Prod.fst).symm.trans
        (finalState_unitary_quantumMarginal environment program output Reference input.state)
  unfold RestoresBorrowed Circuit.BorrowedRestored
  rw [Execution.observeBorrowedAfter_sameContext]
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [Execution.observeBorrowed_empty_entry noClassical noQuantum,
    Execution.observeBorrowed_empty_entry noClassical noQuantum]
  change (∑ basis : ctx.register.Index,
    (run.execute environment Reference input.state).quantumMarginal.matrix
      (basis, refLeft) (basis, refRight)) = _
  rw [marginal]
  exact DensityOperator.localUnitary_reference_entry (program.matrix environment.quantum)
    input.state.quantumMarginal
    refLeft refRight

end

end QuantumAlg.AlgorithmRun
