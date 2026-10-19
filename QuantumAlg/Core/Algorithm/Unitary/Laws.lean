/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Actual final states of complete unitary runs

A placed unitary acts on the full incoming quantum marginal and leaves the
external reference untouched. Summing the interpreter's classical records
and paths changes no quantum state. The output manifest only observes the
actual final store, so this statement applies to every complete output.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A complete unitary run conjugates the actual joint input by the local operator
and the identity on an arbitrary reference, for every classical correlation. -/
lemma finalState_unitary_quantumMarginal {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {ctx : RuntimeCtx .quantum} {shape : CShape}
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (output : Output ctx shape) (Reference : Register)
    (input : ExecutionState (Execution.Store ctx × services.HiddenState)
      (Register.prod ctx.register Reference)) :
    (({ code := .unitary program, output := output } :
        AlgorithmRun (.quantum gates oracles operations services) ctx ctx shape).finalState
          environment Reference input).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program.matrix environment.quantum)
        (1 : UnitaryOperator Reference))
        input.quantumMarginal := by
  let run : AlgorithmRun (.quantum gates oracles operations services) ctx ctx shape :=
    { code := .unitary program, output := output }
  let initial := input.mapClassical (fun value => (value.1, (value.2, value.1)))
  let operator := UnitaryOperator.prodTensor (program.matrix environment.quantum)
        (1 : UnitaryOperator Reference)
  calc
    (run.finalState environment Reference input).quantumMarginal =
        (run.execute environment Reference input).quantumMarginal :=
      ExecutionState.mapClassical_quantumMarginal (run.execute environment Reference input) Prod.fst
    _ = (initial.applyUnitary (fun _ => operator)).quantumMarginal := by
      change ((Circuit.unitary (operations := operations) (classicalOracles := services)
        program).execute environment Reference initial).quantumMarginal = _
      rw [Circuit.execute_unitary]
      exact ExecutionState.mapClassical_quantumMarginal
        (initial.applyUnitary (fun _ => operator))
        (fun value => (value.1, (value.2.1, (value.2.2, ()))))
    _ = DensityOperator.applyUnitary operator initial.quantumMarginal :=
      ExecutionState.fixedUnitary_quantumMarginal initial operator
    _ = _ := congrArg (DensityOperator.applyUnitary operator)
      (ExecutionState.mapClassical_quantumMarginal input
        (fun value => (value.1, (value.2, value.1))))

end

end QuantumAlg.AlgorithmRun
