/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.MarginalLaws

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
theorem finalState_unitary_quantumMarginal {ctx : RuntimeCtx .quantum} {shape : CShape}
    (program : UnitaryCircuit ctx.register) (placement : program.physical_idx = ctx.physicalIdx)
    (output : Output ctx shape) (Reference : Register)
    (input : ExecutionState (Execution.Store ctx) (Register.prod ctx.register Reference)) :
    (({ code := .unitary program placement, output := output } :
        AlgorithmRun ctx ctx shape).finalState Reference input).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
        input.quantumMarginal := by
  let run : AlgorithmRun ctx ctx shape := { code := .unitary program placement, output := output }
  let initial := input.mapClassical (fun store => (store, store))
  let operator := UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)
  calc
    (run.finalState Reference input).quantumMarginal =
        (run.execute Reference input).quantumMarginal :=
      ExecutionState.mapClassical_quantumMarginal (run.execute Reference input) Prod.fst
    _ = (initial.applyUnitary (fun _ => operator)).quantumMarginal :=
      ExecutionState.mapClassical_quantumMarginal
        (initial.applyUnitary (fun _ => operator)) (fun value => (value.1, (value.2, ())))
    _ = DensityOperator.applyUnitary operator initial.quantumMarginal :=
      ExecutionState.fixedUnitary_quantumMarginal initial operator
    _ = _ := congrArg (DensityOperator.applyUnitary operator)
      (ExecutionState.mapClassical_quantumMarginal input (fun store => (store, store)))

end

end QuantumAlg.AlgorithmRun
