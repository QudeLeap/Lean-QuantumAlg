/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Algorithm.Unitary.Laws
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Base.State.Density

/-!
# Independent complete-state targets for unitary execution

The specification takes a mathematical unitary without circuit metadata.
It describes the full incoming quantum state transformed by that operator
and the identity on an arbitrary reference. A separate equality with the
placed program proves that its actual complete execution meets this target.
No input purity or factorization assumption is needed.
-/

namespace QuantumAlg.StateRequirement

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def unitaryTarget {ctx : RuntimeCtx .quantum} (operator : UnitaryOperator ctx.register)
    (Reference : Register) (input : Execution.Input ctx Reference) :
    DensityOperator (Register.prod
      (ctx.quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference ctx.quantumLayout Finset.univ Reference
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))
      input.state.quantumMarginal)

private lemma unitaryTarget_normalized {ctx : RuntimeCtx .quantum}
    (operator : UnitaryOperator ctx.register) (Reference : Register)
    (input : Execution.Input ctx Reference) :
    (unitaryTarget operator Reference input).IsNormalized := by
  change (unitaryTarget operator Reference input).mass = 1
  rw [unitaryTarget, DensityOperator.observeSelectionWithReference_mass,
    DensityOperator.applyUnitary_mass, ExecutionState.quantumMarginal_mass]
  exact input.normalized

/-- Independent full-layout and reference-aware action of a metadata-free unitary. -/
public def unitary {ctx : RuntimeCtx .quantum} (operator : UnitaryOperator ctx.register) :
    StateRequirement ctx ctx :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (unitaryTarget operator Reference input)
      (unitaryTarget_normalized operator Reference input)

/-- Equality of the actual program operator proves its independent full joint-state target. -/
lemma unitary_holds {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {ctx : RuntimeCtx .quantum} {shape : CShape}
    (operator : UnitaryOperator ctx.register)
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (same : program.matrix environment.quantum = operator)
    (output : Output ctx shape) {Reference : Register}
    (input : Execution.OracleInput services ctx Reference) :
    (unitary operator).Holds input.caller
      (({ code := .unitary program, output := output } :
        AlgorithmRun (.quantum gates oracles operations services) ctx ctx shape).finalState
          environment Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (unitaryTarget operator Reference input.caller)
          (unitaryTarget_normalized operator Reference input.caller)).Holds
        (DensityOperator.observeSelectionWithReference ctx.quantumLayout Finset.univ Reference
          (((({ code := .unitary program, output := output } :
            AlgorithmRun (.quantum gates oracles operations services) ctx ctx shape).finalState
              environment Reference input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block,
        AlgorithmRun.finalState_unitary_quantumMarginal, same,
        ← Execution.OracleInput.oracleInput_caller_quantumMarginal input]
      change (unitaryTarget operator Reference input.caller).matrix =
        ((unitaryTarget operator Reference input.caller).mass : ℝ) •
          (unitaryTarget operator Reference input.caller).matrix
      rw [unitaryTarget_normalized]
      simp only [one_smul]

end

end QuantumAlg.StateRequirement
