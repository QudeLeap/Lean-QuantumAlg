/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Algorithm.Unitary.Laws
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.State.UnitaryNeighborhood
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.State.Density

/-!
# Reference-aware approximate unitary state requirements

The independent target retains every supplied system and its correlations with
an arbitrary reference. A full-phase operator-norm bound supplies a nearby
system unitary that produces the actual joint output. This promise uses no
purity assumption and does not turn an approximation into exact target action.
-/

namespace QuantumAlg.StateRequirement
noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

@[implicit_reducible]
private def neighborhood {ctx : RuntimeCtx .quantum}
    (operator : UnitaryOperator ctx.register) (error : ℝ) (nonnegative : 0 ≤ error)
    (Reference : Register) (input : Execution.Input ctx Reference) :
    UnitaryNeighborhood
      (Register.prod (ctx.quantumLayout.selectedRegister Finset.univ) Reference) where
  width := ctx.systemCount
  layout := ctx.quantumLayout
  selection := Finset.univ
  reference := Reference
  basis := Equiv.refl _
  input := input.state.quantumMarginal
  normalized := (ExecutionState.quantumMarginal_mass input.state).trans input.normalized
  operator := operator
  error := error
  nonnegative := nonnegative

/-- The full joint output lies in an independently specified operator-norm neighborhood. -/
public def approximateUnitary {ctx : RuntimeCtx .quantum}
    (operator : UnitaryOperator ctx.register) (error : ℝ) (nonnegative : 0 ≤ error) :
    StateRequirement ctx ctx :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .unitaryNeighborhood (neighborhood operator error nonnegative Reference input)

/-- A uniform system operator bound certifies the actual output with arbitrary reference. -/
lemma approximateUnitary_holds {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {ctx : RuntimeCtx .quantum} {shape : CShape}
    (operator : UnitaryOperator ctx.register) (error : ℝ) (nonnegative : 0 ≤ error)
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (close : HilbertOperator.opNorm
      ((program.matrix environment.quantum : HilbertOperator ctx.register) -
        (operator : HilbertOperator ctx.register)) ≤ error)
    (output : Output ctx shape) {Reference : Register}
    (input : Execution.OracleInput services ctx Reference) :
    (approximateUnitary operator error nonnegative).Holds input.caller
      (({ code := .unitary program, output := output } :
        AlgorithmRun (.quantum gates oracles operations services) ctx ctx shape).finalState
          environment Reference input.state) := by
  intro value
  cases value with
  | unit =>
      refine ⟨program.matrix environment.quantum, close, ?_⟩
      have unitRead : (OutputRead.unit : OutputRead ctx .unit).eval =
          fun _ => CShape.Value.unit := rfl
      rw [unitRead, ExecutionState.executionState_mapClassical_const_block,
        AlgorithmRun.finalState_unitary_quantumMarginal,
        ← Execution.OracleInput.oracleInput_caller_quantumMarginal input]
      simp only [UnitaryNeighborhood.state, neighborhood, DensityOperator.reindex_refl,
        DensityOperator.observeSelectionWithReference_mass, DensityOperator.applyUnitary_mass,
        ExecutionState.quantumMarginal_mass]
      have mass : input.caller.state.mass = 1 := input.caller.normalized
      rw [mass, one_smul]

end
end QuantumAlg.StateRequirement
