/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Unitary.Laws
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Trace

/-!
# Complete native Bell preparation from supplied zero input qubits

The input is one supplied owned two-qubit register in state `|00>`. Executing
Hadamard on the first wire followed by CNOT produces the independently defined
Bell pure state [dW19, qcnotes.tex:622,711,741]. Both physical systems remain
live in the complete Output. Input preparation is outside this supplied-input
contract; no fresh quantum allocation or preparation instruction is executed.
-/

namespace QuantumAlg.BellStatePreparation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def qubitLayout : QubitLayout 2 :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

/-- One supplied owned two-qubit register occupying physical systems zero and one. -/
@[reducible] public def inputContext : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ layout (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private lemma layout_wires_eq_context :
    layout.wires = inputContext.quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change layout.wires = layout.wires ++ []
  exact (List.append_nil _).symm

/-- Big-endian binary encoding of the exact two physical wire values. -/
public def inputBasisEquiv : inputContext.register.Index ≃ (Qubits 2).Index :=
  (Execution.basisOfEqualWires layout inputContext.quantumLayout
    layout_wires_eq_context).symm.trans qubitLayout.binaryIndexEquiv

/-- The built-in algorithm gate set, with no oracle access. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

private def program : UnitaryCircuit AlgorithmGate.model .empty inputContext.quantumLayout :=
  Execution.unitaryOfEqualWires layout inputContext.quantumLayout layout_wires_eq_context circuit

private lemma program_matrix (environment : model.Environment) :
    (program.matrix environment.quantum)
      = UnitaryOperator.reindex inputBasisEquiv.symm (circuit.binaryMatrix environment.quantum) :=
      by
  rw [program, Execution.unitaryOfEqualWires_matrix, UnitaryCircuit.binaryMatrix,
    UnitaryOperator.unitaryOperator_reindex_trans]
  apply congrArg (fun equivalence : layout.register.Index ≃ inputContext.register.Index =>
    UnitaryOperator.reindex equivalence (circuit.matrix environment.quantum))
  apply Equiv.ext
  intro basis
  change (Execution.basisOfEqualWires layout inputContext.quantumLayout
    layout_wires_eq_context) basis =
      (Execution.basisOfEqualWires layout inputContext.quantumLayout layout_wires_eq_context)
        ((QuantumSignature.qubitsIndexEquiv 2).symm
          ((QuantumSignature.qubitsIndexEquiv 2) basis))
  rw [Equiv.symm_apply_apply]

private def code : Circuit model inputContext inputContext := .unitary program

/-- The supplied local state is exactly the pure zero input,
with every reference extension allowed. -/
@[expose] public def valid
    (state : ExecutionState (Execution.Store inputContext) inputContext.register) : Prop :=
  state.quantumMarginal =
    DensityOperator.ofPure (NormalizedVector.ket (inputBasisEquiv.symm (0 : Fin (2 ^ 2))))

private lemma input_reindexed :
    (DensityOperator.ofPure input).reindex (S := inputContext.register) inputBasisEquiv.symm =
      DensityOperator.ofPure (NormalizedVector.ket (inputBasisEquiv.symm (0 : Fin (2 ^ 2)))) := by
  have zeroInput : input = NormalizedVector.ket (0 : Fin (2 ^ 2)) :=
    NormalizedVector.tensor_ket (0 : Fin (2 ^ 1)) (0 : Fin (2 ^ 1))
  rw [zeroInput]
  apply DensityOperator.ext
  ext row column
  simp only [DensityOperator.reindex_entry, Equiv.symm_symm, DensityOperator.ofPure_matrix,
    NormalizedVector.ket_apply, ← Equiv.eq_symm_apply]

private def targetState :
    DensityOperator (inputContext.quantumLayout.selectedRegister Finset.univ) :=
  (DensityOperator.ofPure bell).reindex
    (inputBasisEquiv.symm.trans inputContext.quantumLayout.allSelectedBasisEquiv)

private lemma targetState_normalized : targetState.IsNormalized := by
  change targetState.mass = 1
  rw [targetState, DensityOperator.reindex_mass]
  exact DensityOperator.ofPure_normalized bell

/-- The independent full-register target retained by the public preparation contract. -/
public def stateRequirement : StateRequirement inputContext inputContext :=
  .marginal Finset.univ .unit fun _ _ => .mixed targetState targetState_normalized

/-- Resident and owned auxiliary coordinates of the supplied preparation register. -/
public def spaceBudget : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then 2 else 0

/-- Execute H followed by CNOT and explicitly retain both supplied quantum systems. -/
public def algorithm : Algorithm model inputContext inputContext .unit where
  run := { code := code, output := Output.all inputContext .unit }

private lemma context_resident : inputContext.residentSpace = spaceBudget := by
  simp only [inputContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact qubitLayout.toQuantumLayout_dimensionCount dimension

private lemma context_auxiliary : inputContext.auxiliarySpace = spaceBudget := by
  simp only [inputContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact qubitLayout.toQuantumLayout_dimensionCount dimension

private lemma actual_events (path : code.Path) :
    code.resourcePool path = ResourcePool.singleton (model := model) (.gate .singleQubit) +
      ResourcePool.singleton (model := model) (.gate .cnot) := by
  change ResourcePool.ofList program.eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    Execution.unitaryOfEqualWires_cost, circuit_eventCost]

private lemma actual_resident (path : code.Path) :
    code.peakResidentSpace path ≤ spaceBudget := by
  intro axis
  change Nat.max (inputContext.residentSpace axis) 0 ≤ spaceBudget axis
  rw [context_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (path : code.Path) :
    code.peakAuxiliarySpace path ≤ spaceBudget := by
  intro axis
  change Nat.max (inputContext.auxiliarySpace axis) 0 ≤ spaceBudget axis
  rw [context_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_depth (path : code.Path) : code.depth (fun _ => 1) path ≤ 2 := by
  change circuit.evaluatedEventDepth (fun _ => 1) ≤ 2
  exact le_of_eq circuit_evaluatedEventDepth_of_one

private lemma final_quantumMarginal (environment : model.Environment) {Reference : Register}
    (supplied : Execution.OracleInput .empty inputContext Reference) :
    ((algorithm.run.finalState environment) Reference supplied.state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program.matrix environment.quantum) (1 : UnitaryOperator
          Reference))
        supplied.state.quantumMarginal := by
  exact AlgorithmRun.finalState_unitary_quantumMarginal environment program
    (Output.all inputContext .unit) Reference supplied.state

private lemma program_input (environment : model.Environment) :
    DensityOperator.applyUnitary (program.matrix environment.quantum)
        ((DensityOperator.ofPure input).reindex (S := inputContext.register) inputBasisEquiv.symm) =
      (DensityOperator.ofPure bell).reindex (S := inputContext.register) inputBasisEquiv.symm := by
  rw [program_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply]
  change (DensityOperator.ofPure ((circuit.binaryMatrix environment.quantum).apply input)).reindex
    (S := inputContext.register) inputBasisEquiv.symm = _
  rw [bellPreparation_eq]

private lemma final_observed_state (environment : model.Environment) {Reference : Register}
    (supplied : Execution.OracleInput .empty inputContext Reference)
    (admitted : valid supplied.caller.localState) :
    DensityOperator.observeSelection inputContext.quantumLayout Finset.univ Reference
      ((algorithm.run.finalState environment) Reference supplied.state).quantumMarginal
        = targetState := by
  change supplied.caller.localState.quantumMarginal =
    DensityOperator.ofPure (NormalizedVector.ket (inputBasisEquiv.symm (0 : Fin (2 ^ 2))))
    at admitted
  rw [← input_reindexed] at admitted
  rw [DensityOperator.observeSelection_all, final_quantumMarginal,
    DensityOperator.localUnitary_marginalLeft,
    ← Execution.OracleInput.oracleInput_caller_quantumMarginal supplied,
    ← Execution.Input.localState_quantumMarginal]
  rw [admitted, program_input, DensityOperator.reindex_trans]
  rfl

private lemma actual_state (environment : model.Environment) {Reference : Register}
    (supplied : Execution.OracleInput .empty inputContext Reference)
    (admitted : valid supplied.caller.localState) :
    stateRequirement.Holds supplied.caller ((algorithm.run.finalState environment) Reference
      supplied.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed targetState targetState_normalized).Holds
        (DensityOperator.observeSelection inputContext.quantumLayout Finset.univ Reference
          ((((algorithm.run.finalState environment) Reference supplied.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block,
        final_observed_state environment supplied admitted]
      change targetState.matrix = (targetState.mass : ℝ) • targetState.matrix
      rw [targetState_normalized]
      simp only [one_smul]

private lemma restores_borrowed (environment : model.Environment) {Reference : Register}
    (supplied : Execution.OracleInput .empty inputContext Reference) :
    (algorithm.run.RestoresBorrowed environment) supplied := by
  exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment rfl rfl program
    (Output.all inputContext .unit) supplied

end

end QuantumAlg.BellStatePreparation
