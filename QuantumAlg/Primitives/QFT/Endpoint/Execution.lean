/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Endpoint.Specification
import all QuantumAlg.Primitives.QFT.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Components.GateModel.Fourier
import all QuantumAlg.Primitives.QFT.Source.FourierMatrix
import all QuantumAlg.Primitives.QFT.Source.Resources
import all QuantumAlg.Primitives.QFT.Source.Depth
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Core.Algorithm.Unitary.Laws
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Trace

/-!
# Native Fourier execution and complete supporting proofs

The same source circuit is placed on the supplied register and retains the
complete live Output. Its matrix, exact event counts, state transformation,
restoration, and space/time proofs connect that execution to the independent
Fourier specification. The lowered native construction remains separately
connected to the same source by the QFT lowering theorems.
-/

namespace QuantumAlg.QuantumFourierTransform

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The canonical source QFT circuit placed on the complete supplied input context. -/
public def program (n : Nat) :
    UnitaryCircuit FourierGate.model .empty (inputContext n).quantumLayout :=
  Execution.unitaryOfEqualWires (layout n) (inputContext n).quantumLayout
    (layout_wires_eq_context n) (Source.circuit .empty n)

/-- Native source counts measured directly on the execution program. -/
public lemma qftProgram_native_counts (n : Nat) :
    ResourcePool.count (model := model) (.gate .hadamard) (program n).eventCost = n ∧
      ResourcePool.count (model := model) (.gate .controlledPhase)
        (program n).eventCost = n.choose 2 ∧
      ResourcePool.count (model := model) (.gate .swap) (program n).eventCost = n / 2 := by
  have events : (program n).eventCost = (Source.circuit .empty n).eventCost :=
    Execution.unitaryOfEqualWires_cost (layout n)
      (inputContext n).quantumLayout (layout_wires_eq_context n)
      (Source.circuit .empty n) .empty .empty
  rw [events]
  simp [Source.qftSource_circuit_event_count]

private lemma program_matrix (n : Nat) (environment : OracleModel.empty.Interpretation) :
    (program n).matrix environment = semanticOperator n := by
  refine (Execution.unitaryOfEqualWires_matrix (layout n)
    (inputContext n).quantumLayout (layout_wires_eq_context n) environment
    (Source.circuit .empty n)).trans ?_
  refine (congrArg
    (UnitaryOperator.reindex (R := (QFTPrimitive.layout n).register)
      (S := (inputContext n).register)
      (Execution.basisOfEqualWires (layout n) (inputContext n).quantumLayout
        (layout_wires_eq_context n)))
    (Source.qftSource_circuit_physicalMatrix .empty n environment)).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private def code (n : Nat) : Circuit model (inputContext n) (inputContext n) :=
  .unitary (program n)

/-- Execute the placed structural QFT and explicitly retain every live input system. -/
public def algorithm (n : Nat) :
    Algorithm model (inputContext n) (inputContext n) .unit where
  run := { code := code n, output := Output.all (inputContext n) .unit }

private lemma context_resident (n : Nat) : (inputContext n).residentSpace = spaceBudget n := by
  simp only [inputContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (qubitLayout n).toQuantumLayout_dimensionCount dimension

private lemma context_auxiliary (n : Nat) : (inputContext n).auxiliarySpace = spaceBudget n := by
  simp only [inputContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (qubitLayout n).toQuantumLayout_dimensionCount dimension

private lemma actual_events (n : Nat) (path : (code n).Path) :
    (code n).resourcePool path =
      n • ResourcePool.singleton (model := model) (.gate FourierGate.Coordinate.hadamard) +
        (n.choose 2) • ResourcePool.singleton (model := model)
          (.gate FourierGate.Coordinate.controlledPhase) +
        (n / 2) • ResourcePool.singleton (model := model) (.gate FourierGate.Coordinate.swap) := by
  change ResourcePool.ofList (program n).eventTrace = _
  refine (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program n)).trans ?_
  refine (Execution.unitaryOfEqualWires_cost (layout n)
    (inputContext n).quantumLayout (layout_wires_eq_context n)
    (Source.circuit .empty n) .empty .empty).trans ?_
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (Source.circuit .empty n).eventCost = _
  rw [Source.qftSource_circuit_event_count]
  simp [ResourcePool.singleton, Multiset.count_singleton, eq_comm]

/-- Exact actual native Hadamard count of the canonical Fourier algorithm. -/
public lemma qftAlgorithm_hadamardCount (n : Nat)
    (path : (algorithm n).run.code.Path) :
    ResourcePool.count (model := model) (.gate .hadamard)
      ((algorithm n).run.code.resourcePool path) = n := by
  change (code n).Path at path
  change ResourcePool.count (model := model) (.gate .hadamard) ((code n).resourcePool path) = n
  rw [actual_events]
  simp

/-- Exact actual native controlled-phase count of the canonical Fourier algorithm. -/
public lemma qftAlgorithm_controlledPhaseCount (n : Nat)
    (path : (algorithm n).run.code.Path) :
    ResourcePool.count (model := model) (.gate .controlledPhase)
      ((algorithm n).run.code.resourcePool path) = n.choose 2 := by
  change (code n).Path at path
  change ResourcePool.count (model := model) (.gate .controlledPhase)
    ((code n).resourcePool path) = n.choose 2
  rw [actual_events]
  simp

/-- Exact actual native SWAP count, including final bit reversal. -/
public lemma qftAlgorithm_swapCount (n : Nat)
    (path : (algorithm n).run.code.Path) :
    ResourcePool.count (model := model) (.gate .swap)
      ((algorithm n).run.code.resourcePool path) = n / 2 := by
  change (code n).Path at path
  change ResourcePool.count (model := model) (.gate .swap) ((code n).resourcePool path) = n / 2
  rw [actual_events]
  simp

private lemma actual_resident (n : Nat) (path : (code n).Path) :
    (code n).peakResidentSpace path ≤ spaceBudget n := by
  intro axis
  change Nat.max ((inputContext n).residentSpace axis) 0 ≤ spaceBudget n axis
  rw [context_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (n : Nat) (path : (code n).Path) :
    (code n).peakAuxiliarySpace path ≤ spaceBudget n := by
  intro axis
  change Nat.max ((inputContext n).auxiliarySpace axis) 0 ≤ spaceBudget n axis
  rw [context_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_depth (n : Nat) (path : (code n).Path) :
    (code n).depth (fun _ => 1) path ≤ n + n.choose 2 + n / 2 := by
  change (Source.circuit .empty n).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [Source.qftSource_circuit_unit_depth]
  split_ifs <;> omega

private lemma final_quantumMarginal (n : Nat) (environment : model.Environment) {Reference :
  Register}
    (input : Execution.OracleInput .empty (inputContext n) Reference) :
    ((algorithm n).run.finalState environment Reference input.state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (semanticOperator n) (1 : UnitaryOperator Reference))
        input.caller.state.quantumMarginal := by
  have actual := AlgorithmRun.finalState_unitary_quantumMarginal
    (operations := .empty) (services := .empty) environment (program n)
    (Output.all (inputContext n) .unit) Reference input.state
  rw [program_matrix] at actual
  exact actual.trans (congrArg
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (semanticOperator n) (1 : UnitaryOperator Reference)))
    (Execution.OracleInput.oracleInput_caller_quantumMarginal input).symm)

private lemma actual_state (n : Nat) (environment : model.Environment) {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext n) Reference) :
    (stateRequirement n).Holds input.caller
      ((algorithm n).run.finalState environment Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (targetState n Reference input.caller)
          (targetState_normalized n Reference input.caller)).Holds
        (DensityOperator.observeSelectionWithReference (inputContext n).quantumLayout
          Finset.univ Reference
          ((((algorithm n).run.finalState environment Reference input.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block, final_quantumMarginal]
      change (targetState n Reference input.caller).matrix =
        ((targetState n Reference input.caller).mass : ℝ) •
          (targetState n Reference input.caller).matrix
      rw [targetState_normalized]
      simp only [one_smul]

private lemma restores_borrowed (n : Nat) (environment : model.Environment) {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext n) Reference) :
    (algorithm n).run.RestoresBorrowed environment input := by
  exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed
    (operations := .empty) (services := .empty) (ctx := inputContext n)
    environment rfl rfl (program n) (Output.all (inputContext n) .unit) input

end

end QuantumAlg.QuantumFourierTransform
