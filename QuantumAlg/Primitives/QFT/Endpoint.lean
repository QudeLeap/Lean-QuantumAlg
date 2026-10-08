/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Primitives.QFT.Native.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.Resources
import all QuantumAlg.Primitives.QFT.Native.Depth
import all QuantumAlg.Primitives.QFT.Native.Macros
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
# Complete native quantum Fourier transform

The input consists of one supplied owned n-qubit register. The same register
remains live in the complete Output after the exact structural Fourier circuit
acts on it. Its state target is the independently defined Fourier operator
[dW19, qcnotes.tex:1692; Lin22, phaseestimation.tex:351], tensored with the
identity on every external reference. Native gate counts come from the actual
Hadamard, controlled-phase and bit-reversal construction.
-/

namespace QuantumAlg.QuantumFourierTransform

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Exact QFT uses the default algorithm gates and requires no oracle access. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

private def qubitLayout (n : Nat) : QubitLayout n :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

private def layout (n : Nat) : QuantumLayout n := (qubitLayout n).toQuantumLayout

/-- One supplied owned register occupying physical systems zero through n minus one. -/
@[reducible] public def inputContext (n : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ (layout n) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private theorem layout_wires_eq_context (n : Nat) :
    (layout n).wires = (inputContext n).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (layout n).wires = (layout n).wires ++ []
  exact (List.append_nil _).symm

/-- Big-endian binary encoding of the same physical wire values in the owned context. -/
public def inputBasisEquiv (n : Nat) : (inputContext n).register.Index ≃ (Qubits n).Index :=
  (Execution.basisOfEqualWires (layout n) (inputContext n).quantumLayout
    (layout_wires_eq_context n)).symm.trans (qubitLayout n).binaryIndexEquiv

/-- The Fourier operator written in the owned register's explicit coordinate basis. -/
private def semanticOperator (n : Nat) : UnitaryOperator (inputContext n).register :=
  UnitaryOperator.reindex (inputBasisEquiv n).symm (QFTOperator n)

/-- The actual expanded QFT word placed on the complete supplied input context. -/
public def program (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (inputContext n).quantumLayout :=
  Execution.unitaryOfEqualWires (layout n) (inputContext n).quantumLayout
    (layout_wires_eq_context n) (Native.circuit .empty n)

/-- Source-level Hadamard, controlled-phase and SWAP occurrences describe this same native word. -/
public theorem qftProgram_macro_counts (n : Nat) :
    (program n).macroCount "hadamard" = n ∧
      (program n).macroCount "controlled-phase" = n.choose 2 ∧
      (program n).macroCount "swap" = n / 2 := by
  change (Native.circuit .empty n).macroCount "hadamard" = n ∧
    (Native.circuit .empty n).macroCount "controlled-phase" = n.choose 2 ∧
    (Native.circuit .empty n).macroCount "swap" = n / 2
  simp [Native.qftNative_circuit_macro_count]

private theorem program_matrix (n : Nat) : (program n).matrix = semanticOperator n := by
  refine (Execution.unitaryOfEqualWires_matrix (layout n)
    (inputContext n).quantumLayout (layout_wires_eq_context n)
    (Native.circuit .empty n)).trans ?_
  refine (congrArg
    (UnitaryOperator.reindex (R := (QFTPrimitive.layout n).register)
      (S := (inputContext n).register)
      (Execution.basisOfEqualWires (layout n) (inputContext n).quantumLayout
        (layout_wires_eq_context n)))
    (Native.qftNative_circuit_physicalMatrix .empty n)).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private def code (n : Nat) : Circuit model (inputContext n) (inputContext n) :=
  .unitary (program n)

/-- The exact local basis-input domain, allowing every extension by an external reference. -/
@[expose] public def valid (n : Nat) (x : Fin (2 ^ n))
    (state : ExecutionState (Execution.Store (inputContext n)) (inputContext n).register) : Prop :=
  state.quantumMarginal =
    DensityOperator.ofPure (NormalizedVector.ket ((inputBasisEquiv n).symm x))

private def targetState (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    DensityOperator (Register.prod
      ((inputContext n).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (inputContext n).quantumLayout Finset.univ Reference
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (semanticOperator n) (1 : UnitaryOperator Reference))
      input.state.quantumMarginal)

private theorem targetState_normalized (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    (targetState n Reference input).IsNormalized := by
  change (targetState n Reference input).mass = 1
  rw [targetState, DensityOperator.observeSelectionWithReference_mass,
    DensityOperator.applyUnitary_mass, ExecutionState.quantumMarginal_mass]
  exact input.normalized

private def stateRequirement (n : Nat) : StateRequirement (inputContext n) (inputContext n) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (targetState n Reference input) (targetState_normalized n Reference input)

private def spaceBudget (n : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then n else 0

/-- Independent exact QFT execution contract.

**Input.** A supplied owned n-qubit register in computational basis state x,
with every external-reference extension of that local state admitted. The
mathematical parameters n and x allocate no classical runtime cells.
**Output.** The same live register, transformed by the forward Fourier
operator with phase exp(2*pi*i/2^n). Its complete joint state with the reference
is specified by that operator tensored with the reference identity.
**Resource budget.** Exactly n+3*(n choose 2) single-qubit operations and
2*(n choose 2)+3*(n/2) CNOT operations suffice, with no Toffoli or oracle queries.
Both resident and auxiliary coordinates are bounded by n
dimension-two systems, since the supplied register has the owned role. These
bounds describe the same live systems. There are no classical bits or other
quantum dimensions. Unit-event depth is at most n+5*(n choose 2)+3*(n/2).
**Success.** The unit classical result has probability one, the independent
joint-state requirement holds, and the untouched reference is restored.
**Source.** Exact Fourier definition and circuit in [dW19, qcnotes.tex:1692]
and [Lin22, phaseestimation.tex:351]; the all-n construction theorem also
covers width zero and preserves its exact native gate counts.
-/
public def problem (n : Nat) (x : Fin (2 ^ n)) :
    Problem model (inputContext n) (inputContext n) .unit where
  valid := valid n x
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [stateRequirement n]
  resources :=
    { events := (n + 3 * n.choose 2) •
        ResourcePool.singleton (model := model) (.gate AlgorithmGate.Coordinate.singleQubit) +
        (2 * n.choose 2 + 3 * (n / 2)) •
          ResourcePool.singleton (model := model) (.gate AlgorithmGate.Coordinate.cnot)
      resident := spaceBudget n
      auxiliary := spaceBudget n }
  depth :=
    { duration := fun _ => 1
      limit := n + 5 * n.choose 2 + 3 * (n / 2)
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- Execute the placed structural QFT and explicitly retain every live input system. -/
public def algorithm (n : Nat) :
    Algorithm model (inputContext n) (inputContext n) .unit where
  run := { code := code n, output := Output.all (inputContext n) .unit }

private theorem context_resident (n : Nat) : (inputContext n).residentSpace = spaceBudget n := by
  simp only [inputContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (qubitLayout n).toQuantumLayout_dimensionCount dimension

private theorem context_auxiliary (n : Nat) : (inputContext n).auxiliarySpace = spaceBudget n := by
  simp only [inputContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (qubitLayout n).toQuantumLayout_dimensionCount dimension

private theorem actual_events (n : Nat) (path : (code n).Path) :
    (code n).resourcePool path =
      (n + 3 * n.choose 2) • ResourcePool.singleton (model := model) (.gate
        AlgorithmGate.Coordinate.singleQubit) +
        (2 * n.choose 2 + 3 * (n / 2)) •
          ResourcePool.singleton (model := model) (.gate AlgorithmGate.Coordinate.cnot) := by
  change ResourcePool.ofList (program n).eventTrace = _
  refine (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program n)).trans ?_
  refine (Execution.unitaryOfEqualWires_cost (layout n)
    (inputContext n).quantumLayout (layout_wires_eq_context n)
    (Native.circuit .empty n) .empty .empty).trans ?_
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (Native.circuit .empty n).eventCost = _
  rw [Native.qftNative_circuit_event_count]
  simp [ResourcePool.singleton, Multiset.count_singleton, eq_comm]

private theorem code_singleQubitCount (n : Nat) (path : (code n).Path) :
    ResourcePool.count (model := model) (.gate .singleQubit)
      ((code n).resourcePool path) = n + 3 * n.choose 2 := by
  rw [actual_events]
  simp [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

private theorem code_cnotCount (n : Nat) (path : (code n).Path) :
    ResourcePool.count (model := model) (.gate .cnot)
      ((code n).resourcePool path) = 2 * n.choose 2 + 3 * (n / 2) := by
  rw [actual_events]
  simp [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

private theorem code_toffoliCount (n : Nat) (path : (code n).Path) :
    ResourcePool.count (model := model) (.gate .toffoli)
      ((code n).resourcePool path) = 0 := by
  rw [actual_events]
  simp [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Exact native one-qubit count of the actual Fourier word, including controlled phases. -/
public theorem qftAlgorithm_singleQubitCount (n : Nat)
    (path : (algorithm n).run.code.Path) :
    ResourcePool.count (model := model) (.gate .singleQubit)
      ((algorithm n).run.code.resourcePool path) = n + 3 * n.choose 2 :=
  code_singleQubitCount n path

/-- The actual Fourier word's exact native CNOT count, including bit reversal. -/
public theorem qftAlgorithm_cnotCount (n : Nat)
    (path : (algorithm n).run.code.Path) :
    ResourcePool.count (model := model) (.gate .cnot)
      ((algorithm n).run.code.resourcePool path) = 2 * n.choose 2 + 3 * (n / 2) :=
  code_cnotCount n path

/-- The exact native Fourier construction uses no Toffoli gate. -/
public theorem qftAlgorithm_toffoliCount (n : Nat)
    (path : (algorithm n).run.code.Path) :
    ResourcePool.count (model := model) (.gate .toffoli)
      ((algorithm n).run.code.resourcePool path) = 0 :=
  code_toffoliCount n path

private theorem actual_resident (n : Nat) (path : (code n).Path) :
    (code n).peakResidentSpace path ≤ spaceBudget n := by
  intro axis
  change Nat.max ((inputContext n).residentSpace axis) 0 ≤ spaceBudget n axis
  rw [context_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (n : Nat) (path : (code n).Path) :
    (code n).peakAuxiliarySpace path ≤ spaceBudget n := by
  intro axis
  change Nat.max ((inputContext n).auxiliarySpace axis) 0 ≤ spaceBudget n axis
  rw [context_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_depth (n : Nat) (path : (code n).Path) :
    (code n).depth (fun _ => 1) path ≤ n + 5 * n.choose 2 + 3 * (n / 2) := by
  change (Native.circuit .empty n).evaluatedEventDepth (fun _ => 1) ≤ _
  exact le_of_eq (Native.qftNative_circuit_unit_depth .empty n)

private theorem final_quantumMarginal (n : Nat) {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext n) Reference) :
    ((algorithm n).run.finalState Reference input.state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (semanticOperator n) (1 : UnitaryOperator Reference))
        input.caller.state.quantumMarginal := by
  have actual := AlgorithmRun.finalState_unitary_quantumMarginal
    (operations := .empty) (services := .empty) (program n)
    (Output.all (inputContext n) .unit) Reference input.state
  rw [program_matrix] at actual
  exact actual.trans (congrArg
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (semanticOperator n) (1 : UnitaryOperator Reference)))
    (Execution.OracleInput.oracleInput_caller_quantumMarginal input).symm)

private theorem actual_state (n : Nat) {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext n) Reference) :
    (stateRequirement n).Holds input.caller
      ((algorithm n).run.finalState Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (targetState n Reference input.caller)
          (targetState_normalized n Reference input.caller)).Holds
        (DensityOperator.observeSelectionWithReference (inputContext n).quantumLayout
          Finset.univ Reference
          ((((algorithm n).run.finalState Reference input.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block, final_quantumMarginal]
      change (targetState n Reference input.caller).matrix =
        ((targetState n Reference input.caller).mass : ℝ) •
          (targetState n Reference input.caller).matrix
      rw [targetState_normalized]
      simp only [one_smul]

private theorem restores_borrowed (n : Nat) {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext n) Reference) :
    (algorithm n).run.RestoresBorrowed input := by
  exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed
    (operations := .empty) (services := .empty) (ctx := inputContext n)
    rfl rfl (program n) (Output.all (inputContext n) .unit) input

/-- The complete native QFT execution solves its independent Fourier-state and resource contract. -/
public theorem main (n : Nat) (x : Fin (2 ^ n)) :
    Algorithm.Solves (algorithm n) (problem n x) := by
  constructor
  · intro Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid _initialization requirement present
    have same : requirement = stateRequirement n := List.mem_singleton.mp present
    subst requirement
    exact actual_state n input
  · intro Reference input _valid _initialization
    exact restores_borrowed n input
  · intro _Reference _input _valid _initialization path _supported
    exact le_of_eq (actual_events n path)
  · intro _Reference _input _valid _initialization path _supported
    exact actual_resident n path
  · intro _Reference _input _valid _initialization path _supported
    exact actual_auxiliary n path
  · intro _Reference _input _valid _initialization path _supported
    exact actual_depth n path

end

end QuantumAlg.QuantumFourierTransform
