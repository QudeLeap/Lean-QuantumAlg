/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Core.Algorithm.AlgorithmRun
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

private theorem context_physicalIdx (n : Nat) :
    (inputContext n).physicalIdx = List.range n := by
  change ((layout n).wires ++ []).map QuantumWire.identity = List.range n
  simp only [List.append_nil, QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun index : Fin n => index.val) = List.range n
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

/-- The Fourier operator written in the owned register's explicit coordinate basis. -/
private def semanticOperator (n : Nat) : UnitaryOperator (inputContext n).register :=
  UnitaryOperator.reindex (inputBasisEquiv n).symm (QFTOperator n)

private def program (n : Nat) : UnitaryCircuit (inputContext n).register :=
  UnitaryCircuit.reindex (inputBasisEquiv n).symm (QFTCircuit n)

private theorem program_matrix (n : Nat) : (program n).matrix = semanticOperator n := by
  simp only [program, UnitaryCircuit.reindex_matrix, QFTCircuit_matrix, semanticOperator]

private theorem placement (n : Nat) : (program n).physical_idx = (inputContext n).physicalIdx := by
  change (QFTCircuit n).physical_idx = (inputContext n).physicalIdx
  rw [QFTCircuit_physical_idx, context_physicalIdx]

private def code (n : Nat) : Circuit (inputContext n) (inputContext n) :=
  .unitary (program n) (placement n)

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
**Resource budget.** Exactly n Hadamard, n choose 2 controlled-phase and n/2
SWAP events suffice. Both resident and auxiliary coordinates are bounded by n
dimension-two systems, since the supplied register has the owned role. These
bounds describe the same live systems. There are no classical bits or other
quantum dimensions. Unit-event depth is at most n+n*(n-1)/2+n/2.
**Success.** The unit classical result has probability one, the independent
joint-state requirement holds, and the untouched reference is restored.
**Source.** Exact Fourier definition and circuit in [dW19, qcnotes.tex:1692]
and [Lin22, phaseestimation.tex:351]; the all-n construction theorem also
covers width zero and preserves its exact native gate counts.
-/
public def problem (n : Nat) (x : Fin (2 ^ n)) :
    Problem .quantum (inputContext n) (inputContext n) .unit where
  valid := valid n x
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [stateRequirement n]
  resources :=
    { events := n • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        n.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
          (n / 2) • ResourcePool.singleton (.gate (.builtin "swap"))
      resident := spaceBudget n
      auxiliary := spaceBudget n }
  depth := .quantum (fun _ => 1) (n + n * (n - 1) / 2 + n / 2)

/-- Execute the placed structural QFT and explicitly retain every live input system. -/
public def algorithm (n : Nat) :
    Algorithm .quantum (inputContext n) (inputContext n) .unit where
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
    (code n).resourcePool path = n • ResourcePool.singleton (.gate (.builtin "hadamard")) +
      n.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
        (n / 2) • ResourcePool.singleton (.gate (.builtin "swap")) := by
  change ResourcePool.ofList (program n).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    UnitaryCircuit.reindex_eventCost, QFTCircuit_eventCost_eq]

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
    (code n).depth (fun _ => 1) path ≤ n + n * (n - 1) / 2 + n / 2 := by
  change (QFTCircuit n).evaluatedEventDepth (fun _ => 1) ≤ _
  exact le_of_eq (QFTCircuit_evaluatedEventDepth_of_one n)

private theorem final_quantumMarginal (n : Nat) {Reference : Register}
    (input : Execution.Input (inputContext n) Reference) :
    ((algorithm n).run.finalState Reference input.state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (semanticOperator n) (1 : UnitaryOperator Reference))
        input.state.quantumMarginal := by
  have actual := AlgorithmRun.finalState_unitary_quantumMarginal (program n) (placement n)
    (Output.all (inputContext n) .unit) Reference input.state
  rw [program_matrix] at actual
  exact actual

private theorem actual_state (n : Nat) {Reference : Register}
    (input : Execution.Input (inputContext n) Reference) :
    (stateRequirement n).Holds input ((algorithm n).run.finalState Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (targetState n Reference input)
          (targetState_normalized n Reference input)).Holds
        (DensityOperator.observeSelectionWithReference (inputContext n).quantumLayout
          Finset.univ Reference
          ((((algorithm n).run.finalState Reference input.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block, final_quantumMarginal]
      change (targetState n Reference input).matrix =
        ((targetState n Reference input).mass : ℝ) • (targetState n Reference input).matrix
      rw [targetState_normalized]
      simp only [one_smul]

private theorem restores_borrowed (n : Nat) {Reference : Register}
    (input : Execution.Input (inputContext n) Reference) :
    (algorithm n).run.RestoresBorrowed input := by
  exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl (program n) (placement n)
    (input.state.mapClassical fun store => (store, store))

/-- The complete native QFT execution solves its independent Fourier-state and resource contract. -/
public theorem main (n : Nat) (x : Fin (2 ^ n)) :
    ∃ candidate, Algorithm.Solves candidate (problem n x) := by
  refine ⟨algorithm n, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = stateRequirement n := List.mem_singleton.mp present
    subst requirement
    exact actual_state n input
  · intro Reference input _valid
    exact restores_borrowed n input
  · intro _Reference _input _valid path _supported
    exact le_of_eq (actual_events n path)
  · intro _Reference _input _valid path _supported
    exact actual_resident n path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary n path
  · intro _Reference _input _valid path _supported
    exact actual_depth n path

end

end QuantumAlg.QuantumFourierTransform
