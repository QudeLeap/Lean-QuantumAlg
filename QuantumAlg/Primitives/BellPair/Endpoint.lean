/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Components.Gates
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

private def layout : QuantumLayout 2 := qubitLayout.toQuantumLayout

/-- One supplied owned two-qubit register occupying physical systems zero and one. -/
@[reducible] public def inputContext : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ layout (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private theorem layout_wires_eq_context :
    layout.wires = inputContext.quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change layout.wires = layout.wires ++ []
  exact (List.append_nil _).symm

/-- Big-endian binary encoding of the exact two physical wire values. -/
public def inputBasisEquiv : inputContext.register.Index ≃ (Qubits 2).Index :=
  (Execution.basisOfEqualWires layout inputContext.quantumLayout
    layout_wires_eq_context).symm.trans qubitLayout.binaryIndexEquiv

private theorem context_physicalIdx : inputContext.physicalIdx = [0, 1] := by
  change ((layout.wires ++ []).map QuantumWire.identity) = [0, 1]
  rfl

private def program : UnitaryCircuit inputContext.register :=
  UnitaryCircuit.reindex inputBasisEquiv.symm circuit

private theorem placement : program.physical_idx = inputContext.physicalIdx := by
  rw [context_physicalIdx]
  rfl

private def code : Circuit inputContext inputContext :=
  .unitary program placement

/-- The supplied local state is exactly the pure zero input,
with every reference extension allowed. -/
@[expose] public def valid
    (state : ExecutionState (Execution.Store inputContext) inputContext.register) : Prop :=
  state.quantumMarginal =
    DensityOperator.ofPure (NormalizedVector.ket (inputBasisEquiv.symm (0 : Fin (2 ^ 2))))

private theorem input_reindexed :
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

private theorem targetState_normalized : targetState.IsNormalized := by
  change targetState.mass = 1
  rw [targetState, DensityOperator.reindex_mass]
  exact DensityOperator.ofPure_normalized bell

private def stateRequirement : StateRequirement inputContext inputContext :=
  .marginal Finset.univ .unit fun _ _ => .mixed targetState targetState_normalized

private def spaceBudget : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then 2 else 0

/-- Independent complete Bell-state preparation contract.

**Input.** Two supplied owned qubits in the pure state |00>, admitting every
normalized extension by an external reference. No runtime classical cells or
fresh quantum preparation are part of this supplied-input execution.
**Output.** Both original physical systems remain live and jointly have the
pure Bell state (|00>+|11>)/sqrt(2). The target is its independently defined
pure density matrix in the exact output coordinates. The classical result is unit.
**Resource budget.** One Hadamard and one CNOT event suffice, with unit-event
depth at most two. Both resident and auxiliary coordinates are bounded by two
dimension-two systems, since the supplied input has the owned role. These are
the same live systems, with zero classical bits and no other quantum dimensions.
**Success.** Probability one, with the exact Bell-state requirement and
mandatory restoration of the complete untouched external reference.
**Source.** The Bell vector and gate actions in [dW19, qcnotes.tex:622,711,741];
the two-gate preparation is the prefix before the final Z in the circuit
example [dW19, qcnotes.tex:1036].
-/
public def problem : Problem .quantum inputContext inputContext .unit where
  valid := valid
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [stateRequirement]
  resources :=
    { events := ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.gate (.builtin "cnot"))
      resident := spaceBudget
      auxiliary := spaceBudget }
  depth := .quantum (fun _ => 1) 2

/-- Execute H followed by CNOT and explicitly retain both supplied quantum systems. -/
public def algorithm : Algorithm .quantum inputContext inputContext .unit where
  run := { code := code, output := Output.all inputContext .unit }

private theorem context_resident : inputContext.residentSpace = spaceBudget := by
  simp only [inputContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact qubitLayout.toQuantumLayout_dimensionCount dimension

private theorem context_auxiliary : inputContext.auxiliarySpace = spaceBudget := by
  simp only [inputContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact qubitLayout.toQuantumLayout_dimensionCount dimension

private theorem actual_events (path : code.Path) :
    code.resourcePool path = ResourcePool.singleton (.gate (.builtin "hadamard")) +
      ResourcePool.singleton (.gate (.builtin "cnot")) := by
  change ResourcePool.ofList program.eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    UnitaryCircuit.reindex_eventCost, circuit_eventCost, Gate.atomicEvent, Gate.atomicEvent]

private theorem actual_resident (path : code.Path) :
    code.peakResidentSpace path ≤ spaceBudget := by
  intro axis
  change Nat.max (inputContext.residentSpace axis) 0 ≤ spaceBudget axis
  rw [context_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (path : code.Path) :
    code.peakAuxiliarySpace path ≤ spaceBudget := by
  intro axis
  change Nat.max (inputContext.auxiliarySpace axis) 0 ≤ spaceBudget axis
  rw [context_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_depth (path : code.Path) : code.depth (fun _ => 1) path ≤ 2 := by
  change circuit.evaluatedEventDepth (fun _ => 1) ≤ 2
  exact le_of_eq circuit_evaluatedEventDepth_of_one

private theorem final_quantumMarginal {Reference : Register}
    (supplied : Execution.Input inputContext Reference) :
    (algorithm.run.finalState Reference supplied.state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
        supplied.state.quantumMarginal := by
  exact AlgorithmRun.finalState_unitary_quantumMarginal program placement
    (Output.all inputContext .unit) Reference supplied.state

private theorem program_input :
    DensityOperator.applyUnitary program.matrix
        ((DensityOperator.ofPure input).reindex (S := inputContext.register) inputBasisEquiv.symm) =
      (DensityOperator.ofPure bell).reindex (S := inputContext.register) inputBasisEquiv.symm := by
  rw [program, UnitaryCircuit.reindex_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply]
  change (DensityOperator.ofPure (circuit.applyNormalized input)).reindex
    (S := inputContext.register) inputBasisEquiv.symm = _
  rw [bellPreparation_eq]

private theorem final_observed_state {Reference : Register}
    (supplied : Execution.Input inputContext Reference) (admitted : valid supplied.localState) :
    DensityOperator.observeSelection inputContext.quantumLayout Finset.univ Reference
      (algorithm.run.finalState Reference supplied.state).quantumMarginal = targetState := by
  change supplied.localState.quantumMarginal =
    DensityOperator.ofPure (NormalizedVector.ket (inputBasisEquiv.symm (0 : Fin (2 ^ 2))))
    at admitted
  rw [← input_reindexed] at admitted
  rw [DensityOperator.observeSelection_all, final_quantumMarginal,
    DensityOperator.localUnitary_marginalLeft, ← Execution.Input.localState_quantumMarginal]
  rw [admitted, program_input, DensityOperator.reindex_trans]
  rfl

private theorem actual_state {Reference : Register}
    (supplied : Execution.Input inputContext Reference) (admitted : valid supplied.localState) :
    stateRequirement.Holds supplied (algorithm.run.finalState Reference supplied.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed targetState targetState_normalized).Holds
        (DensityOperator.observeSelection inputContext.quantumLayout Finset.univ Reference
          (((algorithm.run.finalState Reference supplied.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block,
        final_observed_state supplied admitted]
      change targetState.matrix = (targetState.mass : ℝ) • targetState.matrix
      rw [targetState_normalized]
      simp only [one_smul]

private theorem restores_borrowed {Reference : Register}
    (supplied : Execution.Input inputContext Reference) :
    algorithm.run.RestoresBorrowed supplied := by
  exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl program placement
    (supplied.state.mapClassical fun store => (store, store))

/-- The actual complete execution prepares the independent Bell state within its native bounds. -/
public theorem main : ∃ candidate, Algorithm.Solves candidate problem := by
  refine ⟨algorithm, ?_⟩
  constructor
  · intro Reference supplied _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference supplied admitted requirement present
    have same : requirement = stateRequirement := List.mem_singleton.mp present
    subst requirement
    exact actual_state supplied admitted
  · intro Reference supplied _valid
    exact restores_borrowed supplied
  · intro _Reference _supplied _valid path _supported
    exact le_of_eq (actual_events path)
  · intro _Reference _supplied _valid path _supported
    exact actual_resident path
  · intro _Reference _supplied _valid path _supported
    exact actual_auxiliary path
  · intro _Reference _supplied _valid path _supported
    exact actual_depth path

end

end QuantumAlg.BellStatePreparation
