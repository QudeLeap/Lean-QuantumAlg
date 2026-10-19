/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.BellPair.Endpoint.Execution
import all QuantumAlg.Primitives.BellPair.Endpoint.Execution

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
@[expose] public def problem : Problem model inputContext inputContext .unit where
  Witness := Unit
  valid := fun _ _ => valid
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [stateRequirement]
  resources :=
    { events := ResourcePool.singleton (model := model) (.gate .singleQubit) +
        ResourcePool.singleton (model := model) (.gate .cnot)
      resident := spaceBudget
      auxiliary := spaceBudget }
  quantumTimeLimit := 2

/-- The actual complete execution prepares the independent Bell state within its native bounds. -/
public theorem main :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate problem := by
  refine ⟨algorithm, ?_⟩
  constructor
  · intro environment _witness Reference supplied _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference supplied admitted _initialized requirement present
    have same : requirement = stateRequirement := List.mem_singleton.mp present
    subst requirement
    exact actual_state environment supplied admitted
  · intro environment _witness Reference supplied _valid _initialized
    exact restores_borrowed environment supplied
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    exact le_of_eq (actual_events path)
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    exact actual_resident path
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    exact actual_auxiliary path
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact actual_depth path

end

end QuantumAlg.BellStatePreparation
