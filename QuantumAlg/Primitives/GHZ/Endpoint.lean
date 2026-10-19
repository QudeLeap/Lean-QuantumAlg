/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.GHZ.Endpoint.Execution
import all QuantumAlg.Primitives.GHZ.Endpoint.Execution

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Primitives.GHZ.Construction
import all QuantumAlg.Primitives.GHZ.Construction
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
# Complete native GHZ preparation from supplied zero input qubits

One supplied owned three-qubit register starts in state `|000>`. The original
Hadamard and CNOT cascade produces the independently defined GHZ pure state
`(|000>+|111>)/sqrt(2)`. All three physical systems remain live in the complete
Output. Input preparation is outside this supplied-input contract; the code
executes no fresh quantum allocation or preparation instruction.

The normalized three-qubit form is one block of the displayed Shor-code
zero codeword [dW19, qcnotes.tex:7454-7459]. This supports the target state;
the actual preparation cascade and resource counts are proved here.
Nielsen and Chuang give standard textbook background. The original 1989
Greenberger-Horne-Zeilinger argument uses four particles and provides
historical attribution, not this three-qubit circuit.
-/

namespace QuantumAlg.GHZStatePreparation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent complete three-qubit GHZ preparation contract.

**Input.** Three supplied owned qubits in the pure state |000>, admitting every
normalized extension by an external reference. No runtime classical cells or
fresh quantum preparation are part of this supplied-input execution.
**Output.** All three original physical systems remain live and jointly have
the pure GHZ state (|000>+|111>)/sqrt(2). The independent target is its pure
density matrix in the exact output coordinates. The classical result is unit.
**Resource budget.** One Hadamard and two CNOT events suffice, with unit-event
depth at most three. Both resident and auxiliary coordinates are bounded by
three dimension-two systems, since the supplied input has the owned role.
These are the same live systems, with zero classical bits and no other dimensions.
**Success.** Probability one, with the exact GHZ-state requirement and
mandatory restoration of the complete untouched external reference.
**Source.** The three-qubit target is the normalized block appearing in
[dW19, qcnotes.tex:7454-7459]. This source supports the state form, while the
precise cascade and counts follow from the library's matrix and circuit proofs.
Nielsen and Chuang provide textbook background; the 1989 Greenberger-Horne-
Zeilinger four-particle argument supplies distinct historical attribution.
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
        2 • ResourcePool.singleton (model := model) (.gate .cnot)
      resident := spaceBudget
      auxiliary := spaceBudget }
  quantumTimeLimit := 3

/-- The actual complete execution prepares the independent GHZ state within its native bounds. -/
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

end QuantumAlg.GHZStatePreparation
