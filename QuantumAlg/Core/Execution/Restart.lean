/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Borrowed.State
public import QuantumAlg.Core.Execution.Borrowed
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Observe
public import QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.State.Promise

/-!
# Physical restart of the complete owned output

An actual restart measures, restores the full borrowed interface, and prepares
one fixed owned-state seed on every record, retaining arbitrary references.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A caller-selected physical basis label for the owned output is prepared
in every complete record, including zero-mass records and arbitrary reference. -/
public def ReinitializedAt {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool} (code : Circuit model pre post
      allowAllocation) (environment : model.Environment)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ) : Prop :=
  ∀ (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State pre Reference (model.HiddenState × H))
    (label : Execution.Store post × (model.HiddenState × (H × code.Path))),
  (StatePromise.pure (NormalizedVector.ket seed)).Holds
    (DensityOperator.observeSelection post.quantumLayout
      post.borrowedSelectionᶜ Reference ((code.execute environment Reference state).block label))

/-- Physical cleanup leaves every owned system in one fixed, predetermined basis state,
even after conditioning on the complete store, hidden service state and path.
The seed is chosen before every input, reference, history and execution label;
it may describe zero reset or a fixed re-preparation, but cannot depend on an outcome.
This certificate states physical restoration only; it does not split the
execution's resource or quantum computation time obligations. -/
public structure RestartCleanup {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool} (code : Circuit model pre post
      allowAllocation) (environment : model.Environment) where
  /-- Every actual path includes a quantum measurement. -/
  measured : ∀ path : code.Path, ∃ measuredDimension : model.SystemDimension,
    Resource.Event.measurement measuredDimension ∈ code.eventTrace path
  /-- The actual borrowed interface is restored for every input and external
  reference, independently of the protocol's input predicate. -/
  restores : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : Execution.State pre Reference (model.HiddenState × H)),
    code.BorrowedRestored Reference state (code.execute environment Reference state)
  /-- One fixed seed reinitializes every owned output wire on every actual record,
  with arbitrary borrowed and external-reference correlations retained in the final state. -/
  reinitialized : ∃ seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ,
    ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : Execution.State pre Reference (model.HiddenState × H))
      (label : Execution.Store post × (model.HiddenState × (H × code.Path))),
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection post.quantumLayout
        post.borrowedSelectionᶜ Reference
        ((code.execute environment Reference state).block label))

end

end QuantumAlg.Circuit
