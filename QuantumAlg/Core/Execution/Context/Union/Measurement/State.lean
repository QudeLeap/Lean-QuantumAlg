/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.State
import all QuantumAlg.Core.Execution.Context.Union.Measurement.Store
import all QuantumAlg.Core.Execution.State.Coordinate.Measurement

/-!
# Full state correctness of an actual framed Z measurement

The actual wire is measured, its result is written to the actual classical
cell, and that same outcome is recorded in the execution history. Exact
coordinates preserve all classical frame blocks and all quantum/reference
matrix entries, including correlated and zero-probability inputs
[dW19, qcnotes.tex:5409,5420].
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (left right : RuntimeCtx .quantum)
  (separate : RuntimeCtx.StorageDisjoint left right)
  {Reference : Register} {History : Type} [Fintype History]

/-- Actual framed Z execution and local execution agree on the complete state. -/
theorem contextUnion_splitState_measureZ
    (state : State (left.disjointUnion right separate) Reference History)
    (wire : Fin left.systemCount)
    (output : CWriteRef left (.finite (left.quantumLayout.wire wire).dimension)) :
    splitState left right separate
        (state.measureZ (leftPosition left right separate wire)
          (measurementLeft separate wire output)) =
      ((splitState left right separate state).measureZ wire output).mapHistory
        (fun value => (value.1.1, (value.1.2,
          Fin.cast (congrArg (fun dimension : ℕ+ => (dimension : Nat))
            (contextUnion_left_dimension left right separate wire).symm) value.2))) := by
  let outcomeEquiv := finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
    (contextUnion_left_dimension left right separate wire))
  let labels := recordEquiv left right separate History
  let basis := referenceBasis left right separate Reference
  let original := fun value :
      (Register.prod (left.disjointUnion right separate).register Reference).Index =>
        value.1 (leftPosition left right separate wire)
  let transported := fun value :
      (Register.prod left.register (Register.prod right.register Reference)).Index =>
        value.1 wire
  have reads : ∀ value, outcomeEquiv (original value) = transported (basis value) := by
    intro value
    exact contextUnion_split_left left right separate value.1 wire
  have measured := ExecutionState.coordinate_measureZ state basis labels outcomeEquiv
    original transported reads
  let localWrite :
      ((Store left × (Store right × History)) ×
        Fin (left.quantumLayout.wire wire).dimension) →
      Store left × (Store right × (History ×
        Fin ((left.disjointUnion right separate).quantumLayout.wire
          (leftPosition left right separate wire)).dimension)) := fun value =>
    (value.1.1.write output (.finite value.2),
      (value.1.2.1, (value.1.2.2, outcomeEquiv.symm value.2)))
  have diagram :
      (fun value : ((Store (left.disjointUnion right separate) × History) ×
          Fin ((left.disjointUnion right separate).quantumLayout.wire
            (leftPosition left right separate wire)).dimension) =>
        recordEquiv left right separate
          (History × Fin ((left.disjointUnion right separate).quantumLayout.wire
            (leftPosition left right separate wire)).dimension)
          (value.1.1.write (measurementLeft separate wire output) (.finite value.2),
            (value.1.2, value.2))) =
        localWrite ∘ (labels.prodCongr outcomeEquiv) := by
    funext value
    have writes := contextUnion_measurementLeft_split_write separate value.1.1 wire output
      value.2
    change ((split separate
        (value.1.1.write (measurementLeft separate wire output) (.finite value.2))).1,
      ((split separate
        (value.1.1.write (measurementLeft separate wire output) (.finite value.2))).2,
        (value.1.2, value.2))) = _
    rw [writes]
    change _ = ((split separate value.1.1).1.write output (.finite (outcomeEquiv value.2)),
      ((split separate value.1.1).2, (value.1.2, outcomeEquiv.symm (outcomeEquiv value.2))))
    rw [Equiv.symm_apply_apply]
    rfl
  have writes := ExecutionState.coordinate_transport_diagram
    (ExecutionState.measureZ state original) basis (labels.prodCongr outcomeEquiv)
    (recordEquiv left right separate
      (History × Fin ((left.disjointUnion right separate).quantumLayout.wire
        (leftPosition left right separate wire)).dimension))
    (fun value => (value.1.1.write (measurementLeft separate wire output) (.finite value.2),
      (value.1.2, value.2))) localWrite (congrFun diagram)
  have steps := congrArg (fun originalState => originalState.mapClassical localWrite) measured
  have histories := ExecutionState.executionState_mapClassical_comp
    (ExecutionState.measureZ (splitState left right separate state)
      (fun value => value.1 wire))
    (fun value => (value.1.1.write output (.finite value.2), (value.1.2, value.2)))
    (fun value => (value.1, (value.2.1.1, (value.2.1.2, outcomeEquiv.symm value.2.2))))
  convert writes.trans (steps.trans histories.symm) using 1 <;>
    dsimp only [splitState, State.measureZ, State.mapHistory, basis, original, outcomeEquiv] <;>
    congr! 2

end

end QuantumAlg.Execution.ContextUnion
