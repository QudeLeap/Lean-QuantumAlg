/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Z measurement writes and classical gate selection

These mathematical state updates connect the computational-basis result of an
actual wire to a writable finite classical register. A later conditional step
reads that register through its typed reference and applies the selected
unitary operator. Measurement retains the full quantum register, including all
unmeasured systems and their correlations.

The state updates implement the projective measurement rule
[dW19, qcnotes.tex:5409]. Native events and placement checks belong to the
instruction syntax that supplies these steps.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {systemCount : Nat} {layout : QuantumLayout systemCount}
  {ctx : RuntimeCtx .quantum}

local instance : DecidableEq (Store ctx) := Classical.decEq _

/-- Measure one actual wire in its computational basis and write the result
to the named classical register. No quantum wire is released. -/
def writeZ (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension)) :
    ExecutionState (Store ctx) layout.register :=
  (state.measureZ fun basis => basis wire).mapClassical fun result =>
    result.1.write output (.finite result.2)

/-- Measurement and its classical write preserve total probability mass. -/
theorem writeZ_mass (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension)) :
    (writeZ state wire output).mass = state.mass := by
  simp only [writeZ, ExecutionState.mapClassical_mass, ExecutionState.measureZ_mass]

/-- A classical conditional reads an existing finite register and executes
the corresponding unitary operator. It preserves the stored classical value. -/
def conditional (state : ExecutionState (Store ctx) layout.register)
    {cardinality : ℕ+} (input : CInputRef ctx (.finite cardinality))
    (branch : Fin cardinality → UnitaryOperator layout.register) :
    ExecutionState (Store ctx) layout.register :=
  state.applyUnitary fun store => (branch (store.read input).toFin)

/-- The selected gate acts on the quantum block associated with the actual
stored value, without resampling a result or evaluating an unselected gate. -/
theorem conditional_block (state : ExecutionState (Store ctx) layout.register)
    {cardinality : ℕ+} (input : CInputRef ctx (.finite cardinality))
    (branch : Fin cardinality → UnitaryOperator layout.register) (store : Store ctx) :
    (conditional state input branch).block store =
      DensityOperator.applyUnitary (branch (store.read input).toFin)
        (state.block store) := rfl

/-- A classical conditional preserves the probability of every stored value. -/
theorem conditional_block_mass (state : ExecutionState (Store ctx) layout.register)
    {cardinality : ℕ+} (input : CInputRef ctx (.finite cardinality))
    (branch : Fin cardinality → UnitaryOperator layout.register) (store : Store ctx) :
    ((conditional state input branch).block store).mass = (state.block store).mass := by
  simp only [conditional_block, DensityOperator.applyUnitary_mass]

/-- Conditional unitary execution preserves total probability mass. -/
theorem conditional_mass (state : ExecutionState (Store ctx) layout.register)
    {cardinality : ℕ+} (input : CInputRef ctx (.finite cardinality))
    (branch : Fin cardinality → UnitaryOperator layout.register) :
    (conditional state input branch).mass = state.mass :=
  ExecutionState.applyUnitary_mass state _

/-- The gate selected by a later read is exactly the gate indexed by the
measurement result written into this register. -/
theorem selected_after_write {cardinality : ℕ+} (store : Store ctx)
    (output : CWriteRef ctx (.finite cardinality)) (outcome : Fin cardinality)
    (branch : Fin cardinality → UnitaryOperator layout.register) :
    branch ((store.write output (.finite outcome)).read
      (.storage output.toCStorageRef)).toFin = branch outcome := by
  rw [Store.read_write_same]
  rfl

/-- Measuring, writing, and then reading to select a gate has the exact joint
state obtained by applying the outcome's gate to each measurement branch and
storing that outcome. The equality includes the complete quantum register. -/
theorem conditional_writeZ (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension))
    (branch : Fin (layout.wire wire).dimension → UnitaryOperator layout.register) :
    conditional (writeZ state wire output) (.storage output.toCStorageRef) branch =
      ((state.measureZ fun basis => basis wire).applyUnitary fun result =>
        (branch result.2)).mapClassical fun result =>
          result.1.write output (.finite result.2) := by
  unfold conditional writeZ
  rw [ExecutionState.applyUnitary_mapClassical]
  simp only [Store.read_write_same, CShape.Value.toFin_finite]

end

end QuantumAlg.Execution
