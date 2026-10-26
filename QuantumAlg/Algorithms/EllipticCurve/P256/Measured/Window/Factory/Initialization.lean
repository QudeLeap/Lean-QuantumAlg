/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.RetainedTables
import all QuantumAlg.Core.Execution.Classical.Retained.Support

/-! # Initialization supplied by the actual P-256 retained table allocation -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

open QuantumAlg.Execution QuantumAlg.ClassicalRoutines.EllipticCurve
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α
variable {services : ClassicalOracleModel}

attribute [local irreducible] WindowTables.Outer.Frame.ofRetainedCells RetainedCells.references

/-- Every supported Store after preparation has all ten real table cells initialized. -/
lemma prepareWithTables_initialized_on_support
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (environment : (ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
      BitWord.model services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference ((ExecutionModel.quantum AlgorithmGate.model
      OracleModel.empty BitWord.model services).HiddenState × History))
    (value : Store (tableContext base noQuantum) ×
      ((ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
        BitWord.model services).HiddenState ×
        (History × (prepareWithTables (services := services) base noQuantum).Path)))
    (positive : 0 < (((prepareWithTables (services := services) base noQuantum).execute
      environment Reference state).block value).mass) :
    (RetainedCells.references (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256)).Initialized value.1 := by
  exact RetainedCells.sequence_allocated_store_of_support environment
    (prepare (services := services) base noQuantum) (WindowTables.Outer.sharedShapes 256)
    state (fun store => (RetainedCells.references (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256)).Initialized store)
    (RetainedCells.pushStore_initialized (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256)) value positive

/-- Both distinguished constant inputs are zero in the same actual supported Store. -/
lemma prepareWithTables_zero_one_on_support
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (environment : (ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
      BitWord.model services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference ((ExecutionModel.quantum AlgorithmGate.model
      OracleModel.empty BitWord.model services).HiddenState × History))
    (value : Store (tableContext base noQuantum) ×
      ((ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
        BitWord.model services).HiddenState ×
        (History × (prepareWithTables (services := services) base noQuantum).Path)))
    (positive : 0 < (((prepareWithTables (services := services) base noQuantum).execute
      environment Reference state).block value).mass) :
    (value.1.read (.storage (tableFrame base noQuantum).zero.toCStorageRef)).toNat = 0 ∧
      (value.1.read (.storage (tableFrame base noQuantum).one.toCStorageRef)).toNat = 0 := by
  have initial := prepareWithTables_initialized_on_support base noQuantum
    environment Reference state value positive
  exact WindowTables.Outer.Frame.ofRetainedCells_zero_one_initial_nat
    (RetainedCells.references (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256))
    (RetainedCells.references_keys_nodup (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256)) value.1 initial

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
