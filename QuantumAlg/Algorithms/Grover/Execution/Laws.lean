/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Elementary.Laws
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# The actual prepared Grover state before measurement

The single interpreter prepares the all-zero search register and applies
the original initial Hadamards and k elementary Grover iterates. Allocation of real
measurement and packed-result cells preserves that local density matrix.
The result is the original exact evolved vector in the same wire coordinates,
for every normalized input and external-reference extension.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

theorem allocationCode_localDensity (n k : Nat) {Reference : Register}
    {H : Type} [Fintype H]
    (state : State (preparedContext (totalQubits n k)) Reference H) :
    ((allocationCode n k).execute Reference state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex (S := (post n k).register)
        (MeasurementCells.basisEquiv (resultContext n k) 2 n) := by
  rw [allocationCode, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  calc
    _ = ((State.retain state ⟨2⟩ (.bits n) (resultFresh n k)).quantumMarginal.reindex
        (S := Register.prod (post n k).register Reference)
        (MeasurementCells.jointBasisEquiv (resultContext n k) 2 n Reference)).marginalLeft :=
      congrArg (DensityOperator.marginalLeft (R := (post n k).register) (S := Reference))
        (MeasurementCells.allocate_quantumMarginal (resultContext n k) 2 n
          ((Circuit.retain (preparedContext (totalQubits n k))
            ⟨2⟩ (.bits n) (resultFresh n k)).execute Reference state))
    _ = _ := by
      rw [MeasurementCells.jointBasisEquiv, DensityOperator.reindex_prod_marginalLeft,
        State.retain_quantumMarginal]

private theorem program_input {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    DensityOperator.applyUnitary (program marked k).matrix
      ((DensityOperator.ofPure (Elementary.inputVector n k)).reindex
        (S := (preparedContext (totalQubits n k)).register)
          (preparedBasisEquiv (totalQubits n k)).symm) =
      (DensityOperator.ofPure (Elementary.evolvedVector marked k)).reindex
        (S := (preparedContext (totalQubits n k)).register)
          (preparedBasisEquiv (totalQubits n k)).symm := by
  rw [program, UnitaryCircuit.reindex_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply]
  change (DensityOperator.ofPure
    ((Elementary.circuit marked k).applyNormalized (Elementary.inputVector n k))).reindex
      (S := (preparedContext (totalQubits n k)).register)
          (preparedBasisEquiv (totalQubits n k)).symm = _
  rw [Elementary.circuit_applyNormalized_input]

/-- The actual preparation and circuit produce the original final vector before the real Z reads. -/
theorem beforeMeasurement_localDensity {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H)
    (normalized : state.IsNormalized) :
    ((beforeMeasurement marked k).execute Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (Elementary.evolvedVector marked k)).reindex
        (S := (post n k).register) (outputBasisEquiv n k).symm := by
  have prepared :
      ((preparationCode (totalQubits n k)).execute Reference
        state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (Elementary.inputVector n k)).reindex
          (S := (preparedContext (totalQubits n k)).register)
          (preparedBasisEquiv (totalQubits n k)).symm :=
    (Circuit.prepare_empty_local_density state ⟨1⟩ (runtimeLayout (totalQubits n k))
      preparationFresh (preparationDisjoint (totalQubits n k))
      (inputPreparation (totalQubits n k))
      pre_systemCount normalized).trans
        (by
          rw [elementaryInput_eq_zero]
          exact inputPreparation_density (totalQubits n k))
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal, allocationCode_localDensity,
    Circuit.unitary_localDensity, prepared, program_input, DensityOperator.reindex_trans]
  rfl

end

end QuantumAlg.GroverSearch
