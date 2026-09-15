/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.NativeCoordinates
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
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
# The actual joint state before the phase-register Z writes

The interpreter's basis preparation and source-query unitary produce the
same exact coherent vector as the source mathematics. Allocation of the
real phase-result cells preserves this density matrix, for every normalized
initial state and arbitrary external reference.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

theorem allocationCode_localDensity (t n : Nat) {Reference : Register}
    {H : Type} [Fintype H] (state : State (preparedContext t n) Reference H) :
    ((allocationCode t n).execute Reference state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex (S := (post t n).register)
        (MeasurementCells.basisEquiv (resultContext t n) 2 t) := by
  rw [allocationCode, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  calc
    _ = ((State.retain state ⟨1⟩ (.bits t) (resultFresh t n)).quantumMarginal.reindex
        (S := Register.prod (post t n).register Reference)
        (MeasurementCells.jointBasisEquiv (resultContext t n) 2 t Reference)).marginalLeft :=
      congrArg (DensityOperator.marginalLeft (R := (post t n).register) (S := Reference))
        (MeasurementCells.allocate_quantumMarginal (resultContext t n) 2 t
          ((Circuit.retain (preparedContext t n) ⟨1⟩ (.bits t) (resultFresh t n)).execute
            Reference state))
    _ = _ := by
      rw [MeasurementCells.jointBasisEquiv, DensityOperator.reindex_prod_marginalLeft,
        State.retain_quantumMarginal]

private theorem nativeProgram_input {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (empty : Elementary.helperWidth t n = 0) :
    DensityOperator.applyUnitary (nativeProgram E t).matrix
      ((DensityOperator.ofPure (allZeroInput E t)).reindex
        (S := (preparedContext t n).register) (preparedOriginalBasisEquiv t n empty).symm) =
      (DensityOperator.ofPure ((evolvedState E t).normalized)).reindex
        (S := (preparedContext t n).register) (preparedOriginalBasisEquiv t n empty).symm := by
  rw [nativeProgram_matrix_original E t empty, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply]
  rfl

/-- The actual prepared state is the original coherent source state before the real Z reads. -/
theorem beforeMeasurement_localDensity {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (empty : Elementary.helperWidth t n = 0)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H)
    (normalized : state.IsNormalized) :
    ((beforeMeasurement E t).execute Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure ((evolvedState E t).normalized)).reindex
        (S := (post t n).register) (outputOriginalBasisEquiv t n empty).symm := by
  have prepared :
      ((preparationCode t n).execute Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (allZeroInput E t)).reindex
          (S := (preparedContext t n).register) (preparedOriginalBasisEquiv t n empty).symm :=
    (Circuit.prepare_empty_local_density state ⟨0⟩ (runtimeLayout t n)
      preparationFresh (preparationDisjoint t n) (inputPreparation t n)
      pre_systemCount normalized).trans
        (inputPreparation_density_original E t empty)
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal, allocationCode_localDensity,
    Circuit.unitary_localDensity, prepared, nativeProgram_input E t empty,
    DensityOperator.reindex_trans]
  rfl

end

end QuantumAlg.AmplitudeEstimation
