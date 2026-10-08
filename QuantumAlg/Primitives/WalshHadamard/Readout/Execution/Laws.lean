/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Pipeline

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Program
import all QuantumAlg.Primitives.WalshHadamard.Initialization.Matrix
import all QuantumAlg.Primitives.WalshHadamard
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
# The actual Walsh-Hadamard query readout state before measurement

The single interpreter prepares its prescribed basis input, applies the
original executable circuit, and allocates its actual result cells. The
resulting local quantum marginal is exactly the independently constructed
Walsh-Hadamard query readout final vector in the same physical coordinates. Every initial
classical and external-reference block participates in the preparation's
normalization; no prescribed outcome distribution is used.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

theorem allocationCode_localDensity {n : Nat} (function : WalshHadamard.Oracle n)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext n) Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    ((allocationCode function).execute Reference state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex (S := (post n).register)
        (MeasurementCells.basisEquiv (resultContext n) 2 n) := by
  rw [allocationCode, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  calc
    _ = ((State.retain state ⟨2⟩ (.bits n) (resultFresh n)).quantumMarginal.reindex
        (S := Register.prod (post n).register Reference)
        (MeasurementCells.jointBasisEquiv (resultContext n) 2 n Reference)).marginalLeft :=
      by
        simpa only [Circuit.execute_retain, ExecutionState.mapClassical_quantumMarginal,
          State.retain_quantumMarginal] using
          congrArg (DensityOperator.marginalLeft (R := (post n).register) (S := Reference))
            (MeasurementCells.allocate_quantumMarginal (model := model function)
              (resultContext n) 2 n
              ((Circuit.retain (model := model function) (preparedContext n)
                ⟨2⟩ (.bits n) (resultFresh n)).execute
                Reference state))
    _ = _ := by
      rw [MeasurementCells.jointBasisEquiv, DensityOperator.reindex_prod_marginalLeft,
        State.retain_quantumMarginal]

private theorem program_input {n : Nat} (f : WalshHadamard.Oracle n) :
    DensityOperator.applyUnitary (program f).matrix
      ((DensityOperator.ofPure (NormalizedVector.ket (R := Qubits (n + 1)) 0)).reindex
        (S := (preparedContext n).register) (preparedBasisEquiv n).symm) =
      (DensityOperator.ofPure (WalshHadamard.finalJointState f)).reindex
        (S := (preparedContext n).register) (preparedBasisEquiv n).symm := by
  rw [program_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply, Native.walshNative_zeroInputProgram_apply_zero]

/-- The actual preparation and circuit produce the original final vector before the real Z reads. -/
theorem beforeMeasurement_localDensity {n : Nat} (f : WalshHadamard.Oracle n)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H))
    (normalized : state.IsNormalized) :
    ((beforeMeasurement f).execute Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (WalshHadamard.finalJointState f)).reindex
        (S := (post n).register) (outputBasisEquiv n).symm := by
  have prepared :
      ((preparationCode f).execute Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (NormalizedVector.ket (R := Qubits (n + 1)) 0)).reindex
          (S := (preparedContext n).register) (preparedBasisEquiv n).symm :=
    (Circuit.prepareZero_empty_local_density state ⟨1⟩ (runtimeLayout n)
      preparationFresh (preparationDisjoint n) pre_systemCount normalized).trans
        (inputPreparation_density n)
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal, allocationCode_localDensity,
    Circuit.unitary_localDensity, prepared, program_input, DensityOperator.reindex_trans]
  rfl

end

end QuantumAlg.WalshHadamard.Readout
