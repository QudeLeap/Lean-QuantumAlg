/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.BornModel
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Storage
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Execution
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

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution
open QuantumAlg.OrderFinding.BornBridge

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

/-- The actual preparation is exactly the source's all-zero input in its physical coordinates. -/
theorem inputPreparation_density (t n : Nat) :
    (DensityOperator.ofPure (inputPreparation t n).normalized).reindex
      (S := (preparedContext ctx noQuantum t n).register) (preparedLayoutEquiv ctx noQuantum t n) =
        (DensityOperator.ofPure (preparedInput t n)).reindex
          (S := (preparedContext ctx noQuantum t n).register)
          (preparedBasisEquiv ctx noQuantum t n).symm := by
  have preparedEntry (basis : (runtimeLayout t n).register.Index) :
      (inputPreparation t n).normalized basis =
        preparedInput t n
          ((sourceLayout t n).binaryIndexEquiv basis) := by
    dsimp only [preparedInput]
    change NormalizedVector.ket
      ((sourceLayout t n).binaryIndexEquiv.symm
      (0 : Fin (2 ^ (t + n)))) basis =
        NormalizedVector.ket (R := Qubits (t + n))
          (0 : Fin (2 ^ (t + n))) _
    rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
    simp only [Equiv.eq_symm_apply]
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix, preparedEntry, preparedEntry]
  rfl

theorem allocationCode_localDensity (t n : Nat) {Reference : Register}
    {H : Type} [Fintype H] (state : State (preparedContext ctx noQuantum t n) Reference H) :
    ((allocationCode ctx noQuantum t n).execute Reference state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex (S := (post ctx noQuantum t n).register)
        (MeasurementCells.basisEquiv (resultContext ctx noQuantum t n) 2 t) := by
  rw [allocationCode, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  calc
    _ = ((State.retain state (preparedContext ctx noQuantum t n).canonicalFreshKey (.bits t)
        (preparedContext ctx noQuantum t n).canonicalFreshKey_fresh).quantumMarginal.reindex
        (S := Register.prod (post ctx noQuantum t n).register Reference)
        (MeasurementCells.jointBasisEquiv
          (resultContext ctx noQuantum t n) 2 t Reference)).marginalLeft :=
      congrArg (DensityOperator.marginalLeft
        (R := (post ctx noQuantum t n).register) (S := Reference))
        (MeasurementCells.allocate_quantumMarginal (resultContext ctx noQuantum t n) 2 t
          ((Circuit.retain (preparedContext ctx noQuantum t n)
            (preparedContext ctx noQuantum t n).canonicalFreshKey (.bits t)
            (preparedContext ctx noQuantum t n).canonicalFreshKey_fresh).execute
            Reference state))
    _ = _ := by
      rw [MeasurementCells.jointBasisEquiv, DensityOperator.reindex_prod_marginalLeft,
        State.retain_quantumMarginal]

private theorem nativeProgram_input {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    DensityOperator.applyUnitary (nativeProgram ctx noQuantum A).matrix
      ((DensityOperator.ofPure (preparedInput t n)).reindex
        (S := (preparedContext ctx noQuantum t n).register)
        (preparedBasisEquiv ctx noQuantum t n).symm) =
      (DensityOperator.ofPure ((evolvedState A).normalized)).reindex
        (S := (preparedContext ctx noQuantum t n).register)
        (preparedBasisEquiv ctx noQuantum t n).symm := by
  rw [nativeProgram, UnitaryCircuit.reindex_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply]
  rfl

/-- The actual prepared state is the original coherent source state before the real Z reads. -/
theorem beforeMeasurement_localDensity {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (normalized : state.IsNormalized) :
    ((beforeMeasurement ctx noQuantum A).execute Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure ((evolvedState A).normalized)).reindex
        (S := (post ctx noQuantum t n).register) (outputBasisEquiv ctx noQuantum t n).symm := by
  have prepared :
      ((preparationCode ctx noQuantum t n).execute Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (preparedInput t n)).reindex
          (S := (preparedContext ctx noQuantum t n).register)
          (preparedBasisEquiv ctx noQuantum t n).symm :=
    (Circuit.prepare_empty_local_density state ctx.canonicalFreshKey (runtimeLayout t n)
      ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n) (inputPreparation t n)
      (input_systemCount ctx noQuantum) normalized).trans
        (inputPreparation_density ctx noQuantum t n)
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal, allocationCode_localDensity,
    Circuit.unitary_localDensity, prepared, nativeProgram_input ctx noQuantum A,
    DensityOperator.reindex_trans]
  rfl

end

end QuantumAlg.OrderFinding.Sampling.Framed
