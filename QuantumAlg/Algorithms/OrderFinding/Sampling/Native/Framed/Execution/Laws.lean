/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Preparation.Coordinates
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.State
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
# The state before the selected source sampler's Z measurements

Real zero preparation, the native source word, and allocation of retained
classical outputs yield the source Born vector in the interpreter's physical
basis. The caller may have arbitrary classical cells and external reference.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private lemma sourcePrepared_density (t width : Nat) :
    (DensityOperator.ofPure
      (BasisPreparation.zero (Sampling.Native.runtimeLayout t width)).normalized).reindex
        (S := (preparedContext ctx noQuantum t width).register)
        (Execution.preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey
          (Sampling.Native.runtimeLayout t width) ctx.canonicalFreshKey_fresh
          (by simp only [RuntimeCtx.physicalIdx, noQuantum]; exact List.disjoint_nil_right _)
          (input_systemCount ctx noQuantum)) =
      (DensityOperator.ofPure (OrderFinding.Native.zeroInput t width)).reindex
        (S := (preparedContext ctx noQuantum t width).register)
        (preparedBasisEquiv ctx noQuantum t width).symm := by
  let binary := QuantumSignature.qubitsIndexEquiv (t + width)
  let physical := Execution.basisOfEqualWires
    (Sampling.Native.runtimeLayout t width)
    (preparedContext ctx noQuantum t width).quantumLayout
    (prepared_wires ctx noQuantum t width)
  have coordinate :
      Execution.preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey
        (Sampling.Native.runtimeLayout t width) ctx.canonicalFreshKey_fresh
        (by simp only [RuntimeCtx.physicalIdx, noQuantum]; exact List.disjoint_nil_right _)
        (input_systemCount ctx noQuantum) =
          physical := preparedEmptyBasis_eq_native ctx noQuantum t width
  have preparedEntry (basis : (Sampling.Native.runtimeLayout t width).register.Index) :
      (BasisPreparation.zero (Sampling.Native.runtimeLayout t width)).normalized basis =
        OrderFinding.Native.zeroInput t width (binary basis) := by
    have equal := congrArg
      (fun value : NormalizedVector (Qubits (t + width)) => value (binary basis))
      (preparedZero_vector t width)
    change (BasisPreparation.zero (Sampling.Native.runtimeLayout t width)).normalized
      (binary.symm (binary basis)) =
        OrderFinding.Native.zeroInput t width (binary basis) at equal
    simpa only [Equiv.symm_apply_apply] using equal
  apply DensityOperator.ext
  ext row column
  rw [coordinate, DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix]
  have aligned (basis : (preparedContext ctx noQuantum t width).register.Index) :
      binary (physical.symm basis) = preparedBasisEquiv ctx noQuantum t width basis := by
    rfl
  rw [preparedEntry, preparedEntry, aligned, aligned]
  simp only [Equiv.symm_symm]

/-- Retained measurement cells preserve the complete prepared quantum density. -/
lemma allocationCode_localDensity {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext ctx noQuantum t width) Reference
      ((model t width).HiddenState × H)) :
    ((allocationCode ctx noQuantum t width).execute (Sampling.Native.environment access) Reference
      state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex (S := (post ctx noQuantum t width).register)
        (MeasurementCells.basisEquiv (resultContext ctx noQuantum t width) 2 t) := by
  rw [allocationCode, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  calc
    _ = ((State.retain state (preparedContext ctx noQuantum t width).canonicalFreshKey (.bits t)
        (preparedContext ctx noQuantum t width).canonicalFreshKey_fresh).quantumMarginal.reindex
        (S := Register.prod (post ctx noQuantum t width).register Reference)
        (MeasurementCells.jointBasisEquiv
          (resultContext ctx noQuantum t width) 2 t Reference)).marginalLeft := by
      simpa only [Circuit.execute_retain, ExecutionState.mapClassical_quantumMarginal,
        State.retain_quantumMarginal] using
        congrArg (DensityOperator.marginalLeft
          (R := (post ctx noQuantum t width).register) (S := Reference))
          (MeasurementCells.allocate_quantumMarginal (model := model t width)
            (Sampling.Native.environment access)
            (resultContext ctx noQuantum t width) 2 t
            ((Circuit.retain (model := model t width) (preparedContext ctx noQuantum t width)
              (preparedContext ctx noQuantum t width).canonicalFreshKey (.bits t)
              (preparedContext ctx noQuantum t width).canonicalFreshKey_fresh).execute
                (Sampling.Native.environment access)
              Reference state))
    _ = _ := by
      rw [MeasurementCells.jointBasisEquiv, DensityOperator.reindex_prod_marginalLeft,
        State.retain_quantumMarginal]

/-- The real native source word reaches its declared coherent Born state. -/
lemma beforeMeasurement_localDensity {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference ((model t width).HiddenState × H))
    (normalized : state.IsNormalized) :
    ((beforeMeasurement ctx noQuantum t width).execute (Sampling.Native.environment access)
      Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (OrderFinding.Native.evolvedVector access)).reindex
        (S := (post ctx noQuantum t width).register)
        (outputBasisEquiv ctx noQuantum t width).symm := by
  have prepared :
      ((preparationCode ctx noQuantum t width).execute (Sampling.Native.environment access)
        Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (OrderFinding.Native.zeroInput t width)).reindex
          (S := (preparedContext ctx noQuantum t width).register)
          (preparedBasisEquiv ctx noQuantum t width).symm :=
    (Circuit.prepareZero_empty_local_density (Sampling.Native.environment access) state
      ctx.canonicalFreshKey
      (Sampling.Native.runtimeLayout t width) ctx.canonicalFreshKey_fresh
      (by simp only [RuntimeCtx.physicalIdx, noQuantum]; exact List.disjoint_nil_right _)
      (input_systemCount ctx noQuantum) normalized).trans
        (sourcePrepared_density ctx noQuantum t width)
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal,
    allocationCode_localDensity ctx noQuantum access,
    Circuit.unitary_localDensity, prepared]
  simp only [Sampling.Native.environment]
  rw [nativeProgram_zero_density ctx noQuantum access,
    DensityOperator.reindex_trans]
  rfl

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
