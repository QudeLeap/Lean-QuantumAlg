/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Algorithms.QPE.Preparation
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

/-!
# The actual joint state before the phase-register Z writes

The interpreter's basis preparation and source-query unitary produce the
same exact coherent vector as the source mathematics. Allocation of the
real phase-result cells preserves this density matrix, for every normalized
initial state and arbitrary external reference.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

lemma allocationCode_localDensity {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) {Reference : Register}
    {H : Type} [Fintype H]
    (state : State (preparedContext t n) Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    ((allocationCode n t).execute (sourceEnvironment P.unitary) Reference
      state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex (S := (post t n).register)
        (MeasurementCells.basisEquiv (resultContext t n) 2 t) := by
  rw [allocationCode, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  calc
    _ = ((State.retain state ⟨2⟩ (.bits t) (resultFresh t n)).quantumMarginal.reindex
        (S := Register.prod (post t n).register Reference)
        (MeasurementCells.jointBasisEquiv (resultContext t n) 2 t Reference)).marginalLeft :=
      by
        simpa only [Circuit.execute_retain, ExecutionState.mapClassical_quantumMarginal,
          State.retain_quantumMarginal] using
          congrArg (DensityOperator.marginalLeft (R := (post t n).register) (S := Reference))
            (MeasurementCells.allocate_quantumMarginal (environment := sourceEnvironment
              P.unitary) (model := model n)
              (resultContext t n) 2 t
              ((Circuit.retain (model := model n) (preparedContext t n)
                ⟨2⟩ (.bits t) (resultFresh t n)).execute (sourceEnvironment P.unitary) Reference
                  state))
    _ = _ := by
      rw [MeasurementCells.jointBasisEquiv, DensityOperator.reindex_prod_marginalLeft,
        State.retain_quantumMarginal]

private lemma nativeProgram_matrix {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    ((nativeProgram n t).matrix (UnitarySource.interpretation P.unitary true)) =
      UnitaryOperator.reindex (preparedBasisEquiv t n).symm
      ((Native.circuit t n).binaryMatrix (UnitarySource.interpretation P.unitary true)) := by
  rw [nativeProgram, unitaryOfEqualWires_matrix (runtimeLayout t n)
    (preparedContext t n).quantumLayout (runtime_wires t n)
    (UnitarySource.interpretation P.unitary true) (Native.circuit t n)]
  apply Subtype.ext
  ext row column
  change ((Native.circuit t n).matrix (UnitarySource.interpretation P.unitary true))
    ((preparedLayoutEquiv t n).symm row) ((preparedLayoutEquiv t n).symm column) =
      ((Native.circuit t n).matrix (UnitarySource.interpretation P.unitary true))
        ((qpeLayout t n).binaryIndexEquiv.symm (preparedBasisEquiv t n row))
        ((qpeLayout t n).binaryIndexEquiv.symm (preparedBasisEquiv t n column))
  simp only [preparedBasisEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

private lemma nativeProgram_input {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) :
    DensityOperator.applyUnitary ((nativeProgram n t).matrix (UnitarySource.interpretation
      P.unitary true))
      ((DensityOperator.ofPure (qpeInput P t)).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm) =
      (DensityOperator.ofPure ((qpeEvolvedState P t).normalized)).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm := by
  rw [nativeProgram_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply]
  rfl

/-- The actual prepared state is the original coherent source state before the real Z reads. -/
lemma beforeMeasurement_localDensity {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre t n) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (promised : inputPromise P t state.quantumMarginal.marginalLeft) :
    ((beforeMeasurement n t).execute (sourceEnvironment P.unitary) Reference
      state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure ((qpeEvolvedState P t).normalized)).reindex
        (S := (post t n).register) (outputBasisEquiv t n).symm := by
  have prepared := preparationCode_localDensity P t state promised
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal, allocationCode_localDensity,
    Circuit.unitary_localDensity, prepared]
  change (DensityOperator.applyUnitary
    ((nativeProgram n t).matrix (UnitarySource.interpretation P.unitary true)) _).reindex _ = _
  rw [nativeProgram_input, DensityOperator.reindex_trans]
  rfl

end

end QuantumAlg.QuantumPhaseEstimation
