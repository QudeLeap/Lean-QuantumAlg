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
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero

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

lemma allocationCode_localDensity (n k : Nat) (actual : (model n).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext (totalQubits n k)) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((allocationCode n k).execute actual Reference state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex (S := (post n k).register)
        (MeasurementCells.basisEquiv (resultContext n k) 2 n) := by
  rw [allocationCode, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  calc
    _ = ((State.retain state ⟨2⟩ (.bits n) (resultFresh n k)).quantumMarginal.reindex
        (S := Register.prod (post n k).register Reference)
        (MeasurementCells.jointBasisEquiv (resultContext n k) 2 n Reference)).marginalLeft := by
      simpa only [Circuit.execute_retain, ExecutionState.mapClassical_quantumMarginal,
        State.retain_quantumMarginal] using
        congrArg (DensityOperator.marginalLeft (R := (post n k).register) (S := Reference))
          (MeasurementCells.allocate_quantumMarginal (model := model n)
            (environment := actual)
            (resultContext n k) 2 n
            ((Circuit.retain (model := model n) (preparedContext (totalQubits n k))
              ⟨2⟩ (.bits n) (resultFresh n k)).execute actual Reference state))
    _ = _ := by
      rw [MeasurementCells.jointBasisEquiv, DensityOperator.reindex_prod_marginalLeft,
        State.retain_quantumMarginal]

private lemma preparedPosition_eq (width : Nat) (index : Fin width) :
    positionsOfEqualWires (QuantumSignature.qubits width).canonicalPlacement.layout
      (preparedContext width).quantumLayout (prepared_canonical_wires width) index =
        preparedWire width index := by
  apply Fin.ext
  rfl

private lemma preparedLayoutEquiv_equalWires (width : Nat) :
    basisOfEqualWires (QuantumSignature.qubits width).canonicalPlacement.layout
      (preparedContext width).quantumLayout (prepared_canonical_wires width) =
        preparedLayoutEquiv width := by
  apply Equiv.ext
  intro basis
  funext position
  obtain ⟨index, rfl⟩ :=
    (positionsOfEqualWires (QuantumSignature.qubits width).canonicalPlacement.layout
      (preparedContext width).quantumLayout (prepared_canonical_wires width)).surjective position
  apply Fin.ext
  rw [basisOfEqualWires_value, preparedPosition_eq]
  exact (preparedLayoutEquiv_value width basis index).symm

private lemma program_matrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ((program n k).matrix (environment marked).quantum) =
      UnitaryOperator.reindex (preparedBasisEquiv (totalQubits n k)).symm
        ((Elementary.circuit n k).binaryMatrix (Elementary.interpretation marked)) := by
  rw [program, unitaryOfEqualWires_matrix, preparedLayoutEquiv_equalWires]
  apply Subtype.ext
  ext row column
  change ((Elementary.circuit n k).matrix (Elementary.interpretation marked))
    ((preparedLayoutEquiv (totalQubits n k)).symm row)
    ((preparedLayoutEquiv (totalQubits n k)).symm column) =
      ((Elementary.circuit n k).matrix (Elementary.interpretation marked))
        ((layout (totalQubits n k)).binaryIndexEquiv.symm
          ((preparedBasisEquiv (totalQubits n k)) row))
        ((layout (totalQubits n k)).binaryIndexEquiv.symm
          ((preparedBasisEquiv (totalQubits n k)) column))
  simp only [preparedBasisEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

private lemma zeroPreparation_eq (width : Nat) :
    BasisPreparation.zero (runtimeLayout width) = inputPreparation width := by
  apply congrArg BasisPreparation.mk
  exact (BinaryBasis.bigEndianEquiv_symm_zero width).symm

private lemma program_input {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    DensityOperator.applyUnitary ((program n k).matrix (environment marked).quantum)
      ((DensityOperator.ofPure (Elementary.inputVector n k)).reindex
        (S := (preparedContext (totalQubits n k)).register)
          (preparedBasisEquiv (totalQubits n k)).symm) =
      (DensityOperator.ofPure (Elementary.evolvedVector marked k)).reindex
        (S := (preparedContext (totalQubits n k)).register)
          (preparedBasisEquiv (totalQubits n k)).symm := by
  rw [program_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply, Elementary.circuit_applyNormalized_input]

/-- The actual preparation and circuit produce the original final vector before the real Z reads. -/
lemma beforeMeasurement_localDensity {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H))
    (normalized : state.IsNormalized) :
    ((beforeMeasurement n k).execute
          (environment marked) Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (Elementary.evolvedVector marked k)).reindex
        (S := (post n k).register) (outputBasisEquiv n k).symm := by
  have prepared :
      ((preparationCode n k).execute (environment marked) Reference
        state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (Elementary.inputVector n k)).reindex
          (S := (preparedContext (totalQubits n k)).register)
          (preparedBasisEquiv (totalQubits n k)).symm := by
    have prepared := Circuit.prepareZero_empty_local_density (environment := environment marked)
      (gates := AlgorithmGate.model) (oracles := Elementary.oracles n)
      (operations := BitWord.model) (classicalOracles := .empty)
      state ⟨1⟩ (runtimeLayout (totalQubits n k)) preparationFresh
      (preparationDisjoint (totalQubits n k)) pre_systemCount normalized
    rw [zeroPreparation_eq] at prepared
    refine prepared.trans ?_
    rw [elementaryInput_eq_zero]
    exact inputPreparation_density (totalQubits n k)
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal, allocationCode_localDensity,
    Circuit.unitary_localDensity, prepared, program_input, DensityOperator.reindex_trans]
  rfl

end

end QuantumAlg.GroverSearch
