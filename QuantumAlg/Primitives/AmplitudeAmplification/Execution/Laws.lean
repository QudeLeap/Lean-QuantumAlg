/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Program.Laws
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# The actual amplification output state

Charged basis preparation and the actual source program produce the original
closed-form amplified state together with the retained zero helper. The
result holds for every normalized initial state and external reference.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

private theorem preparedInput_eq (n k : Nat) :
    preparedInput n k = Native.inputVector n k := by
  have zeroBasis : prodEquiv ((0 : Fin (2 ^ n)),
      (0 : Fin (2 ^ ZeroReflection.Workspace.helperWidth n k))) =
      (0 : Fin (2 ^ ZeroReflection.Workspace.totalQubits n k)) := by
    apply Fin.ext
    rfl
  exact ((NormalizedVector.tensor_ket (0 : Fin (2 ^ n))
    (0 : Fin (2 ^ ZeroReflection.Workspace.helperWidth n k))).trans
      (congrArg (NormalizedVector.ket (R := Qubits (ZeroReflection.Workspace.totalQubits n k)))
        zeroBasis)).symm

private theorem nativeProgram_input {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) :
    DensityOperator.applyUnitary (nativeProgram M k).matrix
      ((DensityOperator.ofPure (preparedInput n k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm) =
      (DensityOperator.ofPure (Native.outputVector M k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm := by
  rw [nativeProgram, UnitaryCircuit.reindex_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply, preparedInput_eq]
  change (DensityOperator.ofPure
    ((Native.program M.preparation M.good k).applyNormalized (Native.inputVector n k))).reindex
      (S := (post n k).register) (preparedBasisEquiv n k).symm = _
  rw [Native.program_applyNormalized_input]

/-- The sole interpreter's local output is the independent exact amplified pure state. -/
theorem code_localDensity {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H)
    (normalized : state.IsNormalized) :
    ((code M k).execute Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (Native.outputVector M k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm := by
  have prepared :
      ((preparationCode n k).execute Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (preparedInput n k)).reindex
          (S := (post n k).register) (preparedBasisEquiv n k).symm :=
    (Circuit.prepare_empty_local_density state ⟨0⟩ (runtimeLayout n k)
      preparationFresh (preparationDisjoint n k) (inputPreparation n k)
      pre_systemCount normalized).trans (inputPreparation_density n k)
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.unitary_localDensity, prepared, nativeProgram_input]

/-- Summing the actual classical records and histories preserves that same output state. -/
theorem final_localDensity {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    {Reference : Register} (supplied : Input pre Reference) :
    ((run M k).finalState Reference supplied.state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (Native.outputVector M k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm := by
  calc
    _ = ((run M k).execute Reference supplied.state).quantumMarginal.marginalLeft :=
      congrArg (DensityOperator.marginalLeft (R := (post n k).register) (S := Reference))
        (ExecutionState.mapClassical_quantumMarginal
          ((run M k).execute Reference supplied.state) Prod.fst)
    _ = _ := code_localDensity M k
      (supplied.state.mapClassical (fun store => (store, store)))
      ((supplied.state.mapClassical_mass _).trans supplied.normalized)

end

end QuantumAlg.AmplitudeAmplification
