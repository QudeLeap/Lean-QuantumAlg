/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Program.Laws
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero
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

private lemma preparedInput_eq (n k : Nat) :
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

private lemma preparedLayoutEquiv_eq_wireBasis (n k : Nat) :
    preparedLayoutEquiv n k =
      basisOfEqualWires
        (QuantumSignature.qubits
          (ZeroReflection.Workspace.totalQubits n k)).canonicalPlacement.layout
        (post n k).quantumLayout (post_canonical_wires n k) := by
  apply Equiv.ext
  intro basis
  funext target
  let layout :=
    (QuantumSignature.qubits
          (ZeroReflection.Workspace.totalQubits n k)).canonicalPlacement.layout
  obtain ⟨index, rfl⟩ :=
    (positionsOfEqualWires layout (post n k).quantumLayout (post_canonical_wires n k)).surjective
      target
  apply Fin.ext
  have position :
      positionsOfEqualWires layout (post n k).quantumLayout (post_canonical_wires n k) index =
        pre.addOwnedLayoutPositionEquiv ⟨0⟩ (runtimeLayout n k) preparationFresh
          (preparationDisjoint n k) (Fin.castAdd pre.systemCount index) := by
    apply Fin.ext
    rfl
  have prepared :
      (preparedLayoutEquiv n k basis
        (positionsOfEqualWires layout (post n k).quantumLayout
          (post_canonical_wires n k) index)).val = (basis index).val := by
    rw [position]
    exact (pre.addOwnedLayout_basis_value_preserved ⟨0⟩ (runtimeLayout n k)
      preparationFresh (preparationDisjoint n k) _ (Fin.castAdd pre.systemCount index)).trans
        (QuantumLayout.appendJoinBasis_left_value _ _ _ basis
          (emptyContextBasis pre pre_systemCount) index)
  exact prepared.trans
    (basisOfEqualWires_value layout (post n k).quantumLayout
      (post_canonical_wires n k) basis index).symm

private lemma nativeProgram_matrix {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) :
    ((nativeProgram n k).matrix (environment M).quantum) =
      UnitaryOperator.reindex (preparedBasisEquiv n k).symm
        ((Native.program n k).binaryMatrix (Native.interpretation M.preparation M.good)) := by
  rw [nativeProgram, unitaryOfEqualWires_matrix, UnitaryCircuit.binaryMatrix,
    UnitaryOperator.unitaryOperator_reindex_trans]
  rw [preparedBasisEquiv, preparedLayoutEquiv_eq_wireBasis]
  exact congrArg (fun equivalence => UnitaryOperator.reindex equivalence
    ((Native.program n k).matrix (Native.interpretation M.preparation M.good))) (by
      apply Equiv.ext
      intro basis
      simp only [Equiv.symm_trans_apply, Equiv.trans_apply]
      apply congrArg (basisOfEqualWires
        (QuantumSignature.qubits
          (ZeroReflection.Workspace.totalQubits n k)).canonicalPlacement.layout
        (post n k).quantumLayout (post_canonical_wires n k))
      exact ((QuantumSignature.qubitsIndexEquiv
        (ZeroReflection.Workspace.totalQubits n k)).symm_apply_apply basis).symm)

private lemma zeroPreparation_eq (n k : Nat) :
    BasisPreparation.zero (runtimeLayout n k) = inputPreparation n k := by
  apply congrArg BasisPreparation.mk
  exact (BinaryBasis.bigEndianEquiv_symm_zero
    (ZeroReflection.Workspace.totalQubits n k)).symm

private lemma nativeProgram_input {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) :
    DensityOperator.applyUnitary ((nativeProgram n k).matrix (environment M).quantum)
      ((DensityOperator.ofPure (preparedInput n k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm) =
      (DensityOperator.ofPure (Native.outputVector M k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm := by
  rw [nativeProgram_matrix, ← DensityOperator.applyUnitary_reindex,
    ← DensityOperator.ofPure_apply, preparedInput_eq, Native.program_applyNormalized_input]

/-- The sole interpreter's local output is the independent exact amplified pure state. -/
lemma code_localDensity {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H))
    (normalized : state.IsNormalized) :
    ((code n k).execute (environment M) Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (Native.outputVector M k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm := by
  have prepared :
      ((preparationCode n k).execute (environment M) Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (preparedInput n k)).reindex
          (S := (post n k).register) (preparedBasisEquiv n k).symm := by
    have prepared := Circuit.prepareZero_empty_local_density (environment := environment M)
      (gates := AlgorithmGate.model) (oracles := Native.oracles n)
      (operations := .empty) (classicalOracles := .empty) state ⟨0⟩ (runtimeLayout n k)
      preparationFresh (preparationDisjoint n k) pre_systemCount normalized
    rw [zeroPreparation_eq] at prepared
    exact prepared.trans (inputPreparation_density n k)
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.unitary_localDensity, prepared, nativeProgram_input]

/-- Summing the actual classical records and histories preserves that same output state. -/
lemma final_localDensity {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    {Reference : Register} (supplied : OracleInput (model n).classicalOracles pre Reference) :
    ((run n k).finalState (environment M) Reference supplied.state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (Native.outputVector M k)).reindex
        (S := (post n k).register) (preparedBasisEquiv n k).symm := by
  calc
    _ = ((run n k).execute (environment M) Reference supplied.state).quantumMarginal.marginalLeft :=
      congrArg (DensityOperator.marginalLeft (R := (post n k).register) (S := Reference))
        (ExecutionState.mapClassical_quantumMarginal
          ((run n k).execute (environment M) Reference supplied.state) Prod.fst)
    _ = _ := code_localDensity M k
      (supplied.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      ((supplied.state.mapClassical_mass _).trans supplied.normalized)

end

end QuantumAlg.AmplitudeAmplification
