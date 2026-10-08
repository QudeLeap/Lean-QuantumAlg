/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Query.Ladder
import all QuantumAlg.Algorithms.QPE.Query.Ladder
import all QuantumAlg.Algorithms.QPE.Query.Matrix
import all QuantumAlg.Algorithms.QPE.Query.Exponents
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Product
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Exact matrix of the actual QPE query ladder

The original phase label controls the corresponding power of the source
unitary. Every factor is an actual repeated declared query
[Lin22, phaseestimation.tex:514-523].
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

private theorem stageMatrixFold (gates : GateModel) (phaseWidth : Nat)
    {systemWidth : Nat} (unitary : UnitaryOperator (Qubits systemWidth))
    (stages : List (Fin phaseWidth)) (initial : Fin (2 ^ phaseWidth) → Nat) :
    (stages.map (fun stage => (powerStage gates unitary stage).binaryMatrix)).foldl
        (fun accumulated next => next * accumulated)
        (qpeExponentOp phaseWidth unitary initial) =
      qpeExponentOp phaseWidth unitary (stageExponentFold stages initial) := by
  induction stages generalizing initial with
  | nil => rfl
  | cons stage stages ih =>
      rw [List.map_cons, List.foldl_cons, qpeNative_powerStage_binaryMatrix,
        qpeExponentOp_mul]
      exact ih (fun phase => stageExponent stage phase + initial phase)

/-- The actual ladder has the original full block-diagonal source-power matrix. -/
theorem qpeNative_queryLadder_binaryMatrix (gates : GateModel) (phaseWidth : Nat)
    {systemWidth : Nat} (unitary : UnitaryOperator (Qubits systemWidth)) :
    (queryLadder gates phaseWidth unitary).binaryMatrix =
      qpeControlledPowerOp phaseWidth unitary := by
  rw [queryLadder, UnitaryCircuit.unitaryCircuit_binaryMatrix_indexedProduct,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
  rw [show (1 : UnitaryOperator (Qubits (phaseWidth + systemWidth))) =
      qpeExponentOp phaseWidth unitary (fun _ => 0) from
        (qpeExponentOp_zero phaseWidth unitary).symm]
  rw [show List.ofFn (fun stage : Fin phaseWidth =>
      (powerStage gates unitary stage).binaryMatrix) =
        (List.ofFn fun stage : Fin phaseWidth => stage).map
          (fun stage => (powerStage gates unitary stage).binaryMatrix) by
    exact List.ofFn_comp' (fun stage : Fin phaseWidth => stage)
      (fun stage => (powerStage gates unitary stage).binaryMatrix)]
  rw [stageMatrixFold]
  change qpeExponentOp phaseWidth unitary
      (stageExponentFold (List.ofFn fun stage : Fin phaseWidth => stage)
        (fun _ => 0)) = qpeExponentOp phaseWidth unitary Fin.val
  congr 1
  funext phase
  exact stageExponentFold_all phase

end

end QuantumAlg.QuantumPhaseEstimation.Native
