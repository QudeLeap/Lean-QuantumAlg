/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.StepLaws
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Power.Coordinates
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Construction
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Construction

/-!
# The exact original exponent of the elementary source ladder

The actual finite stage list contributes the original binary weights. Even
when the total definition contains a work suffix, only the original phase
label selects the source power. Its arbitrary work value is untouched.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

private theorem powerStage_matrix_original {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (powerStage U good stage).matrix = qpeExponentOp (phaseWidth t n)
      (U * (ZeroReflection.zeroReflectionOperator n *
        (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
      (fun phase => qpeStageExponent stage (originalPhase t n phase)) := by
  rw [powerStage_matrix]
  congr 1
  funext phase
  exact extendedStage_exponent n stage phase

private theorem stageMatrixFold {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stages : List (Fin t))
    (initial : Fin (2 ^ t) → Nat) :
    (stages.map (fun stage => (powerStage U good stage).matrix)).foldl
        (fun (accumulated next : UnitaryOperator (Qubits (totalQubits t n))) => next * accumulated)
        (qpeExponentOp (phaseWidth t n)
          (U * (ZeroReflection.zeroReflectionOperator n *
            (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
          (fun phase => initial (originalPhase t n phase))) =
      qpeExponentOp (phaseWidth t n)
        (U * (ZeroReflection.zeroReflectionOperator n *
          (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
        (fun phase => qpeStageExponentFold stages initial (originalPhase t n phase)) := by
  induction stages generalizing initial with
  | nil => rfl
  | cons stage stages ih =>
      rw [List.map_cons, List.foldl_cons, powerStage_matrix_original, qpeExponentOp_mul]
      exact ih (fun phase => qpeStageExponent stage phase + initial phase)

/-- The full actual ladder applies precisely the source power indexed by the original phase. -/
theorem ladder_matrix {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (ladder t U good).matrix = qpeExponentOp (phaseWidth t n)
      (U * (ZeroReflection.zeroReflectionOperator n *
        (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
      (fun phase => (originalPhase t n phase).val) := by
  let source := U * (ZeroReflection.zeroReflectionOperator n *
    (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good))
  change (List.ofFn (fun stage : Fin t => (powerStage U good stage).matrix)).foldl
    (fun (accumulated next : UnitaryOperator (Qubits (totalQubits t n))) =>
      next * accumulated) 1 = _
  rw [show (1 : UnitaryOperator (Qubits (totalQubits t n))) =
      qpeExponentOp (phaseWidth t n) source (fun _ => 0) from
        (qpeExponentOp_zero (phaseWidth t n) source).symm]
  rw [show List.ofFn (fun stage : Fin t => (powerStage U good stage).matrix) =
      (List.ofFn fun stage : Fin t => stage).map
        (fun stage => (powerStage U good stage).matrix) by
    exact List.ofFn_comp' (fun stage : Fin t => stage)
      (fun stage => (powerStage U good stage).matrix)]
  calc
    _ = qpeExponentOp (phaseWidth t n) source
        (fun phase => qpeStageExponentFold (List.ofFn fun stage : Fin t => stage)
          (fun _ => 0) (originalPhase t n phase)) :=
      stageMatrixFold U good (List.ofFn fun stage : Fin t => stage) (fun _ => 0)
    _ = _ := by
      congr 1
      funext phase
      exact qpeStageExponentFold_all (originalPhase t n phase)

end

end QuantumAlg.AmplitudeEstimation.Elementary
