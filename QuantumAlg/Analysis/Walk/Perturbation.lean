/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.Walk.Construction
import all QuantumAlg.Analysis.Walk.Construction
public import QuantumAlg.Util.ProbabilityBound

/-!
# Pointwise reflection perturbation

A supplied approximate reflection accumulates at most `kη` state error and
`2kη` squared-amplitude loss. Its accuracy is an explicit hypothesis.
-/

section

namespace QuantumAlg.QuantumWalk

noncomputable section

private theorem unitaryIterates_distance_le {R : Register}
    (A B : UnitaryOperator R) (ψ : NormalizedVector R) (η : ℝ)
    (hstep : ∀ φ : HilbertVector R, ‖φ‖ = 1 → ‖A.applyVec φ - B.applyVec φ‖ ≤ η)
    (k : ℕ) :
    ‖(A ^ k).applyVec ψ - (B ^ k).applyVec ψ‖ ≤ (k : ℝ) * η := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', pow_succ', UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec]
      have hnorm : ‖(B ^ k).applyVec ψ‖ = 1 := by
        rw [UnitaryOperator.norm_applyVec, ψ.norm_eq_one]
      calc
        ‖A.applyVec ((A ^ k).applyVec ψ) - B.applyVec ((B ^ k).applyVec ψ)‖
            ≤ ‖A.applyVec ((A ^ k).applyVec ψ) - A.applyVec ((B ^ k).applyVec ψ)‖ +
                ‖A.applyVec ((B ^ k).applyVec ψ) - B.applyVec ((B ^ k).applyVec ψ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖(A ^ k).applyVec ψ - (B ^ k).applyVec ψ‖ +
                ‖A.applyVec ((B ^ k).applyVec ψ) - B.applyVec ((B ^ k).applyVec ψ)‖ := by
          rw [← UnitaryOperator.applyVec_sub, UnitaryOperator.norm_applyVec]
        _ ≤ (k : ℝ) * η + η := add_le_add ih (hstep _ hnorm)
        _ = ((k + 1 : ℕ) : ℝ) * η := by push_cast; ring

variable {n : ℕ}

/-- State distance grows by at most `η` per reflection pair. -/
public theorem state_distance_induction
    (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M : Finset (Fin (2 ^ n)))
    (approximation : UnitaryOperator (Qubits (n + n))) (η : ℝ)
    (happroximation : ∀ ψ : HilbertVector (Qubits (n + n)), ‖ψ‖ = 1 →
      ‖approximation.applyVec ψ - (idealRefUOp P).applyVec ψ‖ ≤ η)
    (k : ℕ) :
    ‖((approximation * refBglobalOp M) ^ k).applyVec (uniformEdgeState P) -
        ((idealRefUOp P * refBglobalOp M) ^ k).applyVec (uniformEdgeState P)‖ ≤
      (k : ℝ) * η := by
  apply unitaryIterates_distance_le
  intro ψ hψ
  rw [UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec]
  apply happroximation
  rw [UnitaryOperator.norm_applyVec, hψ]

/-- Pointwise reflection error reduces the marked squared amplitude by at most `2kη`. -/
public theorem quantum_walk_search_success_with_perturbation
    (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M : Finset (Fin (2 ^ n)))
    (hM : M.Nonempty) (approximation : UnitaryOperator (Qubits (n + n))) (η : ℝ)
    (happroximation : ∀ ψ : HilbertVector (Qubits (n + n)), ‖ψ‖ = 1 →
      ‖approximation.applyVec ψ - (idealRefUOp P).applyVec ψ‖ ≤ η)
    (k : ℕ) :
    Complex.normSq (inner ℂ (goodState P M)
        (((approximation * refBglobalOp M) ^ k).applyVec (uniformEdgeState P))) ≥
      Complex.normSq (inner ℂ (goodState P M)
        (((idealRefUOp P * refBglobalOp M) ^ k).applyVec (uniformEdgeState P))) -
          2 * (k : ℝ) * η := by
  have hactual :
      ‖((approximation * refBglobalOp M) ^ k).applyVec (uniformEdgeState P)‖ = 1 := by
    rw [UnitaryOperator.norm_applyVec, uniformEdgeState_norm]
  have hideal :
      ‖((idealRefUOp P * refBglobalOp M) ^ k).applyVec (uniformEdgeState P)‖ = 1 := by
    rw [UnitaryOperator.norm_applyVec, uniformEdgeState_norm]
  have h := success_probability_bound_of_dist
    (goodState P M)
    (((approximation * refBglobalOp M) ^ k).applyVec (uniformEdgeState P))
    (((idealRefUOp P * refBglobalOp M) ^ k).applyVec (uniformEdgeState P))
    ((k : ℝ) * η) (goodState_norm P M hM) hactual hideal
    (state_distance_induction P M approximation η happroximation k)
  simpa [mul_assoc] using h

end
end QuantumAlg.QuantumWalk

end
