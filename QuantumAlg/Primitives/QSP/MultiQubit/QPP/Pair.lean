/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Decomposition
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Components.Gates.PhaseOperator.Rotation
import all QuantumAlg.Components.Kets.Decomposition
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# QPP signal support

Single-qubit signal gates and controlled-eigenstate reductions used by QPP.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open NormalizedVector Module.End

noncomputable section

variable {n : ℕ}
variable {U : UnitaryOperator (Qubits n)}

private theorem phaseGateOp_applyVec (θ : ℝ)
    (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOp θ).applyVec ψ =
      (ψ 0) • (ket0 : HilbertVector (Qubits 1)) +
        (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) •
          (ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [UnitaryOperator.applyVec, HilbertOperator.applyVec_apply,
      phaseGateOp, NormalizedVector.ket0, NormalizedVector.ket1,
      NormalizedVector.ket_apply, PiLp.add_apply, PiLp.smul_apply]

private theorem phaseGateOnZeroOp_applyVec (θ : ℝ)
    (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOnZeroOp θ).applyVec ψ =
      (Complex.exp ((θ : ℝ) * Complex.I) * ψ 0) •
          (ket0 : HilbertVector (Qubits 1)) +
        (ψ 1) • (ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [UnitaryOperator.applyVec, HilbertOperator.applyVec_apply,
      phaseGateOnZeroOp, NormalizedVector.ket0, NormalizedVector.ket1,
      NormalizedVector.ket_apply, PiLp.add_apply, PiLp.smul_apply]

private theorem phaseGateOp_applyVec_eq_smul_rotZStdOp (θ : ℝ)
    (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOp θ).applyVec ψ =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ).applyVec ψ := by
  change HilbertOperator.applyVec (phaseGateOp θ : HilbertOperator (Qubits 1)) ψ =
    Complex.exp ((θ / 2 : ℝ) * Complex.I) •
      HilbertOperator.applyVec (rotZStdOp θ : HilbertOperator (Qubits 1)) ψ
  rw [phaseGateOp_signal, HilbertOperator.smul_applyVec]

/-! ### The controlled-phase action of `c-U` on an eigenstate -/

/-- **Controlled-phase factorization on an eigenstate.** When the target holds
an eigenstate `U|u⟩ = e^{iθ}|u⟩`, the controlled unitary `c-U` acts on
`|ψ⟩ ⊗ |u⟩` as the controlled-phase gate on the ancilla, leaving the
eigenstate fixed [WZYW23, arxiv_v3.tex:641]. -/
theorem controlled_apply_eigenstate_phaseVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (ψ : HilbertVector (Qubits 1)) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor ((phaseGateOp θ).applyVec ψ)
        (u : HilbertVector (Qubits n)) := by
  calc
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n)))
        =
      (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor
          ((ψ 0) • (ket0 : HilbertVector (Qubits 1)) + (ψ 1) • (ket1 : HilbertVector (Qubits 1)))
          (u : HilbertVector (Qubits n))) := by
        exact congrArg
          (fun v : HilbertVector (Qubits 1) =>
            (UnitaryOperator.controlledQubits U).applyVec
              (HilbertVector.tensor v (u : HilbertVector (Qubits n))))
          (single_qubit_vec_decomp ψ)
    _ =
      HilbertVector.tensor
        ((ψ 0) • (ket0 : HilbertVector (Qubits 1)) +
          (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : HilbertVector (Qubits 1)))
        (u : HilbertVector (Qubits n)) := by
        rw [GeneralizedPhaseKickback.eigenvalue_action U u θ hu (ψ 0) (ψ 1)]
    _ =
      HilbertVector.tensor ((phaseGateOp θ).applyVec ψ)
        (u : HilbertVector (Qubits n)) := by
        rw [phaseGateOp_applyVec]

theorem controlled_apply_eigenstate_phase
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (ψ : NormalizedVector (Qubits 1)) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor (ψ : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor ((phaseGateOp θ).applyVec (ψ : HilbertVector (Qubits 1)))
        (u : HilbertVector (Qubits n)) :=
  controlled_apply_eigenstate_phaseVec U u θ hu (ψ : HilbertVector (Qubits 1))

/-- If `U|u⟩ = e^{iθ}|u⟩`, then `U†|u⟩ = e^{-iθ}|u⟩`. This is the
adjoint branch used by Wang's alternating QPP convention
[WZYW23, arxiv_v3.tex:601-609,641]. -/
theorem QPP.conjTranspose_apply_eigenstate_phaseVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n))) :
    U.dagger.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp (-((θ : ℝ) * Complex.I)) • (u : HilbertVector (Qubits n)) := by
  have hpre :
      Complex.exp (-((θ : ℝ) * Complex.I)) •
          U.applyVec (u : HilbertVector (Qubits n)) =
        (u : HilbertVector (Qubits n)) := by
    rw [hu, smul_smul]
    simp [exp_neg_I_mul_exp_I θ]
  calc
    U.dagger.applyVec (u : HilbertVector (Qubits n))
        = U.dagger.applyVec
            (Complex.exp (-((θ : ℝ) * Complex.I)) •
              U.applyVec (u : HilbertVector (Qubits n))) := by
          rw [hpre]
    _ = Complex.exp (-((θ : ℝ) * Complex.I)) •
          U.dagger.applyVec (U.applyVec (u : HilbertVector (Qubits n))) := by
          rw [UnitaryOperator.applyVec_smul]
    _ = Complex.exp (-((θ : ℝ) * Complex.I)) •
          (u : HilbertVector (Qubits n)) := by
          change Complex.exp (-((θ : ℝ) * Complex.I)) •
              HilbertOperator.applyVec
                ((U : HilbertOperator (Qubits n)).conjTranspose)
                (HilbertOperator.applyVec (U : HilbertOperator (Qubits n))
                  (u : HilbertVector (Qubits n))) = _
          rw [← HilbertOperator.mul_applyVec]
          rw [show (U : HilbertOperator (Qubits n)).conjTranspose *
              (U : HilbertOperator (Qubits n)) = 1 by
            rw [← Matrix.star_eq_conjTranspose]
            exact Matrix.mem_unitaryGroup_iff'.mp U.property]
          rw [HilbertOperator.one_applyVec]

/-- On the zero-control branch of Wang's alternating QPP word, `U†` contributes
the eigenphase `e^{-iθ}` [WZYW23, arxiv_v3.tex:601-609,641]. -/
theorem QPP.controlledOnZero_conjTranspose_apply_eigenstate_ket0
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n))) :
    (UnitaryOperator.controlledQubitsOnZero U.dagger).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (Complex.exp (-((θ : ℝ) * Complex.I)) • (u : HilbertVector (Qubits n))) := by
  rw [UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor]
  rw [QPP.conjTranspose_apply_eigenstate_phaseVec U u θ hu]

/-- On the one-control branch of Wang's zero-controlled `U†` block, the target
eigenstate is unchanged [WZYW23, arxiv_v3.tex:601-609]. -/
theorem QPP.controlledOnZero_conjTranspose_apply_eigenstate_ket1
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) :
    (UnitaryOperator.controlledQubitsOnZero U.dagger).applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n)) := by
  rw [UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor]

/-- The zero-control `U†` block acts as `diag(e^{-iθ},1)` on the ancilla when
the target is an eigenstate of `U` [WZYW23, arxiv_v3.tex:601-609,641]. -/
theorem QPP.controlledOnZero_conjTranspose_apply_eigenstate_phaseVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (ψ : HilbertVector (Qubits 1)) :
    (UnitaryOperator.controlledQubitsOnZero U.dagger).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor ((phaseGateOnZeroOp (-θ)).applyVec ψ)
        (u : HilbertVector (Qubits n)) := by
  let G : HilbertOperator (Qubits (1 + n)) :=
    (UnitaryOperator.controlledQubitsOnZero U.dagger :
      HilbertOperator (Qubits (1 + n)))
  have h0 :
      HilbertOperator.applyVec G
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n))) =
        HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (Complex.exp (-((θ : ℝ) * Complex.I)) • (u : HilbertVector (Qubits n))) := by
    dsimp [G]
    simpa [UnitaryOperator.applyVec] using
      QPP.controlledOnZero_conjTranspose_apply_eigenstate_ket0 U u θ hu
  have h1 :
      HilbertOperator.applyVec G
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n))) =
        HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n)) := by
    dsimp [G]
    simpa [UnitaryOperator.applyVec] using
      QPP.controlledOnZero_conjTranspose_apply_eigenstate_ket1 U u
  change HilbertOperator.applyVec G
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor ((phaseGateOnZeroOp (-θ)).applyVec ψ)
        (u : HilbertVector (Qubits n))
  calc
    HilbertOperator.applyVec G
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n)))
        =
      HilbertOperator.applyVec G
        (HilbertVector.tensor
          ((ψ 0) • (ket0 : HilbertVector (Qubits 1)) + (ψ 1) • (ket1 : HilbertVector (Qubits 1)))
          (u : HilbertVector (Qubits n))) := by
        exact congrArg
          (fun v : HilbertVector (Qubits 1) =>
            HilbertOperator.applyVec G (HilbertVector.tensor v (u : HilbertVector (Qubits n))))
          (single_qubit_vec_decomp ψ)
    _ =
      HilbertOperator.applyVec G
        ((ψ 0) •
            HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n)) +
          (ψ 1) •
            HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) := by
        rw [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.smul_tensor]
    _ =
      (ψ 0) • HilbertOperator.applyVec G
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n))) +
        (ψ 1) • HilbertOperator.applyVec G
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
            (u : HilbertVector (Qubits n))) := by
        rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
          HilbertOperator.applyVec_smul]
    _ =
      (ψ 0) • HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (Complex.exp (-((θ : ℝ) * Complex.I)) • (u : HilbertVector (Qubits n))) +
        (ψ 1) •
          HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
            (u : HilbertVector (Qubits n)) := by
        rw [h0, h1]
    _ =
      HilbertVector.tensor ((phaseGateOnZeroOp (-θ)).applyVec ψ)
        (u : HilbertVector (Qubits n)) := by
        rw [phaseGateOnZeroOp_applyVec]
        simp [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.tensor_smul,
          smul_smul, mul_comm]

/-- **Eigenstate reduction of `c-U` to the QSP signal.** On an eigenstate
`U|u⟩ = e^{iθ}|u⟩`, the controlled unitary acts as the QSP encoding gate at
signal `θ`, up to the global phase `e^{iθ/2}`:
`c-U (|ψ⟩ ⊗ |u⟩) = (e^{iθ/2} · R_Z(θ)|ψ⟩) ⊗ |u⟩` [WZYW23, arxiv_v3.tex:641]. -/
theorem QPP.eigenstate_reductionVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (ψ : HilbertVector (Qubits 1)) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n)))
      = HilbertVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStdOp θ).applyVec ψ)
          (u : HilbertVector (Qubits n)) := by
  rw [controlled_apply_eigenstate_phaseVec U u θ hu,
    phaseGateOp_applyVec_eq_smul_rotZStdOp]

theorem QPP.eigenstate_reduction
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (ψ : NormalizedVector (Qubits 1)) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor (ψ : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n)))
      = HilbertVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStdOp θ).applyVec (ψ : HilbertVector (Qubits 1)))
          (u : HilbertVector (Qubits n)) :=
  QPP.eigenstate_reductionVec U u θ hu
    (ψ : HilbertVector (Qubits 1))

namespace QPP.Pair

/-- Staged pair-level form of the controlled-signal eigenstate reduction. -/
theorem eigenstate_reduction
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (ψ : NormalizedVector (Qubits 1)) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor (ψ : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n)))
      = HilbertVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStdOp θ).applyVec (ψ : HilbertVector (Qubits 1)))
          (u : HilbertVector (Qubits n)) :=
  QuantumAlg.QSP.MultiQubit.QPP.eigenstate_reduction U u θ hu ψ

end QPP.Pair



end

end QSP.MultiQubit

end QuantumAlg

end
