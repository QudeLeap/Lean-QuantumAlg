/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Decomposition

/-!
# QPP signal support

Single-qubit signal gates and controlled-eigenstate reductions used by QPP.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open PureState Module.End

noncomputable section

variable {n : ℕ}
variable {U : Gate (Qubits n)}

/-! ### The controlled-phase action of `c-U` on an eigenstate -/

/-- **Controlled-phase factorization on an eigenstate.** When the target holds
an eigenstate `U|u⟩ = e^{iθ}|u⟩`, the controlled unitary `c-U` acts on
`|ψ⟩ ⊗ |u⟩` as the controlled-phase gate on the ancilla, leaving the
eigenstate fixed [WZYW23, arxiv_v3.tex:641]. -/
theorem controlled_apply_eigenstate_phaseVec
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (ψ : StateVector (Qubits 1)) :
    (Gate.controlled U).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n))) =
      StateVector.tensor ((phaseGate θ).applyVec ψ)
        (u : StateVector (Qubits n)) := by
  calc
    (Gate.controlled U).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n)))
        =
      (Gate.controlled U).applyVec
        (StateVector.tensor
          ((ψ 0) • (ket0 : StateVector (Qubits 1)) + (ψ 1) • (ket1 : StateVector (Qubits 1)))
          (u : StateVector (Qubits n))) := by
        exact congrArg
          (fun v : StateVector (Qubits 1) =>
            (Gate.controlled U).applyVec (StateVector.tensor v (u : StateVector (Qubits n))))
          (single_qubit_vec_decomp ψ)
    _ =
      StateVector.tensor
        ((ψ 0) • (ket0 : StateVector (Qubits 1)) +
          (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : StateVector (Qubits 1)))
        (u : StateVector (Qubits n)) := by
        rw [GeneralizedPhaseKickback.main U u θ hu (ψ 0) (ψ 1)]
    _ =
      StateVector.tensor ((phaseGate θ).applyVec ψ)
        (u : StateVector (Qubits n)) := by
        rw [phaseGate_applyVec]

theorem controlled_apply_eigenstate_phase
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (ψ : PureState (Qubits 1)) :
    (Gate.controlled U).applyVec
        (StateVector.tensor (ψ : StateVector (Qubits 1)) (u : StateVector (Qubits n))) =
      StateVector.tensor ((phaseGate θ).applyVec (ψ : StateVector (Qubits 1)))
        (u : StateVector (Qubits n)) :=
  controlled_apply_eigenstate_phaseVec U u θ hu (ψ : StateVector (Qubits 1))

/-- If `U|u⟩ = e^{iθ}|u⟩`, then `U†|u⟩ = e^{-iθ}|u⟩`. This is the
adjoint branch used by Wang's alternating QPP convention
[WZYW23, arxiv_v3.tex:601-609,641]. -/
theorem QPP.conjTranspose_apply_eigenstate_phaseVec
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n))) :
    U.conjTranspose.applyVec (u : StateVector (Qubits n)) =
      Complex.exp (-((θ : ℝ) * Complex.I)) • (u : StateVector (Qubits n)) := by
  have hpre :
      Complex.exp (-((θ : ℝ) * Complex.I)) •
          U.applyVec (u : StateVector (Qubits n)) =
        (u : StateVector (Qubits n)) := by
    rw [hu, smul_smul]
    simp [exp_neg_I_mul_exp_I θ]
  calc
    U.conjTranspose.applyVec (u : StateVector (Qubits n))
        = U.conjTranspose.applyVec
            (Complex.exp (-((θ : ℝ) * Complex.I)) •
              U.applyVec (u : StateVector (Qubits n))) := by
          rw [hpre]
    _ = Complex.exp (-((θ : ℝ) * Complex.I)) •
          U.conjTranspose.applyVec (U.applyVec (u : StateVector (Qubits n))) := by
          rw [Gate.applyVec_smul]
    _ = Complex.exp (-((θ : ℝ) * Complex.I)) •
          (u : StateVector (Qubits n)) := by
          rw [Gate.conjTranspose_applyVec_applyVec]

/-- On the zero-control branch of Wang's alternating QPP word, `U†` contributes
the eigenphase `e^{-iθ}` [WZYW23, arxiv_v3.tex:601-609,641]. -/
theorem QPP.controlledOnZero_conjTranspose_apply_eigenstate_ket0
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n))) :
    (Gate.controlledOnZero U.conjTranspose).applyVec
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) =
      StateVector.tensor (ket0 : StateVector (Qubits 1))
        (Complex.exp (-((θ : ℝ) * Complex.I)) • (u : StateVector (Qubits n))) := by
  change HilbertOperator.applyVec
      (Gate.controlledOnZero U.conjTranspose : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) =
      StateVector.tensor (ket0 : StateVector (Qubits 1))
        (Complex.exp (-((θ : ℝ) * Complex.I)) • (u : StateVector (Qubits n)))
  rw [Gate.controlledOnZero_applyVec_ket0_tensor]
  rw [QPP.conjTranspose_apply_eigenstate_phaseVec U u θ hu]

/-- On the one-control branch of Wang's zero-controlled `U†` block, the target
eigenstate is unchanged [WZYW23, arxiv_v3.tex:601-609]. -/
theorem QPP.controlledOnZero_conjTranspose_apply_eigenstate_ket1
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) :
    (Gate.controlledOnZero U.conjTranspose).applyVec
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) =
      StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n)) := by
  change HilbertOperator.applyVec
      (Gate.controlledOnZero U.conjTranspose : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) =
      StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n))
  rw [Gate.controlledOnZero_applyVec_ket1_tensor]

/-- The zero-control `U†` block acts as `diag(e^{-iθ},1)` on the ancilla when
the target is an eigenstate of `U` [WZYW23, arxiv_v3.tex:601-609,641]. -/
theorem QPP.controlledOnZero_conjTranspose_apply_eigenstate_phaseVec
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (ψ : StateVector (Qubits 1)) :
    (Gate.controlledOnZero U.conjTranspose).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n))) =
      StateVector.tensor ((phaseGateOnZero (-θ)).applyVec ψ)
        (u : StateVector (Qubits n)) := by
  let G : HilbertOperator (Qubits (1 + n)) :=
    (Gate.controlledOnZero U.conjTranspose : HilbertOperator (Qubits (1 + n)))
  have h0 :
      HilbertOperator.applyVec G
          (StateVector.tensor (ket0 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) =
        StateVector.tensor (ket0 : StateVector (Qubits 1))
          (Complex.exp (-((θ : ℝ) * Complex.I)) • (u : StateVector (Qubits n))) := by
    dsimp [G]
    simpa [Gate.applyVec] using
      QPP.controlledOnZero_conjTranspose_apply_eigenstate_ket0 U u θ hu
  have h1 :
      HilbertOperator.applyVec G
          (StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) =
        StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n)) := by
    dsimp [G]
    simp
  change HilbertOperator.applyVec G
        (StateVector.tensor ψ (u : StateVector (Qubits n))) =
      StateVector.tensor ((phaseGateOnZero (-θ)).applyVec ψ)
        (u : StateVector (Qubits n))
  calc
    HilbertOperator.applyVec G
        (StateVector.tensor ψ (u : StateVector (Qubits n)))
        =
      HilbertOperator.applyVec G
        (StateVector.tensor
          ((ψ 0) • (ket0 : StateVector (Qubits 1)) + (ψ 1) • (ket1 : StateVector (Qubits 1)))
          (u : StateVector (Qubits n))) := by
        exact congrArg
          (fun v : StateVector (Qubits 1) =>
            HilbertOperator.applyVec G (StateVector.tensor v (u : StateVector (Qubits n))))
          (single_qubit_vec_decomp ψ)
    _ =
      HilbertOperator.applyVec G
        ((ψ 0) •
            StateVector.tensor (ket0 : StateVector (Qubits 1)) (u : StateVector (Qubits n)) +
          (ψ 1) •
            StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) := by
        rw [StateVector.add_tensor, StateVector.smul_tensor, StateVector.smul_tensor]
    _ =
      (ψ 0) • HilbertOperator.applyVec G
          (StateVector.tensor (ket0 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) +
        (ψ 1) • HilbertOperator.applyVec G
          (StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n))) := by
        rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
          HilbertOperator.applyVec_smul]
    _ =
      (ψ 0) • StateVector.tensor (ket0 : StateVector (Qubits 1))
          (Complex.exp (-((θ : ℝ) * Complex.I)) • (u : StateVector (Qubits n))) +
        (ψ 1) •
          StateVector.tensor (ket1 : StateVector (Qubits 1)) (u : StateVector (Qubits n)) := by
        rw [h0, h1]
    _ =
      StateVector.tensor ((phaseGateOnZero (-θ)).applyVec ψ)
        (u : StateVector (Qubits n)) := by
        rw [phaseGateOnZero_applyVec]
        simp [StateVector.add_tensor, StateVector.smul_tensor, StateVector.tensor_smul,
          smul_smul, mul_comm]

/-- **Eigenstate reduction of `c-U` to the QSP signal.** On an eigenstate
`U|u⟩ = e^{iθ}|u⟩`, the controlled unitary acts as the QSP encoding gate at
signal `θ`, up to the global phase `e^{iθ/2}`:
`c-U (|ψ⟩ ⊗ |u⟩) = (e^{iθ/2} · R_Z(θ)|ψ⟩) ⊗ |u⟩` [WZYW23, arxiv_v3.tex:641]. -/
theorem QPP.eigenstate_reductionVec
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (ψ : StateVector (Qubits 1)) :
    (Gate.controlled U).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n)))
      = StateVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStd θ).applyVec ψ)
          (u : StateVector (Qubits n)) := by
  rw [controlled_apply_eigenstate_phaseVec U u θ hu, phaseGate_applyVec_eq_smul_rotZStd]

theorem QPP.eigenstate_reduction
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (ψ : PureState (Qubits 1)) :
    (Gate.controlled U).applyVec
        (StateVector.tensor (ψ : StateVector (Qubits 1)) (u : StateVector (Qubits n)))
      = StateVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStd θ).applyVec (ψ : StateVector (Qubits 1)))
          (u : StateVector (Qubits n)) :=
  QPP.eigenstate_reductionVec U u θ hu
    (ψ : StateVector (Qubits 1))

namespace QPP.Pair

/-- Staged pair-level form of the controlled-signal eigenstate reduction. -/
theorem eigenstate_reduction
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (ψ : PureState (Qubits 1)) :
    (Gate.controlled U).applyVec
        (StateVector.tensor (ψ : StateVector (Qubits 1)) (u : StateVector (Qubits n)))
      = StateVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStd θ).applyVec (ψ : StateVector (Qubits 1)))
          (u : StateVector (Qubits n)) :=
  QuantumAlg.QSP.MultiQubit.QPP.eigenstate_reduction U u θ hu ψ

end QPP.Pair



end

end QSP.MultiQubit

end QuantumAlg
