/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Control
public import QuantumAlg.Core.Components.Kets

/-!
# The Hadamard test

The Hadamard test estimates `Re ⟨ψ| U |ψ⟩` for a unitary `U`: prepare
`|0⟩ ⊗ ψ`, apply `H` on the control, the controlled `U`, and `H` again,
then measure the control qubit. The outcome probabilities are

`P(0) = (1 + Re ⟨ψ| U |ψ⟩)/2`, `P(1) = (1 − Re ⟨ψ| U |ψ⟩)/2`.

This is the abstract form of the single-particle interferometer of
[CEMM98, cemm6.tex:93], whose detector probabilities `(1 ± cos φ)/2`
are the eigenstate case `U |ψ⟩ = e^{iφ} |ψ⟩`; instantiated with a
register-swap unitary it becomes the SWAP test of
[BCWdW01, main.tex:291] (see `QuantumAlg/Primitives/SwapTest.lean`).

## Conventions

- The control is qubit 0 (most significant, big-endian), matching
  `Gate.controlled`; the target register holds the remaining `n` qubits.
- Probabilities refer to measuring the control qubit only, in the
  computational basis (`PureState.probQubit0`).

## Main results

- `QuantumAlg.hadamardTest U` — the circuit `(H ⊗ I) · c-U · (H ⊗ I)`.
- `QuantumAlg.hadamardTest_apply_ket0_tensor` — the pre-measurement state
  `(|0⟩ ⊗ (ψ + Uψ) + |1⟩ ⊗ (ψ − Uψ))/2`.
- `QuantumAlg.hadamardTest_probQubit0_zero` / `_one` — the outcome
  probabilities, as `Re`-of-inner-product formulas.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- The Hadamard test circuit `(H ⊗ I) · c-U · (H ⊗ I)`: Hadamard on the
control qubit, controlled `U`, Hadamard again [CEMM98, cemm6.tex:93;
BCWdW01, main.tex:291]. -/
def hadamardTest (U : Gate n) : Gate (1 + n) :=
  Gate.tensor H (1 : Gate n)
    * (Gate.controlled U * Gate.tensor H (1 : Gate n))

/-- The Hadamard test is unitary whenever `U` is. -/
theorem hadamardTest_mem_unitaryGroup {U : Gate n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    hadamardTest U ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ := by
  have hH1 : Gate.tensor H (1 : Gate n)
      ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ :=
    tensor_mem_unitaryGroup H_mem_unitaryGroup (one_mem _)
  exact mul_mem hH1 (mul_mem (controlled_mem_unitaryGroup hU) hH1)

/-- The pre-measurement state of the Hadamard test:
`(H ⊗ I) c-U (H ⊗ I) (|0⟩ ⊗ ψ) = (|0⟩ ⊗ (ψ + Uψ) + |1⟩ ⊗ (ψ − Uψ))/2`. -/
theorem hadamardTest_apply_ket0_tensor (U : Gate n) (ψ : PureState n) :
    (hadamardTest U).apply (ket0.tensor ψ)
      = (2 : ℂ)⁻¹ • (ket0.tensor (ψ + U.apply ψ)
          + ket1.tensor (ψ - U.apply ψ)) := by
  rw [hadamardTest, Gate.mul_apply, Gate.mul_apply]
  simp only [Gate.tensor_apply_tensor, H_apply_ket0, H_apply_ket1,
    Gate.one_apply, ketPlus, ketMinus, PureState.smul_tensor,
    PureState.add_tensor, PureState.sub_tensor, PureState.tensor_add,
    PureState.tensor_sub, Gate.apply_smul, Gate.apply_add,
    controlled_apply_ket0_tensor, controlled_apply_ket1_tensor,
    smul_add, smul_sub, smul_smul, invSqrt2_mul_self]
  module

/-- **Hadamard test, outcome 0** [CEMM98, cemm6.tex:93]: for normalized
`ψ` and unitary `U`, the control reads `0` with probability
`(1 + Re ⟨ψ| U |ψ⟩)/2`. -/
theorem hadamardTest_probQubit0_zero {U : Gate n} (ψ : PureState n)
    (hψ : ‖ψ‖ = 1) (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    probQubit0 ((hadamardTest U).apply (ket0.tensor ψ)) 0
      = (1 + (inner ℂ ψ (U.apply ψ)).re) / 2 := by
  rw [hadamardTest_apply_ket0_tensor, probQubit0_smul,
    probQubit0_ket0_tensor_add_ket1_tensor,
    norm_add_sq (𝕜 := ℂ), hψ, norm_apply_of_mem_unitaryGroup hU, hψ]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

/-- **Hadamard test, outcome 1** [CEMM98, cemm6.tex:93]: the control
reads `1` with probability `(1 − Re ⟨ψ| U |ψ⟩)/2`. -/
theorem hadamardTest_probQubit0_one {U : Gate n} (ψ : PureState n)
    (hψ : ‖ψ‖ = 1) (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    probQubit0 ((hadamardTest U).apply (ket0.tensor ψ)) 1
      = (1 - (inner ℂ ψ (U.apply ψ)).re) / 2 := by
  rw [hadamardTest_apply_ket0_tensor, probQubit0_smul,
    probQubit1_ket0_tensor_add_ket1_tensor,
    norm_sub_sq (𝕜 := ℂ), hψ, norm_apply_of_mem_unitaryGroup hU, hψ]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

end

end QuantumAlg
