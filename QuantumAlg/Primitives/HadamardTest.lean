/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Control
public import QuantumAlg.Core.Components.Kets
public import QuantumAlg.Core.Circuit

/-!
# The Hadamard test

The Hadamard test estimates `Re <psi| U |psi>` for a unitary `U`: prepare
`|0> ⊗ psi`, apply `H` on the control, the controlled `U`, and `H` again,
then measure the control qubit. The outcome probabilities are

`P(0) = (1 + Re <psi| U |psi>)/2`, `P(1) = (1 - Re <psi| U |psi>)/2`.

Pure-state normalization and gate unitarity are carried by the `PureState` and
`Gate` types themselves.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- The Hadamard test circuit `(H ⊗ I) · c-U · (H ⊗ I)`. -/
def hadamardTest (U : Gate (Qubits n)) : Gate (Qubits (1 + n)) :=
  Gate.tensor H (1 : Gate (Qubits n))
    * (Gate.controlled U * Gate.tensor H (1 : Gate (Qubits n)))

/-- The Hadamard test is unitary. -/
theorem hadamardTest_mem_unitaryGroup (U : Gate (Qubits n)) :
    (hadamardTest U : HilbertOperator (Qubits (1 + n)))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ :=
  (hadamardTest U).unitary

private theorem tensor_H_one_applyVec_ket0
    (psi : StateVector (Qubits n)) :
    HilbertOperator.applyVec
        (Gate.tensor H (1 : Gate (Qubits n)) : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi)
      = StateVector.tensor (ketPlus : StateVector (Qubits 1)) psi := by
  change HilbertOperator.applyVec
      (HilbertOperator.tensor (H : HilbertOperator (Qubits 1)) (1 : HilbertOperator (Qubits n)))
      (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi)
    = StateVector.tensor (ketPlus : StateVector (Qubits 1)) psi
  rw [HilbertOperator.tensor_applyVec_tensor]
  change StateVector.tensor (H.applyVec (ket0 : StateVector (Qubits 1)))
      (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n)) psi)
    = StateVector.tensor (ketPlus : StateVector (Qubits 1)) psi
  rw [H_applyVec_ket0, HilbertOperator.one_applyVec]

private theorem ketPlus_tensor (psi : StateVector (Qubits n)) :
    StateVector.tensor (ketPlus : StateVector (Qubits 1)) psi
      = invSqrt2 •
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi
          + StateVector.tensor (ket1 : StateVector (Qubits 1)) psi) := by
  simp [ketPlus, ketPlusVec, StateVector.smul_tensor, StateVector.add_tensor]

private theorem controlled_applyVec_ketPlus_tensor
    (U : Gate (Qubits n)) (psi : StateVector (Qubits n)) :
    HilbertOperator.applyVec (Gate.controlled U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ketPlus : StateVector (Qubits 1)) psi)
      = invSqrt2 •
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi
          + StateVector.tensor (ket1 : StateVector (Qubits 1)) (U.applyVec psi)) := by
  rw [ketPlus_tensor, HilbertOperator.applyVec_smul, HilbertOperator.applyVec_add,
    controlled_applyVec_ket0_tensor, controlled_applyVec_ket1_tensor]

private theorem tensor_H_one_finish
    (U : Gate (Qubits n)) (psi : PureState (Qubits n)) :
    HilbertOperator.applyVec
        (Gate.tensor H (1 : Gate (Qubits n)) : HilbertOperator (Qubits (1 + n)))
        (invSqrt2 •
          (StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n))
            + StateVector.tensor (ket1 : StateVector (Qubits 1))
              (U.applyVec (psi : StateVector (Qubits n)))))
      =
        (2 : ℂ)⁻¹ •
          (StateVector.tensor (ket0 : StateVector (Qubits 1))
              (psi + U.apply psi : StateVector (Qubits n))
            + StateVector.tensor (ket1 : StateVector (Qubits 1))
              (psi - U.apply psi : StateVector (Qubits n))) := by
  rw [HilbertOperator.applyVec_smul, HilbertOperator.applyVec_add,
    show
        (Gate.tensor H (1 : Gate (Qubits n)) :
          HilbertOperator (Qubits (1 + n))) =
          HilbertOperator.tensor (H : HilbertOperator (Qubits 1))
            (1 : HilbertOperator (Qubits n))
      from rfl,
    HilbertOperator.tensor_applyVec_tensor, HilbertOperator.tensor_applyVec_tensor]
  change invSqrt2 •
      (StateVector.tensor (H.applyVec (ket0 : StateVector (Qubits 1)))
          (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
            (psi : StateVector (Qubits n)))
        + StateVector.tensor (H.applyVec (ket1 : StateVector (Qubits 1)))
          (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
            (U.applyVec (psi : StateVector (Qubits n)))))
      =
        (2 : ℂ)⁻¹ •
          (StateVector.tensor (ket0 : StateVector (Qubits 1))
              (psi + U.apply psi : StateVector (Qubits n))
            + StateVector.tensor (ket1 : StateVector (Qubits 1))
              (psi - U.apply psi : StateVector (Qubits n)))
  rw [H_applyVec_ket0, H_applyVec_ket1, HilbertOperator.one_applyVec,
    HilbertOperator.one_applyVec]
  apply WithLp.ofLp_injective
  funext i
  simp [ketPlus, ketMinus, ketPlusVec, ketMinusVec, StateVector.tensor_apply,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, smul_add,
    smul_sub, smul_smul, invSqrt2_mul_self]
  ring

/-- Raw-vector pre-measurement state of the Hadamard test. -/
theorem hadamardTest_applyVec_ket0_tensor
    (U : Gate (Qubits n)) (psi : PureState (Qubits n)) :
    HilbertOperator.applyVec (hadamardTest U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n)))
      =
        (2 : ℂ)⁻¹ •
          (StateVector.tensor (ket0 : StateVector (Qubits 1))
              (psi + U.apply psi : StateVector (Qubits n))
            + StateVector.tensor (ket1 : StateVector (Qubits 1))
              (psi - U.apply psi : StateVector (Qubits n))) := by
  change HilbertOperator.applyVec
      ((Gate.tensor H (1 : Gate (Qubits n)) *
          (Gate.controlled U * Gate.tensor H (1 : Gate (Qubits n)))) :
        HilbertOperator (Qubits (1 + n)))
      (StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n))) = _
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, tensor_H_one_applyVec_ket0,
    controlled_applyVec_ketPlus_tensor, tensor_H_one_finish]

/-- The pre-measurement state of the Hadamard test. -/
theorem hadamardTest_apply_ket0_tensor (U : Gate (Qubits n)) (psi : PureState (Qubits n)) :
    ((hadamardTest U).apply (ket0.tensor psi) : StateVector (Qubits (1 + n)))
      =
        (2 : ℂ)⁻¹ •
          (StateVector.tensor (ket0 : StateVector (Qubits 1))
              (psi + U.apply psi : StateVector (Qubits n))
            + StateVector.tensor (ket1 : StateVector (Qubits 1))
              (psi - U.apply psi : StateVector (Qubits n))) := by
  change HilbertOperator.applyVec (hadamardTest U : HilbertOperator (Qubits (1 + n)))
      (StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n))) = _
  rw [hadamardTest_applyVec_ket0_tensor]

/-- Typed circuit witness for the Hadamard test. -/
def hadamardTestCircuit (U : Gate (Qubits n)) : Circuit (Qubits (1 + n)) :=
  Circuit.ofGate "hadamard-test" (hadamardTest U)
    { oracleQueries := 1, hadamardGates := 2, elementaryGates := 3, classicalOps := 0 } 3 1

/-- Hadamard test, outcome 0, in operator form. -/
theorem hadamardTest_probQubit0_zero {U : Gate (Qubits n)} (psi : PureState (Qubits n)) :
    probQubit0 ((hadamardTest U).apply (ket0.tensor psi)) 0
      = (1 + (inner ℂ psi (U.apply psi)).re) / 2 := by
  change StateVector.probQubit0
      (((hadamardTest U).apply (ket0.tensor psi)) : StateVector (Qubits (1 + n))) 0
      = (1 + (inner ℂ (psi : StateVector (Qubits n))
          ((U.apply psi : PureState (Qubits n)) : StateVector (Qubits n))).re) / 2
  rw [hadamardTest_apply_ket0_tensor, StateVector.probQubit0_smul,
    probQubit0_ket0_tensor_add_ket1_tensor,
    norm_add_sq (𝕜 := ℂ), psi.norm_eq_one, (U.apply psi).norm_eq_one]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

/-- **Hadamard test, outcome 0**. -/
theorem HadamardTest.main {U : Gate (Qubits n)} (psi : PureState (Qubits n)) :
    StateVector.probQubit0
        (Circuit.apply (hadamardTestCircuit U)
          (StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n)))) 0
      = (1 + (inner ℂ psi (U.apply psi)).re) / 2 := by
  rw [hadamardTestCircuit, Circuit.apply, Circuit.ofGate,
    Circuit.atom]
  change probQubit0 ((hadamardTest U).apply (ket0.tensor psi)) 0
      = (1 + (inner ℂ psi (U.apply psi)).re) / 2
  exact hadamardTest_probQubit0_zero psi

/-- **Hadamard test, outcome 1**. -/
theorem hadamardTest_probQubit0_one {U : Gate (Qubits n)} (psi : PureState (Qubits n)) :
    probQubit0 ((hadamardTest U).apply (ket0.tensor psi)) 1
      = (1 - (inner ℂ psi (U.apply psi)).re) / 2 := by
  change StateVector.probQubit0
      (((hadamardTest U).apply (ket0.tensor psi)) : StateVector (Qubits (1 + n))) 1
      = (1 - (inner ℂ (psi : StateVector (Qubits n))
          ((U.apply psi : PureState (Qubits n)) : StateVector (Qubits n))).re) / 2
  rw [hadamardTest_apply_ket0_tensor, StateVector.probQubit0_smul,
    probQubit1_ket0_tensor_add_ket1_tensor,
    norm_sub_sq (𝕜 := ℂ), psi.norm_eq_one, (U.apply psi).norm_eq_one]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

end

end QuantumAlg
