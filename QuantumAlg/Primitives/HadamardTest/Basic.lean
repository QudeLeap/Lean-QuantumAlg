/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Gates.Hadamard.Operator
import all QuantumAlg.Components.Gates.Hadamard.Action
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Kets
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.State.Pure

/-!
# The Hadamard test

The Hadamard test estimates `Re <psi| U |psi>` for a unitary `U`: prepare
`|0> ⊗ psi`, apply `H` on the control, the controlled `U`, and `H` again,
then measure the control qubit. The outcome probabilities are

`P(0) = (1 + Re <psi| U |psi>)/2`, `P(1) = (1 - Re <psi| U |psi>)/2`.

State normalization and operator unitarity are carried by `NormalizedVector`
and `UnitaryOperator`.  The mathematical operator and Born probabilities are independent of
the native execution model; actual query access is specified by the execution layer.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

variable {n : ℕ}

/-- Metadata-free Hadamard action on the leading control qubit. -/
def hadamardTestHadamardOp (n : ℕ) : UnitaryOperator (Qubits (1 + n)) :=
  Gate.leadingHadamardOp n

/-- Metadata-free Hadamard-test unitary. -/
public def hadamardTest (U : UnitaryOperator (Qubits n)) :
    UnitaryOperator (Qubits (1 + n)) :=
  hadamardTestHadamardOp n *
    (UnitaryOperator.controlledQubits U * hadamardTestHadamardOp n)


private lemma tensor_H_one_applyVec_ket0
    (ψ : HilbertVector (Qubits n)) :
    (hadamardTestHadamardOp n).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ)
      = HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ := by
  change HilbertOperator.applyVec
      (HilbertOperator.tensor (HOp : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits n)))
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ)
    = HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ
  rw [HilbertOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor (HOp.applyVec (ket0 : HilbertVector (Qubits 1)))
      (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n)) ψ)
    = HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ
  have hH : HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) :=
    congrArg (fun v : NormalizedVector (Qubits 1) =>
      (v : HilbertVector (Qubits 1))) hadamardOperator_apply_ket0
  rw [hH, HilbertOperator.one_applyVec]

private lemma ketPlus_tensor (ψ : HilbertVector (Qubits n)) :
    HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ
      = invSqrt2 •
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ
          + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) ψ) := by
  rw [ketPlus_coe, HilbertVector.smul_tensor, HilbertVector.add_tensor]

private lemma controlled_applyVec_ketPlus_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits n)) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) ψ)
      = invSqrt2 •
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ
          + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (U.applyVec ψ)) := by
  rw [ketPlus_tensor, UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add,
    UnitaryOperator.controlledQubits_applyVec_ket0_tensor,
    UnitaryOperator.controlledQubits_applyVec_ket1_tensor]

private lemma tensor_H_one_finish
    (U : UnitaryOperator (Qubits n)) (ψ : NormalizedVector (Qubits n)) :
    (hadamardTestHadamardOp n).applyVec
        (invSqrt2 •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ψ : HilbertVector (Qubits n))
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              (U.applyVec (ψ : HilbertVector (Qubits n)))))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ)) := by
  rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add]
  change invSqrt2 •
      (HilbertOperator.applyVec
          (HilbertOperator.tensor (HOp : HilbertOperator (Qubits 1))
            (1 : HilbertOperator (Qubits n)))
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (ψ : HilbertVector (Qubits n)))
        + HilbertOperator.applyVec
          (HilbertOperator.tensor (HOp : HilbertOperator (Qubits 1))
            (1 : HilbertOperator (Qubits n)))
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
            (U.applyVec (ψ : HilbertVector (Qubits n))))) = _
  rw [HilbertOperator.tensor_applyVec_tensor, HilbertOperator.tensor_applyVec_tensor]
  change invSqrt2 •
      (HilbertVector.tensor (HOp.applyVec (ket0 : HilbertVector (Qubits 1)))
          (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
            (ψ : HilbertVector (Qubits n)))
        + HilbertVector.tensor (HOp.applyVec (ket1 : HilbertVector (Qubits 1)))
          (HilbertOperator.applyVec (1 : HilbertOperator (Qubits n))
            (U.applyVec (ψ : HilbertVector (Qubits n)))))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ))
  have hH0 : HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) :=
    congrArg (fun v : NormalizedVector (Qubits 1) =>
      (v : HilbertVector (Qubits 1))) hadamardOperator_apply_ket0
  have hH1 : HOp.applyVec (ket1 : HilbertVector (Qubits 1)) =
      (ketMinus : HilbertVector (Qubits 1)) :=
    congrArg (fun v : NormalizedVector (Qubits 1) =>
      (v : HilbertVector (Qubits 1))) hadamardOperator_apply_ket1
  rw [hH0, hH1, HilbertOperator.one_applyVec, HilbertOperator.one_applyVec]
  apply WithLp.ofLp_injective
  funext i
  simp [ketPlus_coe, ketMinus_coe, HilbertVector.tensor_apply,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, smul_add,
    smul_sub, smul_smul, invSqrt2_mul_self]
  ring

/-- Raw-vector proof of the Hadamard-test pre-measurement state. -/
private lemma hadamardTest_applyVec_ket0_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : NormalizedVector (Qubits n)) :
    (hadamardTest U).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ψ : HilbertVector (Qubits n)))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ)) := by
  rw [hadamardTest, UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec,
    tensor_H_one_applyVec_ket0, controlled_applyVec_ketPlus_tensor,
    tensor_H_one_finish]

/-- The pre-measurement state of the Hadamard test. -/
lemma hadamardTest_apply_ket0_tensor (U : UnitaryOperator (Qubits n))
    (ψ : NormalizedVector (Qubits n)) :
    (hadamardTest U).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ψ : HilbertVector (Qubits n)))
      =
        (2 : ℂ)⁻¹ •
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) + U.applyVec ψ)
            + HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              ((ψ : HilbertVector (Qubits n)) - U.applyVec ψ)) := by
  exact hadamardTest_applyVec_ket0_tensor U ψ

/-- Hadamard test, outcome 0, in operator form. -/
lemma hadamardTest_probQubit0_zero {U : UnitaryOperator (Qubits n)}
    (ψ : NormalizedVector (Qubits n)) :
    NormalizedVector.probQubit0
        ((hadamardTest U).apply (ket0.tensor ψ)) 0
      = (1 + (inner ℂ (ψ : HilbertVector (Qubits n)) (U.applyVec ψ)).re) / 2 := by
  change HilbertVector.leadingQubitWeight ((hadamardTest U).applyVec
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ψ : HilbertVector (Qubits n)))) 0 = _
  rw [hadamardTest_apply_ket0_tensor, HilbertVector.leadingQubitWeight_smul,
    leadingQubitWeight_ket0_tensor_add_ket1_tensor,
    norm_add_sq (𝕜 := ℂ), ψ.norm_eq_one]
  have hU_norm : ‖U.applyVec (ψ : HilbertVector (Qubits n))‖ = 1 := by
    rw [U.norm_applyVec, ψ.norm_eq_one]
  rw [hU_norm]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

/-- **Hadamard test, outcome 1**. -/
lemma hadamardTest_probQubit0_one {U : UnitaryOperator (Qubits n)}
    (ψ : NormalizedVector (Qubits n)) :
    NormalizedVector.probQubit0
        ((hadamardTest U).apply (ket0.tensor ψ)) 1
      = (1 - (inner ℂ (ψ : HilbertVector (Qubits n)) (U.applyVec ψ)).re) / 2 := by
  change HilbertVector.leadingQubitWeight ((hadamardTest U).applyVec
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ψ : HilbertVector (Qubits n)))) 1 = _
  rw [hadamardTest_apply_ket0_tensor, HilbertVector.leadingQubitWeight_smul,
    leadingQubitWeight_one_ket0_tensor_add_ket1_tensor,
    norm_sub_sq (𝕜 := ℂ), ψ.norm_eq_one]
  have hU_norm : ‖U.applyVec (ψ : HilbertVector (Qubits n))‖ = 1 := by
    rw [U.norm_applyVec, ψ.norm_eq_one]
  rw [hU_norm]
  have h2 : ‖(2 : ℂ)⁻¹‖ ^ 2 = (4 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [h2]
  simp only [RCLike.re_to_complex]
  ring

end

end QuantumAlg

end
