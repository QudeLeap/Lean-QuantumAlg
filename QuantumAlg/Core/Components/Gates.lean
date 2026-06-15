/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Tensor
public import QuantumAlg.Core.Components.Kets
public import QuantumAlg.Util.Complex

/-!
# Named gates

The standard named gates as `Components` (concrete instances built on the
`Core` gate framework `QuantumAlg.Gate`):

- the one-qubit `H` [dW19, qcnotes.tex:712], `X`, `Z` [dW19, qcnotes.tex:675],
  `Y` [dW19, qcnotes.tex:8047], and the two-qubit `CNOT`
  [dW19, qcnotes.tex:741] (control = qubit 0 = most significant bit), with
  unitarity and basis-action lemmas, including `CNOT` on the two-qubit tensor
  basis;
- the rotation gates `rotZ φ = e^{iφZ}` [Lin22, hermfunc.tex:1112] (QSP
  processing convention) and the standard `rotY θ = R_Y(θ)`,
  `rotZStd φ = R_Z(φ) = e^{-iφZ/2}` [YYLW22, neurips_2022.tex:266], with their
  group/unitarity laws.

Kept out of `Core/Gate.lean` and `Core/Tensor.lean` so the base gate/tensor
framework carries no commitment to particular gates.
-/

@[expose] public section

namespace QuantumAlg

open PureState

noncomputable section

namespace Gate

/-! ## Pauli, Hadamard, and CNOT -/

/-- The Hadamard gate `H = (1/√2) [[1, 1], [1, −1]]`. -/
noncomputable def H : Gate 1 := invSqrt2 • !![1, 1; 1, -1]

/-- The Pauli-X (NOT) gate, as the basis permutation `|0⟩ ↔ |1⟩`. -/
def X : Gate 1 := ofPerm (Equiv.swap 0 1)

/-- The Pauli-Y gate `[[0, −i], [i, 0]]`. -/
def Y : Gate 1 := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli-Z gate `[[1, 0], [0, −1]]`. -/
def Z : Gate 1 := !![1, 0; 0, -1]

/-- The controlled-NOT gate on two qubits, control = qubit 0 (most
significant bit), target = qubit 1: the basis permutation `|10⟩ ↔ |11⟩`
(indices 2 ↔ 3). -/
def CNOT : Gate 2 := ofPerm (Equiv.swap 2 3)

theorem X_mem_unitaryGroup : X ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  ofPerm_mem_unitaryGroup _

theorem CNOT_mem_unitaryGroup : CNOT ∈ Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ :=
  ofPerm_mem_unitaryGroup _

theorem Y_mem_unitaryGroup : Y ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Y, Matrix.mul_apply, Matrix.star_apply]

theorem Z_mem_unitaryGroup : Z ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Z, Matrix.mul_apply, Matrix.star_apply]

/-- `H |0⟩ = |+⟩`. -/
@[simp]
theorem H_apply_ket0 : H.apply ket0 = ketPlus := by
  apply WithLp.ofLp_injective
  funext i
  change H.apply ket0 i = ketPlus i
  rw [ket0, apply_ket, ketPlus_apply]
  fin_cases i <;> simp [H, Matrix.smul_apply]

/-- `H |1⟩ = |−⟩`. -/
@[simp]
theorem H_apply_ket1 : H.apply ket1 = ketMinus := by
  apply WithLp.ofLp_injective
  funext i
  change H.apply ket1 i = ketMinus i
  rw [ket1, apply_ket, ketMinus_apply]
  fin_cases i <;> simp [H, Matrix.smul_apply]

/-- `CNOT` permutes the basis by swapping `|10⟩ ↔ |11⟩` (indices 2 ↔ 3). -/
theorem CNOT_apply_ket (x : Fin (2 ^ 2)) :
    CNOT.apply (ket x) = ket (Equiv.swap 2 3 x) := by
  rw [CNOT, ofPerm_apply_ket, Equiv.swap_inv]

/-- `X |0⟩ = |1⟩`. -/
@[simp]
theorem X_apply_ket0 : X.apply ket0 = ket1 := by
  rw [ket0, X, ofPerm_apply_ket, Equiv.swap_inv, ket1]
  congr 1

/-- `X |1⟩ = |0⟩`. -/
@[simp]
theorem X_apply_ket1 : X.apply ket1 = ket0 := by
  rw [ket1, X, ofPerm_apply_ket, Equiv.swap_inv, ket0]
  congr 1

/-- `Z |0⟩ = |0⟩`. -/
@[simp]
theorem Z_apply_ket0 : Z.apply ket0 = ket0 := by
  apply WithLp.ofLp_injective
  funext i
  change Z.apply ket0 i = ket0 i
  rw [ket0, apply_ket, ket_apply]
  fin_cases i <;> simp [Z]

/-- `Z |1⟩ = −|1⟩`. -/
@[simp]
theorem Z_apply_ket1 : Z.apply ket1 = -ket1 := by
  apply WithLp.ofLp_injective
  funext i
  change Z.apply ket1 i = (-ket1) i
  rw [ket1, apply_ket]
  fin_cases i <;> simp [Z, ket_apply]

/-- `H · H = 1`: the Hadamard gate is an involution. -/
theorem H_mul_H : H * H = 1 := by
  rw [H, smul_mul_smul_comm, invSqrt2_mul_self]
  have hmul : (!![1, 1; 1, -1] : Gate 1) * !![1, 1; 1, -1] = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
  rw [hmul, smul_smul]
  norm_num

/-- `H |+⟩ = |0⟩`. -/
@[simp]
theorem H_apply_ketPlus : H.apply ketPlus = ket0 := by
  rw [← H_apply_ket0, ← mul_apply, H_mul_H, one_apply]

/-- `H |−⟩ = |1⟩`. -/
@[simp]
theorem H_apply_ketMinus : H.apply ketMinus = ket1 := by
  rw [← H_apply_ket1, ← mul_apply, H_mul_H, one_apply]

theorem H_mem_unitaryGroup : H ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, H, star_smul, smul_mul_smul_comm,
    star_invSqrt2, invSqrt2_mul_self]
  have hstar : star (!![1, 1; 1, -1] : Gate 1) = !![1, 1; 1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
  have hmul : (!![1, 1; 1, -1] : Gate 1) * !![1, 1; 1, -1] = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
  rw [hstar, hmul, smul_smul]
  norm_num

/-! ## `CNOT` on the tensor basis

`CNOT` (control = qubit 0) on the four two-qubit basis states, in tensor
form. These let circuit proofs stay in per-qubit tensor language without
detouring through `Fin 4` index arithmetic. -/

/-- `CNOT |00⟩ = |00⟩`. -/
@[simp]
theorem CNOT_apply_ket0_tensor_ket0 :
    CNOT.apply (ket0.tensor ket0) = ket0.tensor ket0 := by
  rw [ket0, PureState.tensor_ket]
  change CNOT.apply (ket 0) = ket 0
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 0 = 0 from by decide]

/-- `CNOT |01⟩ = |01⟩`. -/
@[simp]
theorem CNOT_apply_ket0_tensor_ket1 :
    CNOT.apply (ket0.tensor ket1) = ket0.tensor ket1 := by
  rw [ket0, ket1, PureState.tensor_ket]
  change CNOT.apply (ket 1) = ket 1
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 1 = 1 from by decide]

/-- `CNOT |10⟩ = |11⟩`. -/
@[simp]
theorem CNOT_apply_ket1_tensor_ket0 :
    CNOT.apply (ket1.tensor ket0) = ket1.tensor ket1 := by
  rw [ket0, ket1, PureState.tensor_ket, PureState.tensor_ket]
  change CNOT.apply (ket 2) = ket 3
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 2 = 3 from by decide]

/-- `CNOT |11⟩ = |10⟩`. -/
@[simp]
theorem CNOT_apply_ket1_tensor_ket1 :
    CNOT.apply (ket1.tensor ket1) = ket1.tensor ket0 := by
  rw [ket0, ket1, PureState.tensor_ket, PureState.tensor_ket]
  change CNOT.apply (ket 3) = ket 2
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 3 = 2 from by decide]

end Gate

/-! ## Rotation gates (QSP / QNN conventions)

The processing/encoding/trainable rotations used by the single-qubit QSP and
quantum-neural-network conventions. They live directly in the `QuantumAlg`
namespace (not under `Gate`) and carry only their generic gate laws here; the
QSP-specific identities stay with each QSP convention. -/

/-- The processing rotation `e^{iφZ} = [[e^{iφ}, 0], [0, e^{-iφ}]]`
[Lin22, hermfunc.tex:1112]. -/
def rotZ (φ : ℝ) : Gate 1 :=
  !![Complex.exp (φ * Complex.I), 0; 0, Complex.exp (-(φ * Complex.I))]

theorem rotZ_mul_rotZ (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, ← Complex.exp_add]
  · congr 1; ring
  · congr 1; ring

@[simp]
theorem rotZ_zero : rotZ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ]

theorem rotZ_mem_unitaryGroup (φ : ℝ) :
    rotZ φ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
      conj_exp_neg_I, exp_I_mul_exp_neg_I, exp_neg_I_mul_exp_I]

theorem rotZ_comm (a b : ℝ) : rotZ a * rotZ b = rotZ b * rotZ a := by
  rw [rotZ_mul_rotZ, rotZ_mul_rotZ, add_comm]

theorem rotZ_neg_mul_rotZ (φ : ℝ) : rotZ (-φ) * rotZ φ = 1 := by
  rw [rotZ_mul_rotZ, neg_add_cancel, rotZ_zero]

theorem rotZ_mul_rotZ_neg (φ : ℝ) : rotZ φ * rotZ (-φ) = 1 := by
  rw [rotZ_mul_rotZ, add_neg_cancel, rotZ_zero]

/-- The standard `R_Y(θ) = [[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]]`
(the trainable gate of [YYLW22, neurips_2022.tex:266]). -/
def rotY (θ : ℝ) : Gate 1 :=
  !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
     (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]

/-- The standard `R_Z(φ) = e^{-iφZ/2} = diag(e^{-iφ/2}, e^{iφ/2})`
(the encoding and trainable `Z`-gate of [YYLW22]); equals `rotZ (-(φ/2))`. -/
def rotZStd (φ : ℝ) : Gate 1 := rotZ (-(φ / 2))

@[simp]
theorem rotZStd_zero : rotZStd 0 = 1 := by
  rw [rotZStd, show -(0 / 2 : ℝ) = 0 by norm_num, rotZ_zero]

theorem rotY_mem_unitaryGroup (θ : ℝ) :
    rotY θ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have hcs' : (Real.sin (θ / 2) : ℂ) ^ 2 + (Real.cos (θ / 2) : ℂ) ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq (θ / 2)
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) this
  rw [Matrix.mem_unitaryGroup_iff]
  unfold rotY
  generalize Real.cos (θ / 2) = c at hcs' ⊢
  generalize Real.sin (θ / 2) = s at hcs' ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
      try ring_nf
      try linear_combination hcs'

theorem rotZStd_mem_unitaryGroup (φ : ℝ) :
    rotZStd φ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  rotZ_mem_unitaryGroup _

end

end QuantumAlg
