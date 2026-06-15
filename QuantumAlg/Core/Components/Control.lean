/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Gates

/-!
# Controlled gates

`Gate.controlled U` is the `(1 + n)`-qubit gate that applies the `n`-qubit
gate `U` on the target register exactly when the control qubit is in `|1⟩`,
and does nothing when it is in `|0⟩` [CEMM98, cemm6.tex:127]. As a matrix it
is the block decomposition `c-U = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`.

## Conventions

- The control is qubit 0, the most significant bit of the joint basis label
  (big-endian, matching `CNOT` and `QuantumAlg.prodEquiv`); the target
  register holds the remaining `n` qubits.
- The defining branches are `c-U (|0⟩ ⊗ ψ) = |0⟩ ⊗ ψ` and
  `c-U (|1⟩ ⊗ ψ) = |1⟩ ⊗ (U ψ)` [CEMM98, cemm6.tex:131].

## Main definitions

- `QuantumAlg.Gate.proj0` / `QuantumAlg.Gate.proj1` — the one-qubit basis
  projectors `|0⟩⟨0|` and `|1⟩⟨1|` (building blocks, not unitary).
- `QuantumAlg.Gate.controlled` — `c-U = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`;
  `controlled_apply_ket0_tensor` / `controlled_apply_ket1_tensor` compute
  the two control branches, `controlled_mem_unitaryGroup` gives unitarity,
  and `controlled_X` checks `c-X = CNOT`.

Pinned Mathlib API: `Matrix.mem_unitaryGroup_iff`,
`Matrix.conjTranspose_add`, `Matrix.conjTranspose_one`, `Matrix.mul_apply`,
`Matrix.one_apply`, `Matrix.conjTranspose_apply`.
-/

@[expose] public section

namespace QuantumAlg

namespace Gate

open PureState

noncomputable section

variable {n : ℕ}

/-- The one-qubit projector `|0⟩⟨0| = [[1, 0], [0, 0]]` (a building block for
block-diagonal constructions, not itself unitary). -/
def proj0 : Gate 1 := !![1, 0; 0, 0]

/-- The one-qubit projector `|1⟩⟨1| = [[0, 0], [0, 1]]`. -/
def proj1 : Gate 1 := !![0, 0; 0, 1]

@[simp]
theorem proj0_conjTranspose : proj0.conjTranspose = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.conjTranspose_apply]

@[simp]
theorem proj1_conjTranspose : proj1.conjTranspose = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.conjTranspose_apply]

theorem proj0_mul_proj0 : proj0 * proj0 = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply]

theorem proj0_mul_proj1 : proj0 * proj1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

theorem proj1_mul_proj0 : proj1 * proj0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

theorem proj1_mul_proj1 : proj1 * proj1 = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply]

theorem proj0_add_proj1 : proj0 + proj1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.add_apply]

@[simp]
theorem proj0_apply_ket0 : proj0.apply ket0 = ket0 := by
  apply WithLp.ofLp_injective
  funext i
  change proj0.apply ket0 i = ket0 i
  rw [ket0, apply_ket, ket_apply]
  fin_cases i <;> simp [proj0]

@[simp]
theorem proj0_apply_ket1 : proj0.apply ket1 = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change proj0.apply ket1 i = (0 : PureState 1) i
  rw [ket1, apply_ket]
  fin_cases i <;> simp [proj0]

@[simp]
theorem proj1_apply_ket0 : proj1.apply ket0 = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change proj1.apply ket0 i = (0 : PureState 1) i
  rw [ket0, apply_ket]
  fin_cases i <;> simp [proj1]

@[simp]
theorem proj1_apply_ket1 : proj1.apply ket1 = ket1 := by
  apply WithLp.ofLp_injective
  funext i
  change proj1.apply ket1 i = ket1 i
  rw [ket1, apply_ket, ket_apply]
  fin_cases i <;> simp [proj1]

/-- The controlled gate `c-U` [CEMM98, cemm6.tex:127]: apply `U` on the
target register when the control qubit (qubit 0, the most significant bit)
is `|1⟩`, do nothing when it is `|0⟩`. Matrix form:
`c-U = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`. -/
def controlled (U : Gate n) : Gate (1 + n) :=
  proj0.tensor 1 + proj1.tensor U

/-- On the `|0⟩` control branch `c-U` does nothing:
`c-U (|0⟩ ⊗ ψ) = |0⟩ ⊗ ψ`. -/
@[simp]
theorem controlled_apply_ket0_tensor (U : Gate n) (ψ : PureState n) :
    (controlled U).apply (ket0.tensor ψ) = ket0.tensor ψ := by
  rw [controlled, add_apply, tensor_apply_tensor, tensor_apply_tensor,
    proj0_apply_ket0, proj1_apply_ket0, one_apply, PureState.zero_tensor,
    add_zero]

/-- On the `|1⟩` control branch `c-U` applies `U`:
`c-U (|1⟩ ⊗ ψ) = |1⟩ ⊗ (U ψ)`. -/
@[simp]
theorem controlled_apply_ket1_tensor (U : Gate n) (ψ : PureState n) :
    (controlled U).apply (ket1.tensor ψ) = ket1.tensor (U.apply ψ) := by
  rw [controlled, add_apply, tensor_apply_tensor, tensor_apply_tensor,
    proj0_apply_ket1, proj1_apply_ket1, PureState.zero_tensor, zero_add]

/-- `c-U` is unitary whenever `U` is. -/
theorem controlled_mem_unitaryGroup {U : Gate n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    controlled U ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU ⊢
  rw [controlled, Matrix.conjTranspose_add, conjTranspose_tensor,
    conjTranspose_tensor, proj0_conjTranspose, proj1_conjTranspose,
    Matrix.conjTranspose_one, add_mul, mul_add, mul_add,
    tensor_mul_tensor, tensor_mul_tensor, tensor_mul_tensor,
    tensor_mul_tensor, hU]
  simp only [one_mul, mul_one, proj0_mul_proj0, proj0_mul_proj1,
    proj1_mul_proj0, proj1_mul_proj1, zero_tensor, add_zero, zero_add]
  rw [← add_tensor, proj0_add_proj1, one_tensor_one]

/-- Sanity check: the controlled Pauli-X gate is exactly `CNOT`. -/
theorem controlled_X : controlled X = CNOT := by
  have hX : ∀ i j : Fin (2 ^ 1), X i j = if i = Equiv.swap 0 1 j then 1 else 0 := by
    intro i j
    rw [← apply_ket X j i, X, ofPerm_apply_ket, Equiv.swap_inv, ket_apply]
  have hC : ∀ i j : Fin (2 ^ 2), CNOT i j = if i = Equiv.swap 2 3 j then 1 else 0 := by
    intro i j
    rw [← apply_ket CNOT j i, CNOT_apply_ket, ket_apply]
  ext i j
  rw [hC]
  fin_cases i <;> fin_cases j <;>
    simp +decide [controlled, Matrix.add_apply, tensor_apply, proj0, proj1,
      hX, Matrix.one_apply, prodEquiv, finProdFinEquiv, finCongr,
      Fin.divNat, Fin.modNat]

end

end Gate

end QuantumAlg
