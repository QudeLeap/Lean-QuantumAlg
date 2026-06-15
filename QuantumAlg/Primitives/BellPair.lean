/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Gates

/-!
# Bell pair (EPR pair) and its preparation

The Bell state (EPR-pair) `(|00⟩ + |11⟩)/√2` [dW19, qcnotes.tex:622] is
prepared from `|00⟩` by a Hadamard on qubit 0 followed by a CNOT with
control qubit 0:

`CNOT · (H ⊗ I) · |00⟩ = (|00⟩ + |11⟩)/√2`.

This is a `Primitives` module: the Bell pair is a reusable resource state, so
it lives below `Algorithms/` and is shared by the protocols that consume it
(superdense coding, teleportation) without those algorithms importing one
another. The registered `bell-state-prep` target is `bell_state_prep` here.

## Main results

- `QuantumAlg.bell` — the Bell state, as a `PureState 2`.
- `QuantumAlg.bell_state_prep` — the preparation-circuit equality.
- `QuantumAlg.bell_eq_tensor` — the Bell state in per-qubit tensor form.
- `QuantumAlg.norm_bell` — the Bell state is normalized.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The Bell state (EPR-pair) `(|00⟩ + |11⟩)/√2` [dW19, qcnotes.tex:622].
In the big-endian basis labelling, `|00⟩ = ket 0` and `|11⟩ = ket 3`. -/
def bell : PureState 2 := invSqrt2 • (ket 0 + ket 3)

/-- The Bell state in per-qubit tensor form: `(|0⟩⊗|0⟩ + |1⟩⊗|1⟩)/√2`. -/
theorem bell_eq_tensor :
    bell = invSqrt2 • (ket0.tensor ket0 + ket1.tensor ket1) := by
  rw [bell, ket0, ket1, PureState.tensor_ket, PureState.tensor_ket]
  change invSqrt2 • (ket 0 + ket 3) = invSqrt2 • (ket 0 + ket 3)
  rfl

/-- Bell-state preparation: a Hadamard on qubit 0 followed by a CNOT
(control = qubit 0) turns `|00⟩` into the Bell state. -/
theorem bell_state_prep :
    CNOT.apply ((H.tensor (1 : Gate 1)).apply (ket0.tensor ket0)) = bell := by
  rw [Gate.tensor_apply_tensor, H_apply_ket0, Gate.one_apply, ketPlus,
    PureState.smul_tensor, PureState.add_tensor, ket0, ket1,
    PureState.tensor_ket, PureState.tensor_ket]
  change CNOT.apply (invSqrt2 • (ket 0 + ket 2)) = bell
  rw [Gate.apply_smul, Gate.apply_add, CNOT_apply_ket, CNOT_apply_ket,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 0 = 0 by decide,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 2 = 3 by decide, bell]

/-- The Bell state is normalized. -/
@[simp]
theorem norm_bell : ‖bell‖ = 1 := by
  rw [bell, norm_smul, norm_invSqrt2]
  have h : ‖(ket 0 + ket 3 : PureState 2)‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i, ‖(ket 0 + ket 3 : PureState 2) i‖ ^ 2 = 2 := by
      refine (Fin.sum_univ_four (f := fun i : Fin (2 ^ 2) =>
        ‖(ket 0 + ket 3 : PureState 2) i‖ ^ 2)).trans ?_
      simp +decide [PiLp.add_apply, ket_apply]
      all_goals norm_num
    rw [hsum]
  rw [h, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

end

end QuantumAlg
