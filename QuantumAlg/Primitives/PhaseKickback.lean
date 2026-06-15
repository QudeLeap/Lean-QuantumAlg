/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Control
public import QuantumAlg.Core.Components.Oracle

/-!
# Phase kickback

Querying the XOR oracle of `f` with the target qubit in `|−⟩` leaves the
target untouched and kicks the value of `f` back into the phase of the
input register [dW19, qcnotes.tex:1167]:

`U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} · (|x⟩ ⊗ |−⟩)`,

the "phase kick-back trick" [dW19, qcnotes.tex:1173]. Dually, a `|+⟩`
target is left invariant, which lets circuits choose per-branch whether a
phase query happens [dW19, qcnotes.tex:1173].

The eigenvalue form replaces the oracle by a controlled unitary: if the
target register holds an eigenstate `|u⟩` of `U`, the eigenvalue `e^{iθ}`
is "kicked back" in front of the `|1⟩` component of the control
[CEMM98, cemm6.tex:163].

## Main results

- `QuantumAlg.phase_kickback` — `U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} (|x⟩ ⊗ |−⟩)`,
  with the sign written as `if f x then -1 else 1`.
- `QuantumAlg.xorOracle_apply_tensor_ketPlus` — `U_f (|x⟩ ⊗ |+⟩) = |x⟩ ⊗ |+⟩`.
- `QuantumAlg.eigenvalue_phase_kickback` —
  `c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩` when
  `U |u⟩ = e^{iθ} |u⟩`.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- **Phase kickback**: on a `|−⟩` target the XOR oracle acts as the phase
oracle `|x⟩ ↦ (−1)^{f(x)} |x⟩`; the sign `(−1)^{f(x)}` is written
`if f x then -1 else 1`. -/
theorem phase_kickback (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) :
    (Gate.xorOracle f).apply ((ket x).tensor ketMinus)
      = (if f x then (-1 : ℂ) else 1) • ((ket x).tensor ketMinus) := by
  have h0 : (0 : Fin (2 ^ 1)).rev = 1 := by decide
  have h1 : (1 : Fin (2 ^ 1)).rev = 0 := by decide
  rw [ketMinus, PureState.tensor_smul, PureState.tensor_sub, ket0, ket1,
    PureState.tensor_ket, PureState.tensor_ket, Gate.apply_smul,
    Gate.apply_sub, Gate.xorOracle_apply_ket, Gate.xorOracle_apply_ket]
  by_cases h : f x
  · simp [h, h0, h1]
    all_goals module
  · simp [h]

/-- On a `|+⟩` target the XOR oracle acts trivially, whatever `f` is. -/
theorem xorOracle_apply_tensor_ketPlus (f : Fin (2 ^ n) → Bool)
    (x : Fin (2 ^ n)) :
    (Gate.xorOracle f).apply ((ket x).tensor ketPlus)
      = (ket x).tensor ketPlus := by
  have h0 : (0 : Fin (2 ^ 1)).rev = 1 := by decide
  have h1 : (1 : Fin (2 ^ 1)).rev = 0 := by decide
  rw [ketPlus, PureState.tensor_smul, PureState.tensor_add, ket0, ket1,
    PureState.tensor_ket, PureState.tensor_ket, Gate.apply_smul,
    Gate.apply_add, Gate.xorOracle_apply_ket, Gate.xorOracle_apply_ket]
  by_cases h : f x
  · simp [h, h0, h1]
    all_goals module
  · simp [h]

/-- **Eigenvalue phase kickback** [CEMM98, cemm6.tex:163]: if the target
register holds an eigenstate `|u⟩` of `U` with eigenvalue `e^{iθ}`, the
controlled `U` leaves the target unchanged and kicks the eigenvalue back
onto the `|1⟩` component of the control [CEMM98, cemm6.tex:142]:

`c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩`. -/
theorem eigenvalue_phase_kickback (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.apply u = Complex.exp (θ * Complex.I) • u) (a b : ℂ) :
    (Gate.controlled U).apply ((a • ket0 + b • ket1).tensor u)
      = (a • ket0 + (Complex.exp (θ * Complex.I) * b) • ket1).tensor u := by
  simp only [PureState.add_tensor, PureState.smul_tensor, Gate.apply_add,
    Gate.apply_smul, Gate.controlled_apply_ket0_tensor,
    Gate.controlled_apply_ket1_tensor, hu, PureState.tensor_smul, smul_smul]
  module

end

end QuantumAlg
