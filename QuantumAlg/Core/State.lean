/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Qubit states

An `n`-qubit pure state is a unit vector in `ℂ^(2^n)` with the L2 inner
product, encoded as `EuclideanSpace ℂ (Fin (2 ^ n))`.

## Naming: `PureState`, not `State`

In quantum mechanics the general notion of a state is a *density operator*
(density matrix); pure states are the special case of a closed system with
maximal knowledge. The algorithms in this library live entirely in that
special case (pure state + unitary evolution + projective measurement), but
the library does not redefine the standard term: this type is `PureState`,
and the bare name `State` is deliberately left undefined, reserved for the
density-operator concept should the library later introduce mixed states
(a pure state then embeds as the rank-one projector `|ψ⟩⟨ψ|`).

## Conventions

- **Endianness**: computational basis states of an `n`-qubit register are
  labelled by `n`-bit strings read as integers `0, …, 2^n - 1`
  [dW19, qcnotes.tex:587], leftmost bit most significant. We index qubits
  left to right, so the basis label `x : Fin (2 ^ n)` encodes
  `|q₀ q₁ … q_{n-1}⟩` with `x = Σ qᵢ · 2^(n-1-i)`: qubit 0 carries the most
  significant bit.
- **Normalization** is stated per ket (`norm_ket`; the named-ket norms live
  with their kets in `Core.Components.Kets`), not bundled in the type: gates
  act on the raw vector space and unitarity (`QuantumAlg.Gate`) preserves
  norms.
- Components are accessed by plain application `ψ i`; the underlying
  `Pi`-function of `ψ : PureState n` is `ψ.ofLp` (Mathlib's `WithLp` design).

## Main definitions

- `QuantumAlg.PureState n` — the state space `EuclideanSpace ℂ (Fin (2 ^ n))`.
- `QuantumAlg.PureState.ket x` — computational basis ket `|x⟩`
  (`PiLp.single 2 x 1`).

The named one-qubit kets (`ket0`, `ket1`, `ketPlus`, `ketMinus`) and the
scalar `invSqrt2` now live in `QuantumAlg.Core.Components.Kets`.

Pinned Mathlib API: `PiLp.single`, `PiLp.single_apply`, `PiLp.norm_single`,
`EuclideanSpace.norm_eq`.
-/

@[expose] public section

namespace QuantumAlg

/-- The space of `n`-qubit pure states: length-`2^n` complex vectors with the
L2 inner product. States used in theorems are normalized (see the `norm_*`
lemmas); the type itself does not enforce it. The general (density-operator)
notion of state is intentionally not defined here — see the module docstring. -/
abbrev PureState (n : ℕ) : Type := EuclideanSpace ℂ (Fin (2 ^ n))

namespace PureState

noncomputable section

variable {n : ℕ}

/-- The computational basis ket `|x⟩ : PureState n`, big-endian (qubit 0 is
the most significant bit of `x`). -/
def ket (x : Fin (2 ^ n)) : PureState n := PiLp.single 2 x 1

@[simp]
theorem ket_apply (x i : Fin (2 ^ n)) : ket x i = if i = x then 1 else 0 := by
  simp [ket]

theorem ket_injective : Function.Injective (ket (n := n)) := by
  intro x y hxy
  by_contra hne
  have h : ket x x = ket y x := by rw [hxy]
  rw [ket_apply, ket_apply, if_pos rfl, if_neg hne] at h
  exact one_ne_zero h

@[simp]
theorem norm_ket (x : Fin (2 ^ n)) : ‖ket x‖ = 1 := by
  simp [ket]

end

end PureState

end QuantumAlg
