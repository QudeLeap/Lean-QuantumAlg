/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Gates

/-!
# GHZ state preparation

The three-qubit GHZ state `(|000⟩ + |111⟩)/√2`, prepared from `|000⟩` by a
Hadamard on qubit 0 followed by a CNOT cascade:

`(I ⊗ CNOT) · (CNOT ⊗ I) · (H ⊗ I ⊗ I) · |000⟩ = (|000⟩ + |111⟩)/√2`.

States of this multipartite family are due to Greenberger, Horne and
Zeilinger (1989), whose original argument uses a four-particle spin state
(reprinted as arXiv:0712.0921). The three-qubit form and the name "GHZ
state" are standard textbook material (e.g. Nielsen and Chuang 2000). In
[dW19] the unnormalized states `|000⟩ ± |111⟩` appear as
the code blocks of Shor's 9-qubit code [dW19, qcnotes.tex:7456], and a
locally-equivalent three-qubit state powers Mermin's game
[dW19, qcnotes.tex:6667].

## Conventions

- Big-endian basis labelling as in `Core/State.lean`: `|000⟩ = ket 0` and
  `|111⟩ = ket 7`.
- Qubit 0 carries the Hadamard and controls the first CNOT (target
  qubit 1); qubit 1 controls the second CNOT (target qubit 2).
- The circuit factors use the qubit groupings `1+2`, `2+1`, `1+2`; the
  index types all reduce to `Fin (2^3)` definitionally.

## Main results

- `QuantumAlg.ghz` — the three-qubit GHZ state, as a `PureState 3`.
- `QuantumAlg.ghzCircuit` — the preparation circuit, as a `Gate 3`.
- `QuantumAlg.ghz_state_prep` — the preparation-circuit equality.
- `QuantumAlg.norm_ghz` — the GHZ state is normalized.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The three-qubit GHZ state `(|000⟩ + |111⟩)/√2` (Greenberger, Horne and
Zeilinger 1989; three-qubit form standard, e.g. Nielsen and Chuang 2000).
In the big-endian basis labelling, `|000⟩ = ket 0` and `|111⟩ = ket 7`. -/
def ghz : PureState 3 := invSqrt2 • (ket 0 + ket 7)

/-- The GHZ preparation circuit: a Hadamard on qubit 0, a CNOT with
control 0 and target 1, then a CNOT with control 1 and target 2 —
`(I ⊗ CNOT) · (CNOT ⊗ I) · (H ⊗ I ⊗ I)`. -/
def ghzCircuit : Gate 3 :=
  Gate.tensor (1 : Gate 1) CNOT
    * (Gate.tensor CNOT (1 : Gate 1) * Gate.tensor H (1 : Gate 2))

/-- **GHZ state preparation**: the cascade circuit turns `|000⟩` into the
GHZ state, extending Bell-state preparation (`bell_state_prep`) by one
CNOT. -/
theorem GHZStatePreparation.main :
    ghzCircuit.apply (ket0.tensor (ket0.tensor ket0)) = ghz := by
  -- `CNOT ⊗ I` on `(2+1)`-grouped basis kets.
  have hb21 : ∀ (x : Fin (2 ^ 2)) (y : Fin (2 ^ 1)),
      (Gate.tensor CNOT (1 : Gate 1)).apply ((ket x).tensor (ket y))
        = (ket (Equiv.swap 2 3 x)).tensor (ket y) := fun x y => by
    rw [Gate.tensor_apply_tensor, CNOT_apply_ket, Gate.one_apply]
  -- `I ⊗ CNOT` on `(1+2)`-grouped basis kets.
  have hb12 : ∀ (a : Fin (2 ^ 1)) (x : Fin (2 ^ 2)),
      (Gate.tensor (1 : Gate 1) CNOT).apply ((ket a).tensor (ket x))
        = (ket a).tensor (ket (Equiv.swap 2 3 x)) := fun a x => by
    rw [Gate.tensor_apply_tensor, CNOT_apply_ket, Gate.one_apply]
  -- Numeral kets in `Fin (2^3)` versus their `2+1` / `1+2` tensor groupings.
  have h00a : (ket 0 : PureState 3)
      = (ket (0 : Fin (2 ^ 2))).tensor (ket (0 : Fin (2 ^ 1))) := by
    rw [PureState.tensor_ket]; congr 1
  have h40a : (ket 4 : PureState 3)
      = (ket (2 : Fin (2 ^ 2))).tensor (ket (0 : Fin (2 ^ 1))) := by
    rw [PureState.tensor_ket]; congr 1
  have h00b : (ket 0 : PureState 3)
      = (ket (0 : Fin (2 ^ 1))).tensor (ket (0 : Fin (2 ^ 2))) := by
    rw [PureState.tensor_ket]; congr 1
  have h60b : (ket 6 : PureState 3)
      = (ket (1 : Fin (2 ^ 1))).tensor (ket (2 : Fin (2 ^ 2))) := by
    rw [PureState.tensor_ket]; congr 1
  -- Step 1: Hadamard on qubit 0.
  rw [ghzCircuit, Gate.mul_apply, Gate.mul_apply,
    Gate.tensor_apply_tensor H (1 : Gate 2) ket0 (ket0.tensor ket0),
    H_apply_ket0, Gate.one_apply, ketPlus, PureState.smul_tensor,
    PureState.add_tensor, ket0, ket1]
  simp only [PureState.tensor_ket]
  change (Gate.tensor (1 : Gate 1) CNOT).apply
      ((Gate.tensor CNOT (1 : Gate 1)).apply (invSqrt2 • (ket 0 + ket 4)))
    = ghz
  -- Step 2: CNOT with control 0, target 1 (grouping `2+1`).
  rw [Gate.apply_smul, Gate.apply_add, h00a, h40a, hb21, hb21,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 0 = 0 from by decide,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 2 = 3 from by decide]
  simp only [PureState.tensor_ket]
  change (Gate.tensor (1 : Gate 1) CNOT).apply (invSqrt2 • (ket 0 + ket 6))
    = ghz
  -- Step 3: CNOT with control 1, target 2 (grouping `1+2`).
  rw [Gate.apply_smul, Gate.apply_add, h00b, h60b, hb12, hb12,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 0 = 0 from by decide,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 2 = 3 from by decide]
  simp only [PureState.tensor_ket]
  change invSqrt2 • (ket 0 + ket 7) = ghz
  rw [ghz]


/-- The GHZ state is normalized. -/
@[simp]
theorem norm_ghz : ‖ghz‖ = 1 := by
  rw [ghz, norm_smul, norm_invSqrt2]
  have h : ‖(ket 0 + ket 7 : PureState 3)‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i, ‖(ket 0 + ket 7 : PureState 3) i‖ ^ 2 = 2 := by
      refine (Fin.sum_univ_eight (f := fun i : Fin (2 ^ 3) =>
        ‖(ket 0 + ket 7 : PureState 3) i‖ ^ 2)).trans ?_
      simp +decide [PiLp.add_apply, ket_apply]
      all_goals norm_num
    rw [hsum]
  rw [h, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

end

end QuantumAlg
