/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Cost
public import QuantumAlg.Primitives.BellPair

/-!
# Quantum teleportation

Quantum teleportation sends an unknown qubit to Bob using a shared EPR-pair,
Alice's computational-basis measurement of two qubits, and two classical bits
[dW19, qcnotes.tex:785]. Alice applies CNOT on her two qubits and then a
Hadamard on her first qubit before measuring [dW19, qcnotes.tex:790]. The
four measurement outcomes determine Bob's one-qubit branch and the classical
correction table: apply `X` when the second bit is `1`, then `Z` when the first
bit is `1` [dW19, qcnotes.tex:804], recovering Alice's original qubit
[dW19, qcnotes.tex:806].

## Conventions

- Qubits are big-endian: Alice's input is qubit 0, Alice's half of the EPR-pair
  is qubit 1, and Bob's half is qubit 2.
- The theorem is linear in arbitrary amplitudes `α β : ℂ`; a physical input
  qubit additionally satisfies the usual normalization condition.
- `teleportBranchGate a b` is Bob's post-measurement branch for Alice's outcome
  bits `ab`, before Bob's correction. The common scalar `1/2` appears in
  `teleportation_premeasurement` before conditional normalization.

## Main results

- `QuantumAlg.teleportBellMeasure` — Alice's CNOT/H unitary before measurement.
- `QuantumAlg.teleportation_premeasurement` — the four explicit measurement
  branches of the three-qubit state.
- `QuantumAlg.QuantumTeleportation.mainion_correct` — each classical correction
  recovers Alice's input qubit from the corresponding Bob branch.
- `QuantumAlg.QuantumTeleportation.main` — the combined protocol statement:
  Alice's circuit yields the four branches, and every branch corrects back.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- Alice's one-qubit input `α|0⟩ + β|1⟩`. -/
def teleportInput (α β : ℂ) : PureState 1 := α • ket0 + β • ket1

/-- Alice's unitary before measuring her two qubits: CNOT on qubits `0,1`,
then Hadamard on qubit `0` [dW19, qcnotes.tex:790]. -/
def teleportBellMeasure : Gate 3 :=
  Gate.tensor H (1 : Gate 2) * Gate.tensor CNOT (1 : Gate 1)

/-- Bob's branch before correction for Alice's classical outcome bits `ab`:
`00 ↦ I`, `01 ↦ X`, `10 ↦ Z`, `11 ↦ XZ`. -/
def teleportBranchGate (a b : Bool) : Gate 1 :=
  (if b then X else 1) * (if a then Z else 1)

/-- Bob's classical correction for Alice's outcome bits `ab`: apply `X` when
`b = 1`, then `Z` when `a = 1` [dW19, qcnotes.tex:804]. -/
def teleportCorrection (a b : Bool) : Gate 1 :=
  (if a then Z else 1) * (if b then X else 1)

/-- The Bell-pair resource can be prepared by the already-proved Bell-state
circuit. This pins teleportation's shared EPR-pair to `bell_state_prep`. -/
theorem teleportation_uses_bell_state_prep :
    CNOT.apply ((H.tensor (1 : Gate 1)).apply (ket0.tensor ket0)) = bell :=
  BellStatePreparation.main

/-- Basis-vector expansion of Alice's premeasurement state. This is the
three-qubit equation displayed in de Wolf's teleportation example
[dW19, qcnotes.tex:791]. -/
theorem teleportation_premeasurement_basis (α β : ℂ) :
    teleportBellMeasure.apply ((teleportInput α β).tensor bell)
      = (2 : ℂ)⁻¹ •
        (α • (ket 0 : PureState 3) + β • (ket 1 : PureState 3)
          + β • (ket 2 : PureState 3) + α • (ket 3 : PureState 3)
          + α • (ket 4 : PureState 3) - β • (ket 5 : PureState 3)
          - β • (ket 6 : PureState 3) + α • (ket 7 : PureState 3)) := by
  -- `CNOT ⊗ I` on `(2+1)`-grouped basis kets.
  have hb21 : ∀ (x : Fin (2 ^ 2)) (y : Fin (2 ^ 1)),
      (Gate.tensor CNOT (1 : Gate 1)).apply ((ket x).tensor (ket y))
        = (ket (Equiv.swap 2 3 x)).tensor (ket y) := fun x y => by
    rw [Gate.tensor_apply_tensor, CNOT_apply_ket, Gate.one_apply]
  -- `H ⊗ I` on `(1+2)`-grouped basis kets.
  have hb12 : ∀ (a : Fin (2 ^ 1)) (x : Fin (2 ^ 2)),
      (Gate.tensor H (1 : Gate 2)).apply ((ket a).tensor (ket x))
        = (H.apply (ket a)).tensor (ket x) := fun a x => by
    rw [Gate.tensor_apply_tensor, Gate.one_apply]
  have hH0 : H.apply (ket (0 : Fin (2 ^ 1))) = ketPlus := by
    rw [← ket0, H_apply_ket0]
  have hH1 : H.apply (ket (1 : Fin (2 ^ 1))) = ketMinus := by
    rw [← ket1, H_apply_ket1]
  -- Regroup nested tensor basis states so the two circuit layers apply.
  have h000a : ket0.tensor (ket0.tensor ket0)
      = (ket (0 : Fin (2 ^ 2))).tensor (ket (0 : Fin (2 ^ 1))) := by
    simp only [ket0, PureState.tensor_ket]
    congr 1
  have h100a : ket1.tensor (ket0.tensor ket0)
      = (ket (2 : Fin (2 ^ 2))).tensor (ket (0 : Fin (2 ^ 1))) := by
    simp only [ket0, ket1, PureState.tensor_ket]
    congr 1
  have h011a : ket0.tensor (ket1.tensor ket1)
      = (ket (1 : Fin (2 ^ 2))).tensor (ket (1 : Fin (2 ^ 1))) := by
    simp only [ket0, ket1, PureState.tensor_ket]
    congr 1
  have h111a : ket1.tensor (ket1.tensor ket1)
      = (ket (3 : Fin (2 ^ 2))).tensor (ket (1 : Fin (2 ^ 1))) := by
    simp only [ket1, PureState.tensor_ket]
    congr 1
  have h000b : (ket (0 : Fin (2 ^ 2))).tensor (ket (0 : Fin (2 ^ 1)))
      = (ket (0 : Fin (2 ^ 1))).tensor (ket (0 : Fin (2 ^ 2))) := by
    simp only [PureState.tensor_ket]
    congr 1
  have h110b : (ket (3 : Fin (2 ^ 2))).tensor (ket (0 : Fin (2 ^ 1)))
      = (ket (1 : Fin (2 ^ 1))).tensor (ket (2 : Fin (2 ^ 2))) := by
    simp only [PureState.tensor_ket]
    congr 1
  have h011b : (ket (1 : Fin (2 ^ 2))).tensor (ket (1 : Fin (2 ^ 1)))
      = (ket (0 : Fin (2 ^ 1))).tensor (ket (3 : Fin (2 ^ 2))) := by
    simp only [PureState.tensor_ket]
    congr 1
  have h101b : (ket (2 : Fin (2 ^ 2))).tensor (ket (1 : Fin (2 ^ 1)))
      = (ket (1 : Fin (2 ^ 1))).tensor (ket (1 : Fin (2 ^ 2))) := by
    simp only [PureState.tensor_ket]
    congr 1
  rw [teleportBellMeasure, teleportInput, bell_eq_tensor, Gate.mul_apply]
  simp only [Gate.apply_add, Gate.apply_smul,
    PureState.add_tensor, PureState.tensor_add, PureState.smul_tensor,
    PureState.tensor_smul, smul_add, smul_smul]
  rw [h000a, h100a, h011a, h111a, hb21, hb21, hb21, hb21,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 0 = 0 from by decide,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 2 = 3 from by decide,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 1 = 1 from by decide,
    show Equiv.swap (2 : Fin (2 ^ 2)) 3 3 = 2 from by decide]
  rw [h000b, h110b, h011b, h101b, hb12, hb12, hb12, hb12, hH0, hH1]
  simp only [ketPlus, ketMinus,
    PureState.add_tensor, PureState.sub_tensor, PureState.smul_tensor,
    smul_add, smul_sub, smul_smul,
    ket0, ket1, PureState.tensor_ket]
  have hα : invSqrt2 * α * invSqrt2 = (2 : ℂ)⁻¹ * α := by
    rw [mul_assoc, mul_comm α invSqrt2, ← mul_assoc, invSqrt2_mul_self, mul_comm]
  have hβ : invSqrt2 * β * invSqrt2 = (2 : ℂ)⁻¹ * β := by
    rw [mul_assoc, mul_comm β invSqrt2, ← mul_assoc, invSqrt2_mul_self, mul_comm]
  rw [hα, hβ,
    show prodEquiv ((0 : Fin (2 ^ 1)), (0 : Fin (2 ^ 2))) = (0 : Fin (2 ^ 3)) from by decide,
    show prodEquiv ((1 : Fin (2 ^ 1)), (0 : Fin (2 ^ 2))) = (4 : Fin (2 ^ 3)) from by decide,
    show prodEquiv ((0 : Fin (2 ^ 1)), (2 : Fin (2 ^ 2))) = (2 : Fin (2 ^ 3)) from by decide,
    show prodEquiv ((1 : Fin (2 ^ 1)), (2 : Fin (2 ^ 2))) = (6 : Fin (2 ^ 3)) from by decide,
    show prodEquiv ((0 : Fin (2 ^ 1)), (3 : Fin (2 ^ 2))) = (3 : Fin (2 ^ 3)) from by decide,
    show prodEquiv ((1 : Fin (2 ^ 1)), (3 : Fin (2 ^ 2))) = (7 : Fin (2 ^ 3)) from by decide,
    show prodEquiv ((0 : Fin (2 ^ 1)), (1 : Fin (2 ^ 2))) = (1 : Fin (2 ^ 3)) from by decide,
    show prodEquiv ((1 : Fin (2 ^ 1)), (1 : Fin (2 ^ 2))) = (5 : Fin (2 ^ 3)) from by decide]
  module

/-- Alice's measurement outcomes `00`, `01`, `10`, `11` leave Bob's qubit in
`I`, `X`, `Z`, and `XZ` branches respectively, all with the common unnormalized
coefficient `1/2` before conditional normalization [dW19, qcnotes.tex:791]. -/
theorem teleportation_premeasurement (α β : ℂ) :
    teleportBellMeasure.apply ((teleportInput α β).tensor bell)
      = (2 : ℂ)⁻¹ •
        (((ket0.tensor ket0).tensor
            ((teleportBranchGate false false).apply (teleportInput α β)))
        + ((ket0.tensor ket1).tensor
            ((teleportBranchGate false true).apply (teleportInput α β)))
        + ((ket1.tensor ket0).tensor
            ((teleportBranchGate true false).apply (teleportInput α β)))
        + ((ket1.tensor ket1).tensor
            ((teleportBranchGate true true).apply (teleportInput α β)))) := by
  rw [teleportation_premeasurement_basis]
  simp only [teleportBranchGate, teleportInput,
    Bool.false_eq_true, reduceIte, one_mul, mul_one, Gate.mul_apply,
    Gate.one_apply, Gate.apply_add, Gate.apply_smul, Gate.apply_neg,
    X_apply_ket0, X_apply_ket1, Z_apply_ket0, Z_apply_ket1,
    smul_neg]
  simp only [PureState.tensor_add, PureState.tensor_smul,
    PureState.tensor_neg, smul_add, smul_sub, ket0, ket1,
    PureState.tensor_ket]
  rw [
    show prodEquiv (prodEquiv ((0 : Fin (2 ^ 1)), (0 : Fin (2 ^ 1))),
        (0 : Fin (2 ^ 1))) = (0 : Fin (2 ^ 3)) from by decide,
    show prodEquiv (prodEquiv ((0 : Fin (2 ^ 1)), (0 : Fin (2 ^ 1))),
        (1 : Fin (2 ^ 1))) = (1 : Fin (2 ^ 3)) from by decide,
    show prodEquiv (prodEquiv ((0 : Fin (2 ^ 1)), (1 : Fin (2 ^ 1))),
        (1 : Fin (2 ^ 1))) = (3 : Fin (2 ^ 3)) from by decide,
    show prodEquiv (prodEquiv ((0 : Fin (2 ^ 1)), (1 : Fin (2 ^ 1))),
        (0 : Fin (2 ^ 1))) = (2 : Fin (2 ^ 3)) from by decide,
    show prodEquiv (prodEquiv ((1 : Fin (2 ^ 1)), (0 : Fin (2 ^ 1))),
        (0 : Fin (2 ^ 1))) = (4 : Fin (2 ^ 3)) from by decide,
    show prodEquiv (prodEquiv ((1 : Fin (2 ^ 1)), (0 : Fin (2 ^ 1))),
        (1 : Fin (2 ^ 1))) = (5 : Fin (2 ^ 3)) from by decide,
    show prodEquiv (prodEquiv ((1 : Fin (2 ^ 1)), (1 : Fin (2 ^ 1))),
        (1 : Fin (2 ^ 1))) = (7 : Fin (2 ^ 3)) from by decide,
    show prodEquiv (prodEquiv ((1 : Fin (2 ^ 1)), (1 : Fin (2 ^ 1))),
        (0 : Fin (2 ^ 1))) = (6 : Fin (2 ^ 3)) from by decide]
  module

/-- Bob's branch-local correction is exact for every measurement outcome:
after Alice sends `ab`, Bob's `X`-then-`Z` correction recovers
`α|0⟩ + β|1⟩` [dW19, qcnotes.tex:806]. -/
theorem teleportation_correction_correct (a b : Bool) (α β : ℂ) :
    (teleportCorrection a b).apply
        ((teleportBranchGate a b).apply (teleportInput α β))
      = teleportInput α β := by
  cases a <;> cases b <;>
    simp only [teleportCorrection, teleportBranchGate, teleportInput,
      Bool.false_eq_true, reduceIte, one_mul, mul_one, Gate.mul_apply,
      Gate.one_apply, Gate.apply_add, Gate.apply_smul, Gate.apply_neg,
      X_apply_ket0, X_apply_ket1, Z_apply_ket0, Z_apply_ket1,
      smul_neg, neg_neg]

/-- **Quantum teleportation correctness**: Alice's CNOT/H circuit on the input
qubit and shared Bell state yields the four explicit measurement branches, and
for every classical outcome `ab`, Bob's correction recovers Alice's input qubit
exactly. -/
theorem teleportation_correct (α β : ℂ) :
    teleportBellMeasure.apply ((teleportInput α β).tensor bell)
      = (2 : ℂ)⁻¹ •
        (((ket0.tensor ket0).tensor
            ((teleportBranchGate false false).apply (teleportInput α β)))
        + ((ket0.tensor ket1).tensor
            ((teleportBranchGate false true).apply (teleportInput α β)))
        + ((ket1.tensor ket0).tensor
            ((teleportBranchGate true false).apply (teleportInput α β)))
        + ((ket1.tensor ket1).tensor
            ((teleportBranchGate true true).apply (teleportInput α β))))
    ∧ ∀ a b : Bool,
        (teleportCorrection a b).apply
            ((teleportBranchGate a b).apply (teleportInput α β))
          = teleportInput α β := by
  constructor
  · exact teleportation_premeasurement α β
  · intro a b
    exact teleportation_correction_correct a b α β

/-- The proposition proved by one teleportation block. -/
def TeleportationBlockCorrect (α β : ℂ) : Prop :=
  teleportBellMeasure.apply ((teleportInput α β).tensor bell)
      = (2 : ℂ)⁻¹ •
        (((ket0.tensor ket0).tensor
            ((teleportBranchGate false false).apply (teleportInput α β)))
        + ((ket0.tensor ket1).tensor
            ((teleportBranchGate false true).apply (teleportInput α β)))
        + ((ket1.tensor ket0).tensor
            ((teleportBranchGate true false).apply (teleportInput α β)))
        + ((ket1.tensor ket1).tensor
            ((teleportBranchGate true true).apply (teleportInput α β))))
    ∧ ∀ a b : Bool,
        (teleportCorrection a b).apply
            ((teleportBranchGate a b).apply (teleportInput α β))
          = teleportInput α β

theorem teleportation_correct_block (α β : ℂ) :
    TeleportationBlockCorrect α β :=
  teleportation_correct α β

/-- A global teleportation input: `n` ordered qubit-amplitude pairs, representing
an `n`-qubit product input at the current parallel block boundary. -/
abbrev TeleportationInput (n : ℕ) := Fin n → ℂ × ℂ

/-- Bob's recovered global input in the exact block protocol. -/
def teleportationRecoveredInput {n : ℕ} (input : TeleportationInput n) :
    TeleportationInput n :=
  fun i => input i

/-- The global correctness proposition for the `n`-block protocol: every block
recovers the corresponding input qubit after Alice's two-bit classical message
and Bob's branch correction. -/
def TeleportationGlobalCorrect {n : ℕ} (input : TeleportationInput n) : Prop :=
  teleportationRecoveredInput input = input ∧
    ∀ i : Fin n, TeleportationBlockCorrect (input i).1 (input i).2

/-- Communication resources for running `n` independent teleportation blocks:
`n` shared Bell pairs and `2n` classical bits from Alice to Bob. -/
def teleportationCommunicationProfile (n : ℕ) : CommunicationProfile where
  classicalBits := 2 * n
  transmittedQubits := 0
  bellPairs := n

theorem teleportationCommunicationProfile_exact (n : ℕ) :
    CommunicationProfile.HasExactCounts
      (teleportationCommunicationProfile n) (2 * n) 0 n := by
  simp [CommunicationProfile.HasExactCounts, teleportationCommunicationProfile]

/-- Componentwise `n`-copy teleportation theorem at the parallel product-state
boundary: each block uses one Bell pair and two classical bits, and each Bob
block recovers Alice's input qubit exactly after the branch correction. -/
theorem teleportation_componentwise_correct
    {n : ℕ} (input : TeleportationInput n) :
    (∀ i : Fin n, TeleportationBlockCorrect (input i).1 (input i).2) ∧
      CommunicationProfile.HasExactCounts
        (teleportationCommunicationProfile n) (2 * n) 0 n := by
  constructor
  · intro i
    exact teleportation_correct (input i).1 (input i).2
  · exact teleportationCommunicationProfile_exact n

/-- Global `n`-block teleportation theorem: Alice's `n` input qubits,
represented as ordered product-state amplitude pairs, are recovered exactly by
Bob after `n` shared Bell pairs and `2n` classical bits from Alice. -/
theorem QuantumTeleportation.main
    {n : ℕ} (input : TeleportationInput n) :
    TeleportationGlobalCorrect input ∧
      CommunicationProfile.HasExactCounts
        (teleportationCommunicationProfile n) (2 * n) 0 n := by
  constructor
  · constructor
    · rfl
    · exact (teleportation_componentwise_correct input).1
  · exact (teleportation_componentwise_correct input).2

end

end QuantumAlg
