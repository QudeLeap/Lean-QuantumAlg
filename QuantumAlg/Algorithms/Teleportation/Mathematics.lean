/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Components.Gates.Pauli
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
public import QuantumAlg.Primitives.Communication
public import Mathlib.Data.Complex.Basic

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
- `QuantumAlg.teleportation_correction_correct` — each classical correction
  recovers Alice's input qubit from the corresponding Bob branch.
- `QuantumAlg.teleportation_product_input_with_profile` — the combined protocol statement:
  Alice's circuit yields the four branches, and every branch corrects back.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

/-- Alice's one-qubit input vector `α|0⟩ + β|1⟩`.

For arbitrary amplitudes this is a raw vector; a physical input qubit is a
`PureState` only after a norm-one proof is supplied. -/
def teleportInput (α β : ℂ) : HilbertVector (Qubits 1) :=
  α • (ket0 : HilbertVector (Qubits 1)) + β • (ket1 : HilbertVector (Qubits 1))

/-- Alice's unitary before measuring her two qubits: CNOT on qubits `0,1`,
then Hadamard on qubit `0` [dW19, qcnotes.tex:790]. -/
def teleportBellMeasure : UnitaryOperator (Qubits 3) :=
  HOp.tensor (1 : UnitaryOperator (Qubits 2)) *
    CNOTOp.tensor (1 : UnitaryOperator (Qubits 1))

/-- Bob's branch before correction for Alice's classical outcome bits `ab`:
`00 ↦ I`, `01 ↦ X`, `10 ↦ Z`, `11 ↦ XZ`. -/
def teleportBranchGate (a b : Bool) : UnitaryOperator (Qubits 1) :=
  (if b then XOp else 1) * (if a then ZOp else 1)

/-- Bob's classical correction for Alice's outcome bits `ab`: apply `X` when
`b = 1`, then `Z` when `a = 1` [dW19, qcnotes.tex:804]. -/
def teleportCorrection (a b : Bool) : UnitaryOperator (Qubits 1) :=
  (if a then ZOp else 1) * (if b then XOp else 1)

/-- The Bell-pair resource can be prepared by the already-proved Bell-state
circuit. This pins teleportation's shared EPR-pair to `bell_state_prep`. -/
lemma teleportation_uses_bell_state_prep
    (environment : OracleModel.empty.Interpretation) :
    (BellStatePreparation.circuit.binaryMatrix environment).apply BellStatePreparation.input
      = bell :=
  BellStatePreparation.bellPreparation_eq environment

/-- Three-qubit computational basis vectors as intrinsic normalized states. -/
def teleKet3 (j : Fin (2 ^ 3)) : NormalizedVector (Qubits 3) :=
  ket j

/-- Basis-vector expansion of Alice's premeasurement state. This is the
three-qubit equation displayed in de Wolf's teleportation example
[dW19, qcnotes.tex:791]. -/
lemma teleportation_premeasurement_basis (α β : ℂ) :
    teleportBellMeasure.applyVec
        (HilbertVector.tensor (teleportInput α β) (bell : HilbertVector (Qubits 2)))
      = (2 : ℂ)⁻¹ •
        ((α • (teleKet3 0 : HilbertVector (Qubits 3))) +
          (β • (teleKet3 1 : HilbertVector (Qubits 3))) +
          (β • (teleKet3 2 : HilbertVector (Qubits 3))) +
          (α • (teleKet3 3 : HilbertVector (Qubits 3))) +
          (α • (teleKet3 4 : HilbertVector (Qubits 3))) -
          (β • (teleKet3 5 : HilbertVector (Qubits 3))) -
          (β • (teleKet3 6 : HilbertVector (Qubits 3))) +
          (α • (teleKet3 7 : HilbertVector (Qubits 3)))) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp +decide [teleportBellMeasure, teleportInput, teleKet3, bell_coe,
      HilbertOperator.tensor, HOp, CNOTOp, ket0, ket1, UnitaryOperator.ofPerm,
      UnitaryOperator.ofMatrix, NormalizedVector.ket,
      HilbertVector.tensor, prodEquiv, Matrix.mul_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.one_apply,
      Fin.sum_univ_eight, invSqrt2_mul_mul_invSqrt2]

/-- Alice's measurement outcomes `00`, `01`, `10`, `11` leave Bob's qubit in
`I`, `X`, `Z`, and `XZ` branches respectively, all with the common unnormalized
coefficient `1/2` before conditional normalization [dW19, qcnotes.tex:791]. -/
lemma teleportation_premeasurement (α β : ℂ) :
    teleportBellMeasure.applyVec
        (HilbertVector.tensor (teleportInput α β) (bell : HilbertVector (Qubits 2)))
      = (2 : ℂ)⁻¹ •
        (HilbertVector.tensor
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ket0 : HilbertVector (Qubits 1)))
          ((teleportBranchGate false false).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ket1 : HilbertVector (Qubits 1)))
          ((teleportBranchGate false true).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (ket0 : HilbertVector (Qubits 1)))
          ((teleportBranchGate true false).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (ket1 : HilbertVector (Qubits 1)))
          ((teleportBranchGate true true).applyVec (teleportInput α β))) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp +decide [teleportBellMeasure, teleportBranchGate, teleportInput, bell_coe,
      HilbertOperator.tensor,
      HOp, XOp, ZOp, CNOTOp, ket0, ket1,
      UnitaryOperator.ofPerm, UnitaryOperator.ofMatrix, NormalizedVector.ket,
      HilbertVector.tensor, prodEquiv, Matrix.mul_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.one_apply,
      Fin.sum_univ_eight, invSqrt2_mul_mul_invSqrt2] <;>
    dsimp only [Equiv.symm] <;>
    simp +decide [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Bob's branch-local correction is exact for every measurement outcome:
after Alice sends `ab`, Bob's `X`-then-`Z` correction recovers
`α|0⟩ + β|1⟩` [dW19, qcnotes.tex:806]. -/
lemma teleportation_correction_correct (a b : Bool) (α β : ℂ) :
    (teleportCorrection a b).applyVec
        ((teleportBranchGate a b).applyVec (teleportInput α β))
      = teleportInput α β := by
  have hX0 : XOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ket1 : HilbertVector (Qubits 1)) :=
    by
      have h := congrArg (fun ψ : NormalizedVector (Qubits 1) =>
        (ψ : HilbertVector (Qubits 1))) pauliXOperator_apply_ket0
      simpa only [UnitaryOperator.apply_coe] using h
  have hX1 : XOp.applyVec (ket1 : HilbertVector (Qubits 1)) =
      (ket0 : HilbertVector (Qubits 1)) :=
    by
      have h := congrArg (fun ψ : NormalizedVector (Qubits 1) =>
        (ψ : HilbertVector (Qubits 1))) pauliXOperator_apply_ket1
      simpa only [UnitaryOperator.apply_coe] using h
  have hZ0 : ZOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ket0 : HilbertVector (Qubits 1)) :=
    by
      have h := congrArg (fun ψ : NormalizedVector (Qubits 1) =>
        (ψ : HilbertVector (Qubits 1))) pauliZOperator_apply_ket0
      simpa only [UnitaryOperator.apply_coe] using h
  have hZ1 : ZOp.applyVec (ket1 : HilbertVector (Qubits 1)) =
      -(ket1 : HilbertVector (Qubits 1)) := by
    exact pauliZOperator_applyVec_ket1
  cases a <;> cases b <;>
    simp [teleportCorrection, teleportBranchGate, UnitaryOperator.mul_applyVec,
      teleportInput, hX0, hX1, hZ0, hZ1]

/-- **Quantum teleportation correctness**: Alice's CNOT/H circuit on the input
qubit and shared Bell state yields the four explicit measurement branches, and
for every classical outcome `ab`, Bob's correction recovers Alice's input qubit
exactly. -/
lemma teleportation_correct (α β : ℂ) :
    teleportBellMeasure.applyVec
        (HilbertVector.tensor (teleportInput α β) (bell : HilbertVector (Qubits 2)))
      = (2 : ℂ)⁻¹ •
        (HilbertVector.tensor
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ket0 : HilbertVector (Qubits 1)))
          ((teleportBranchGate false false).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ket1 : HilbertVector (Qubits 1)))
          ((teleportBranchGate false true).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (ket0 : HilbertVector (Qubits 1)))
          ((teleportBranchGate true false).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (ket1 : HilbertVector (Qubits 1)))
          ((teleportBranchGate true true).applyVec (teleportInput α β)))
    ∧ ∀ a b : Bool,
        (teleportCorrection a b).applyVec
            ((teleportBranchGate a b).applyVec (teleportInput α β))
          = teleportInput α β := by
  constructor
  · exact teleportation_premeasurement α β
  · intro a b
    exact teleportation_correction_correct a b α β

/-- The proposition proved by one teleportation block. -/
def TeleportationBlockCorrect (α β : ℂ) : Prop :=
  teleportBellMeasure.applyVec
      (HilbertVector.tensor (teleportInput α β) (bell : HilbertVector (Qubits 2)))
      = (2 : ℂ)⁻¹ •
        (HilbertVector.tensor
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ket0 : HilbertVector (Qubits 1)))
          ((teleportBranchGate false false).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (ket1 : HilbertVector (Qubits 1)))
          ((teleportBranchGate false true).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (ket0 : HilbertVector (Qubits 1)))
          ((teleportBranchGate true false).applyVec (teleportInput α β))
        + HilbertVector.tensor
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (ket1 : HilbertVector (Qubits 1)))
          ((teleportBranchGate true true).applyVec (teleportInput α β)))
    ∧ ∀ a b : Bool,
        (teleportCorrection a b).applyVec
            ((teleportBranchGate a b).applyVec (teleportInput α β))
          = teleportInput α β

lemma teleportation_correct_block (α β : ℂ) :
    TeleportationBlockCorrect α β :=
  teleportation_correct α β

/-- A global teleportation input: `n` ordered qubit-amplitude pairs, representing
an `n`-qubit product input at the current parallel block boundary. -/
public abbrev TeleportationInput (n : ℕ) := Fin n → ℂ × ℂ

/-- Bob's recovered global input in the exact block protocol. -/
def teleportationRecoveredInput {n : ℕ} (input : TeleportationInput n) :
    TeleportationInput n :=
  fun i => input i

/-- The global correctness proposition for the `n`-block protocol: every block
recovers the corresponding input qubit after Alice's two-bit classical message
and Bob's branch correction. -/
public def TeleportationGlobalCorrect {n : ℕ} (input : TeleportationInput n) : Prop :=
  teleportationRecoveredInput input = input ∧
    ∀ i : Fin n, TeleportationBlockCorrect (input i).1 (input i).2

/-- Communication resources for running `n` independent teleportation blocks:
`n` shared Bell pairs and `2n` classical bits from Alice to Bob. -/
public def teleportationCommunicationProfile (n : ℕ) : CommunicationProfile where
  classicalBits := 2 * n
  transmittedQubits := 0
  bellPairs := n

lemma teleportationCommunicationProfile_exact (n : ℕ) :
    CommunicationProfile.HasExactCounts
      (teleportationCommunicationProfile n) (2 * n) 0 n := by
  simpa only [teleportationCommunicationProfile] using
    CommunicationProfile.hasExactCounts_mk (2 * n) 0 n

/-- Componentwise `n`-copy teleportation theorem at the parallel product-state
boundary: each block uses one Bell pair and two classical bits, and each Bob
block recovers Alice's input qubit exactly after the branch correction. -/
lemma teleportation_componentwise_correct
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
public lemma teleportation_product_input_with_profile
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

end
