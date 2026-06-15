/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.BellPair

/-!
# Superdense coding

Two classical bits travel over one qubit, given a shared EPR-pair
[dW19, qcnotes.tex:879]. Alice holds bits `a, b` and applies `X` (if
`a = 1`) then `Z` (if `b = 1`) to her half of the Bell state
[dW19, qcnotes.tex:882]; after she sends her qubit to Bob, he applies
`CNOT` then `H` on Alice's qubit and reads both bits off a
computational-basis measurement [dW19, qcnotes.tex:885]. The protocol is
due to Bennett and Wiesner (1992).

## Conventions

- Alice's qubit is qubit 0 (the most significant, big-endian); Bob's is
  qubit 1.
- The decoded state is exactly the basis ket `|b a⟩` — no residual phase —
  so the final measurement is deterministic.

## Main results

- `QuantumAlg.superdenseEncode` — Alice's encoding gate `(Z^b X^a) ⊗ I`.
- `QuantumAlg.superdenseDecode` — Bob's decoding circuit `(H ⊗ I) · CNOT`.
- `QuantumAlg.superdense_coding` — correctness:
  `decode (encode a b |Φ⁺⟩) = |b a⟩`.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- Alice's encoding: `X` on her qubit if `a`, then `Z` if `b`
[dW19, qcnotes.tex:882] — as the two-qubit gate `(Z^b X^a) ⊗ I`. -/
def superdenseEncode (a b : Bool) : Gate 2 :=
  Gate.tensor ((if b then Z else 1) * (if a then X else 1)) (1 : Gate 1)

/-- Bob's decoding circuit: `CNOT` (control = Alice's qubit), then `H` on
Alice's qubit [dW19, qcnotes.tex:885]. -/
def superdenseDecode : Gate 2 :=
  Gate.tensor H (1 : Gate 1) * CNOT

/-- **Superdense coding** [dW19, qcnotes.tex:879]: Bob's decoding circuit
turns the encoded Bell state into exactly the basis state `|b a⟩`, so a
computational-basis measurement recovers both of Alice's bits with
certainty. Protocol due to Bennett and Wiesner (1992). -/
theorem superdense_coding (a b : Bool) :
    superdenseDecode.apply ((superdenseEncode a b).apply bell)
      = (if b then ket1 else ket0).tensor (if a then ket1 else ket0) := by
  rw [superdenseDecode, superdenseEncode, bell_eq_tensor, Gate.mul_apply]
  cases a <;> cases b <;>
    simp only [Bool.false_eq_true, reduceIte, one_mul, mul_one, Gate.mul_apply,
      Gate.apply_smul, Gate.apply_add, Gate.apply_neg, Gate.one_apply,
      Gate.tensor_apply_tensor, Gate.one_tensor_one,
      X_apply_ket0, X_apply_ket1, Z_apply_ket0, Z_apply_ket1,
      H_apply_ket0, H_apply_ket1, ketPlus, ketMinus,
      CNOT_apply_ket0_tensor_ket0, CNOT_apply_ket0_tensor_ket1,
      CNOT_apply_ket1_tensor_ket0, CNOT_apply_ket1_tensor_ket1,
      PureState.smul_tensor, PureState.add_tensor, PureState.sub_tensor,
      PureState.neg_tensor, smul_add, smul_sub, smul_neg, smul_smul,
      invSqrt2_mul_self] <;>
    module

end

end QuantumAlg
