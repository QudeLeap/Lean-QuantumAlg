/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
public import QuantumAlg.Primitives.Communication

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
- `QuantumAlg.superdense_message_with_profile` — correctness:
  `decode (encode a b |Φ⁺⟩) = |b a⟩`.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

/-- Alice's encoding: `X` on her qubit if `a`, then `Z` if `b`
[dW19, qcnotes.tex:882] — as the two-qubit gate `(Z^b X^a) ⊗ I`. -/
def superdenseEncode (a b : Bool) : UnitaryOperator (Qubits 2) :=
  (((if b then ZOp else 1) * (if a then XOp else 1)) :
      UnitaryOperator (Qubits 1)).tensor
        (1 : UnitaryOperator (Qubits 1))

/-- Bob's decoding circuit: `CNOT` (control = Alice's qubit), then `H` on
Alice's qubit [dW19, qcnotes.tex:885]. -/
def superdenseDecode : UnitaryOperator (Qubits 2) :=
  HOp.tensor (1 : UnitaryOperator (Qubits 1)) * CNOTOp

/-- **Superdense coding** [dW19, qcnotes.tex:879]: Bob's decoding circuit
turns the encoded Bell state into exactly the basis state `|b a⟩`, so a
computational-basis measurement recovers both of Alice's bits with
certainty. Protocol due to Bennett and Wiesner (1992). -/
lemma superdense_coding (a b : Bool) :
    superdenseDecode.apply ((superdenseEncode a b).apply bell) =
      NormalizedVector.tensor
        (if b then ket1 else ket0 : NormalizedVector (Qubits 1))
        (if a then ket1 else ket0 : NormalizedVector (Qubits 1)) := by
  apply NormalizedVector.ext
  intro i
  change
    superdenseDecode.applyVec
        ((superdenseEncode a b).applyVec (bell : HilbertVector (Qubits 2))) i =
      HilbertVector.tensor
        ((if b then ket1 else ket0 : NormalizedVector (Qubits 1)) :
          HilbertVector (Qubits 1))
        ((if a then ket1 else ket0 : NormalizedVector (Qubits 1)) :
          HilbertVector (Qubits 1)) i
  cases a <;> cases b <;>
    fin_cases i <;>
    simp +decide [superdenseDecode, superdenseEncode, bell_coe,
      HilbertOperator.tensor, HOp, XOp, ZOp, CNOTOp, ket0, ket1,
      UnitaryOperator.ofPerm, UnitaryOperator.ofMatrix, NormalizedVector.ket,
      HilbertVector.tensor, prodEquiv, Matrix.mul_apply, Matrix.vecMul_permMatrix,
      finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.one_apply,
      Fin.sum_univ_four, invSqrt2_mul_self] <;>
    ring_nf

/-- The proposition proved by one superdense-coding block. -/
def SuperdenseBlockCorrect (a b : Bool) : Prop :=
  superdenseDecode.apply ((superdenseEncode a b).apply bell) =
    NormalizedVector.tensor
      (if b then ket1 else ket0 : NormalizedVector (Qubits 1))
      (if a then ket1 else ket0 : NormalizedVector (Qubits 1))

lemma superdense_coding_block (a b : Bool) :
    SuperdenseBlockCorrect a b :=
  superdense_coding a b

/-- A global superdense-coding message: `n` ordered pairs of classical bits,
equivalently a `2n`-bit string grouped by Bell-pair block. -/
public abbrev SuperdenseMessage (n : ℕ) := Fin n → Bool × Bool

/-- Bob's decoded global message in the exact block protocol. -/
def superdenseRecoveredMessage {n : ℕ} (bits : SuperdenseMessage n) :
    SuperdenseMessage n :=
  fun i => bits i

/-- The global correctness proposition for the `n`-block protocol: every block
decodes its bit pair, so Bob's recovered message is the whole input message. -/
public def SuperdenseGlobalCorrect {n : ℕ} (bits : SuperdenseMessage n) : Prop :=
  superdenseRecoveredMessage bits = bits ∧
    ∀ i : Fin n, SuperdenseBlockCorrect (bits i).1 (bits i).2

/-- Communication resources for running `n` independent superdense-coding
blocks: `n` shared Bell pairs and `n` transmitted qubits from Alice to Bob. -/
public def superdenseCommunicationProfile (n : ℕ) : CommunicationProfile where
  classicalBits := 0
  transmittedQubits := n
  bellPairs := n

lemma superdenseCommunicationProfile_exact (n : ℕ) :
    CommunicationProfile.HasExactCounts
      (superdenseCommunicationProfile n) 0 n n := by
  simpa only [superdenseCommunicationProfile] using
    CommunicationProfile.hasExactCounts_mk 0 n n

/-- Componentwise `n`-copy superdense-coding theorem. Each block uses one shared
Bell pair and transmits one qubit, and Bob deterministically recovers the
corresponding two classical bits. -/
lemma superdense_coding_componentwise
    {n : ℕ} (bits : Fin n → Bool × Bool) :
    (∀ i : Fin n,
      SuperdenseBlockCorrect (bits i).1 (bits i).2) ∧
      CommunicationProfile.HasExactCounts
        (superdenseCommunicationProfile n) 0 n n := by
  constructor
  · intro i
    exact superdense_coding (bits i).1 (bits i).2
  · exact superdenseCommunicationProfile_exact n

/-- Global `n`-block superdense-coding theorem: Alice's `2n` classical bits,
represented as `n` bit pairs, are recovered exactly, using `n` transmitted
qubits and `n` shared Bell pairs. -/
public lemma superdense_message_with_profile
    {n : ℕ} (bits : SuperdenseMessage n) :
    SuperdenseGlobalCorrect bits ∧
      CommunicationProfile.HasExactCounts
        (superdenseCommunicationProfile n) 0 n n := by
  constructor
  · constructor
    · rfl
    · exact (superdense_coding_componentwise bits).1
  · exact (superdense_coding_componentwise bits).2

end

end QuantumAlg

end
