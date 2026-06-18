/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Tensor

/-!
# Computational-basis measurement

Born rule for the computational-basis PVM `{|x⟩⟨x|}` [dW19,
qcnotes.tex:406]: measuring `ψ` yields outcome `x` with probability
`|ψ x|²`. For a `1 + n`-qubit register we also provide the marginal
probability of observing the first qubit, given by the projective
measurement `{|b⟩⟨b| ⊗ I}` whose outcome probability is the squared norm
of the projected state [dW19, qcnotes.tex:433].

Probabilities are stated for the state actually measured; they form a
probability distribution when that state is normalized
(`sum_probOutcome_eq_one`).

## Main definitions

- `QuantumAlg.PureState.probOutcome ψ x` — Born-rule probability `|ψ x|²`
  of outcome `x` when measuring all qubits.
- `QuantumAlg.PureState.probQubit0 ψ b` — probability that measuring
  qubit 0 (the most significant, big-endian) yields `b`, the rest
  unobserved.
The named-ket workhorse lemmas (`probQubit0_ket0_tensor_add_ket1_tensor` /
`probQubit1_ket0_tensor_add_ket1_tensor`) — on a state `|0⟩ ⊗ α + |1⟩ ⊗ β`
the marginal probabilities are `‖α‖²` and `‖β‖²` — now live in
`QuantumAlg.Core.Components.Kets`.
-/

@[expose] public section

namespace QuantumAlg

namespace PureState

noncomputable section

variable {n : ℕ}

/-- Born rule [dW19, qcnotes.tex:406]: the probability of observing
outcome `x` when measuring `ψ` in the computational basis. -/
def probOutcome (ψ : PureState n) (x : Fin (2 ^ n)) : ℝ := ‖ψ x‖ ^ 2

theorem probOutcome_nonneg (ψ : PureState n) (x : Fin (2 ^ n)) :
    0 ≤ probOutcome ψ x :=
  sq_nonneg _

/-- The Born-rule weights sum to the squared norm. -/
theorem sum_probOutcome (ψ : PureState n) :
    ∑ x, probOutcome ψ x = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖ψ i‖)]
  rfl

/-- On a normalized state the outcome probabilities form a probability
distribution [dW19, qcnotes.tex:408]. -/
theorem sum_probOutcome_eq_one {ψ : PureState n} (hψ : ‖ψ‖ = 1) :
    ∑ x, probOutcome ψ x = 1 := by
  rw [sum_probOutcome, hψ, one_pow]

@[simp]
theorem probOutcome_ket (x y : Fin (2 ^ n)) :
    probOutcome (ket x) y = if y = x then 1 else 0 := by
  rw [probOutcome, ket_apply]
  by_cases h : y = x
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- Expectation value `⟨ψ|O|ψ⟩` of an observable `O` in the state `ψ`, as a real
number via the real part. For a Hermitian `O` this is the physical expectation
value; it is the cost function minimized by variational quantum algorithms. -/
def expVal (ψ : PureState n) (O : Gate n) : ℝ := (inner ℂ ψ (O.apply ψ)).re

/-- Probability that measuring qubit 0 of a `1 + n`-qubit state (in the
computational basis, leaving the other qubits unobserved) yields `b`:
the squared norm of the `|b⟩`-block, per the projective measurement
`{|0⟩⟨0| ⊗ I, |1⟩⟨1| ⊗ I}` [dW19, qcnotes.tex:433]. -/
def probQubit0 (ψ : PureState (1 + n)) (b : Fin (2 ^ 1)) : ℝ :=
  ∑ y : Fin (2 ^ n), ‖ψ (prodEquiv (b, y))‖ ^ 2

theorem probQubit0_nonneg (ψ : PureState (1 + n)) (b : Fin (2 ^ 1)) :
    0 ≤ probQubit0 ψ b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Scaling a state scales the marginal probability by the squared
scalar norm. -/
theorem probQubit0_smul (c : ℂ) (ψ : PureState (1 + n)) (b : Fin (2 ^ 1)) :
    probQubit0 (c • ψ) b = ‖c‖ ^ 2 * probQubit0 ψ b := by
  rw [probQubit0, probQubit0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, norm_mul, mul_pow]

end

end PureState

end QuantumAlg
