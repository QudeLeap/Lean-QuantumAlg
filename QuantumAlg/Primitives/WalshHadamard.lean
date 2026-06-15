/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Oracle
public import QuantumAlg.Core.Components.Kets

/-!
# Walsh-Hadamard transform and the XOR phase-query pipeline

The reusable machinery shared by the single-query Hadamard-oracle-Hadamard
algorithms (Deutsch-Jozsa, Bernstein-Vazirani): the `n`-qubit Hadamard layer
in Walsh-Hadamard closed form [dW19, qcnotes.tex:1005-1006], and the
XOR-oracle phase-query pipeline that runs a Boolean oracle on the uniform
input register with a `|−⟩` target.

The central bridge `postOracleState_eq_afterPhaseQuery_tensor` rewrites the
actual XOR-oracle query as the phase pattern `(√(2^n))⁻¹ ∑ x (-1)^{f x}|x⟩`
tensored with the unchanged `|−⟩` target, so a single query followed by the
second Hadamard layer (`finalJointState`) factors through the input-register
`finalState`.

These pieces sit in a `Primitives` module so the Deutsch-Jozsa and
Bernstein-Vazirani algorithms can both build on them without importing one
another; each algorithm keeps only its target-specific content (the
constant/balanced promise and amplitude test for Deutsch-Jozsa; Walsh-character
orthogonality and string recovery for Bernstein-Vazirani).

## Main definitions

- `QuantumAlg.WalshHadamard.Oracle n` — a Boolean function on `2^n` labels,
  queried through `Gate.xorOracle`.
- `QuantumAlg.WalshHadamard.walshSign` — the Walsh-Hadamard sign `(-1)^{x·y}`,
  and `hadamardLayer` its closed-form `n`-qubit gate.
- `QuantumAlg.WalshHadamard.uniformState` — the uniform superposition.
- `QuantumAlg.WalshHadamard.finalJointState` — the post-circuit joint state,
  with `finalJointState_eq_finalState_tensor` factoring off the `|−⟩` target.
-/

@[expose] public section

namespace QuantumAlg

namespace WalshHadamard

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- A Boolean oracle on `2^n` input labels. It is queried through
`Gate.xorOracle`, not through a separate oracle type. -/
abbrev Oracle (n : ℕ) : Type := Fin (2 ^ n) → Bool

/-- The standard XOR query gate for a Boolean oracle. -/
abbrev oracleGate (f : Oracle n) : Gate (n + 1) := Gate.xorOracle f

/-- The phase `(-1)^{f x}`, written as a complex scalar. -/
def phaseSign (f : Oracle n) (x : Fin (2 ^ n)) : ℂ :=
  if f x then -1 else 1

/-! ### The Walsh-Hadamard transform -/

/-- The bit of a basis label used in the Walsh-Hadamard character. The bit
order only affects nonzero rows; the zero row used by Deutsch-Jozsa is
independent of it. -/
def bit (x : Fin (2 ^ n)) (k : Fin n) : Bool := x.val.testBit k.val

/-- Parity of the bitwise inner product of two basis labels. -/
def dotParity (x y : Fin (2 ^ n)) : Bool :=
  Odd ((Finset.univ.filter fun k : Fin n => bit x k && bit y k).card)

/-- The Walsh-Hadamard sign `(-1)^{x · y}`. -/
def walshSign (x y : Fin (2 ^ n)) : ℂ := if dotParity x y then -1 else 1

@[simp]
theorem walshSign_zero_left (x : Fin (2 ^ n)) :
    walshSign (0 : Fin (2 ^ n)) x = 1 := by
  unfold walshSign dotParity bit
  simp

@[simp]
theorem walshSign_zero_right (x : Fin (2 ^ n)) :
    walshSign x (0 : Fin (2 ^ n)) = 1 := by
  unfold walshSign dotParity bit
  simp

/-- `(√(2^n))⁻¹`, the normalization scalar of the `n`-qubit Hadamard layer. -/
def invSqrtCard (n : ℕ) : ℂ := (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ)⁻¹

@[simp]
theorem invSqrtCard_mul_self (n : ℕ) :
    invSqrtCard n * invSqrtCard n = (((2 ^ n : ℕ) : ℂ)⁻¹) := by
  rw [invSqrtCard, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]
  norm_num

/-- The `n`-qubit Hadamard layer in Walsh-Hadamard closed form. -/
def hadamardLayer (n : ℕ) : Gate n :=
  fun y x => invSqrtCard n * walshSign y x

/-- The uniform input-register state produced by the first Hadamard layer. -/
def uniformState (n : ℕ) : PureState n :=
  WithLp.toLp 2 fun _ => invSqrtCard n

@[simp]
theorem uniformState_apply (x : Fin (2 ^ n)) : uniformState n x = invSqrtCard n :=
  rfl

/-- The first Hadamard layer sends `|0^n⟩` to the uniform superposition. -/
theorem hadamardLayer_apply_zero :
    (hadamardLayer n).apply (ket (0 : Fin (2 ^ n))) = uniformState n := by
  apply WithLp.ofLp_injective
  funext i
  change (hadamardLayer n).apply (ket (0 : Fin (2 ^ n))) i = uniformState n i
  rw [Gate.apply_ket]
  simp [hadamardLayer]

/-! ### The XOR phase-query pipeline -/

/-- The pre-Hadamard joint basis state `|0^n⟩ ⊗ |−⟩`. -/
def initialBasisState (n : ℕ) : PureState (n + 1) :=
  (ket (0 : Fin (2 ^ n))).tensor ketMinus

/-- The joint state queried by the XOR oracle, obtained by applying the first
Hadamard layer to the input register and leaving the `|−⟩` target alone. -/
def initialState (n : ℕ) : PureState (n + 1) :=
  ((hadamardLayer n).tensor (1 : Gate 1)).apply (initialBasisState n)

/-- The queried state is the uniform input register tensored with `|−⟩`. -/
theorem initialState_eq_uniform_tensor :
    initialState n = (uniformState n).tensor ketMinus := by
  rw [initialState, initialBasisState, Gate.tensor_apply_tensor,
    hadamardLayer_apply_zero, Gate.one_apply]

/-- The actual post-query joint state, using the XOR oracle gate. -/
def postOracleState (f : Oracle n) : PureState (n + 1) :=
  (oracleGate f).apply (initialState n)

/-- The input-register state after rewriting the oracle query by phase
kickback: `(√(2^n))⁻¹ ∑ x, (-1)^{f x}|x⟩`. -/
def afterPhaseQuery (f : Oracle n) : PureState n :=
  WithLp.toLp 2 fun x => invSqrtCard n * phaseSign f x

/-- The actual XOR-oracle query on the uniform input register and `|−⟩`
target is exactly the phase-query state tensored with the unchanged target. -/
theorem postOracleState_eq_afterPhaseQuery_tensor (f : Oracle n) :
    postOracleState f = (afterPhaseQuery f).tensor ketMinus := by
  apply WithLp.ofLp_injective
  funext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨x, b⟩, rfl⟩
  change postOracleState f (prodEquiv (x, b)) =
    ((afterPhaseQuery f).tensor ketMinus) (prodEquiv (x, b))
  rw [postOracleState, initialState_eq_uniform_tensor, oracleGate,
    Gate.xorOracle_apply, PureState.tensor_apply_prod, afterPhaseQuery]
  simp only [Equiv.symm_apply_apply, Gate.xorPerm_apply]
  by_cases h : f x
  · fin_cases b <;> simp [uniformState, h, phaseSign, ketMinus_apply]
  · simp [uniformState, h, phaseSign]

/-- The final input-register state after the second Hadamard layer, in the
phase-query view. -/
def finalState (f : Oracle n) : PureState n :=
  (hadamardLayer n).apply (afterPhaseQuery f)

/-- The actual final joint state: apply the second Hadamard layer to the
input register and leave the target qubit alone. -/
def finalJointState (f : Oracle n) : PureState (n + 1) :=
  ((hadamardLayer n).tensor (1 : Gate 1)).apply (postOracleState f)

/-- The actual final joint state factors as the final input-register state
and the unchanged `|−⟩` target. -/
theorem finalJointState_eq_finalState_tensor (f : Oracle n) :
    finalJointState f = (finalState f).tensor ketMinus := by
  rw [finalJointState, postOracleState_eq_afterPhaseQuery_tensor,
    Gate.tensor_apply_tensor, Gate.one_apply, finalState]

end

end WalshHadamard

end QuantumAlg
