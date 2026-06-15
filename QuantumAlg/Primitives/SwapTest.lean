/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.HadamardTest

/-!
# The SWAP test

The SWAP test estimates the overlap `|⟨ψ|φ⟩|²` of two `n`-qubit states:
run the Hadamard test with the unitary that swaps the two registers
[BCWdW01, main.tex:291]. Measuring the control yields outcome `1` with
probability `(1 − |⟨ψ|φ⟩|²)/2` [BCWdW01, main.tex:328] — `0` if
`ψ = φ`, and bounded away from `0` when the overlap is small, which is
the one-sided equality test used in quantum fingerprinting. The SWAP
test goes back to the symmetrization-based stabilization of Barenco,
Berthiaume, Deutsch, Ekert, Jozsa and Macchiavello (1997) (source
`barenco-1997-symmetrization`).

## Conventions

- The control is qubit 0; the two `n`-qubit registers occupy qubits
  `1, …, n` and `n+1, …, 2n` (groupings `1 + (n + n)`, big-endian).
- `swapRegisters n` is the permutation gate exchanging the two
  registers: `SWAP (ψ ⊗ φ) = φ ⊗ ψ`.

## Main results

- `QuantumAlg.swapRegisters` — the register-swap gate on `n + n` qubits.
- `QuantumAlg.swapTest` — the circuit `(H ⊗ I) · c-SWAP · (H ⊗ I)`.
- `QuantumAlg.swapTest_probQubit0_zero` / `_one` — outcome probabilities
  `(1 ± |⟨ψ|φ⟩|²)/2`.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- The permutation of joint basis labels that exchanges the two
`n`-qubit registers. -/
def swapRegistersPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ (n + n))) :=
  ((prodEquiv (m := n) (n := n)).symm.trans
    (Equiv.prodComm (Fin (2 ^ n)) (Fin (2 ^ n)))).trans prodEquiv

/-- The register-swap gate `SWAP : Gate (n + n)`, as a basis
permutation: `SWAP (ψ ⊗ φ) = φ ⊗ ψ` [BCWdW01, main.tex:295]. -/
def swapRegisters (n : ℕ) : Gate (n + n) := ofPerm (swapRegistersPerm n)

theorem swapRegisters_mem_unitaryGroup (n : ℕ) :
    swapRegisters n ∈ Matrix.unitaryGroup (Fin (2 ^ (n + n))) ℂ :=
  ofPerm_mem_unitaryGroup _

/-- The register swap exchanges tensor factors:
`SWAP (ψ ⊗ φ) = φ ⊗ ψ`. -/
theorem swapRegisters_apply_tensor (ψ φ : PureState n) :
    (swapRegisters n).apply (ψ.tensor φ) = φ.tensor ψ := by
  apply WithLp.ofLp_injective
  funext i
  change (swapRegisters n).apply (ψ.tensor φ) i = φ.tensor ψ i
  rw [swapRegisters, ofPerm_apply, PureState.tensor_apply,
    PureState.tensor_apply, swapRegistersPerm]
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Equiv.symm_apply_apply,
    Prod.fst_swap, Prod.snd_swap]
  exact mul_comm _ _

/-- The SWAP test circuit: the Hadamard test of the register swap
[BCWdW01, main.tex:291] — `(H ⊗ I) · c-SWAP · (H ⊗ I)`. -/
def swapTest (n : ℕ) : Gate (1 + (n + n)) :=
  hadamardTest (swapRegisters n)

/-- `Re ⟨ψ ⊗ φ, SWAP (ψ ⊗ φ)⟩ = |⟨ψ|φ⟩|²`: the SWAP expectation realizes
the squared overlap. -/
theorem re_inner_swapRegisters (ψ φ : PureState n) :
    (inner ℂ (ψ.tensor φ) ((swapRegisters n).apply (ψ.tensor φ))).re
      = ‖inner ℂ ψ φ‖ ^ 2 := by
  rw [swapRegisters_apply_tensor, PureState.inner_tensor_tensor,
    ← inner_conj_symm φ ψ, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- **SWAP test, outcome 0** [BCWdW01, main.tex:328]: for normalized
states the control reads `0` with probability `(1 + |⟨ψ|φ⟩|²)/2`. -/
theorem swapTest_probQubit0_zero (ψ φ : PureState n)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    probQubit0 ((swapTest n).apply (ket0.tensor (ψ.tensor φ))) 0
      = (1 + ‖inner ℂ ψ φ‖ ^ 2) / 2 := by
  rw [swapTest, hadamardTest_probQubit0_zero _
      (by rw [PureState.norm_tensor, hψ, hφ, one_mul])
      (swapRegisters_mem_unitaryGroup n),
    re_inner_swapRegisters]

/-- **SWAP test, outcome 1** [BCWdW01, main.tex:328]: the control reads
`1` with probability `(1 − |⟨ψ|φ⟩|²)/2` — zero iff the overlap is
maximal, the one-sided error of quantum fingerprinting. -/
theorem swapTest_probQubit0_one (ψ φ : PureState n)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    probQubit0 ((swapTest n).apply (ket0.tensor (ψ.tensor φ))) 1
      = (1 - ‖inner ℂ ψ φ‖ ^ 2) / 2 := by
  rw [swapTest, hadamardTest_probQubit0_one _
      (by rw [PureState.norm_tensor, hψ, hφ, one_mul])
      (swapRegisters_mem_unitaryGroup n),
    re_inner_swapRegisters]

end

end QuantumAlg
