/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Kets
public import QuantumAlg.Core.Base
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# The SWAP test

The SWAP test estimates the overlap `|<psi|phi>|^2` of two `n`-qubit states:
run the Hadamard test with the unitary that swaps the two registers
[BCWdW01, main.tex:291]. Measuring the control yields outcome `1` with
probability `(1 - |<psi|phi>|^2)/2` [BCWdW01, main.tex:328].
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

variable {n : ℕ}

/-- The register swap exchanges tensor factors. -/
theorem swapRegisters_apply_tensor (ψ φ : NormalizedVector (Qubits n)) :
    (swapRegistersOp n).applyVec
        (HilbertVector.tensor (ψ : HilbertVector (Qubits n)) (φ : HilbertVector (Qubits n))) =
      HilbertVector.tensor (φ : HilbertVector (Qubits n)) (ψ : HilbertVector (Qubits n)) := by
  ext i
  change (swapRegistersOp n).applyVec
      (HilbertVector.tensor (ψ : HilbertVector (Qubits n))
        (φ : HilbertVector (Qubits n))) i = _
  rw [swapRegistersOp, UnitaryOperator.ofPerm_applyVec,
    HilbertVector.tensor_apply,
    HilbertVector.tensor_apply, swapRegistersPerm]
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Equiv.symm_apply_apply,
    Prod.fst_swap, Prod.snd_swap]
  exact mul_comm _ _

/-- Metadata-free unitary semantics of the SWAP test. -/
def swapTest (n : ℕ) : UnitaryOperator (Qubits (1 + (n + n))) :=
  hadamardTest (swapRegistersOp n)

/-- `Re <psi ⊗ phi, SWAP (psi ⊗ phi)> = |<psi|phi>|^2`. -/
theorem re_inner_swapRegisters (ψ φ : NormalizedVector (Qubits n)) :
    (inner ℂ
      ((ψ.tensor φ : NormalizedVector (Qubits (n + n))) : HilbertVector (Qubits (n + n)))
      ((swapRegistersOp n).applyVec
        ((ψ.tensor φ : NormalizedVector (Qubits (n + n))) : HilbertVector (Qubits (n + n))))).re
      = ‖inner ℂ ψ φ‖ ^ 2 := by
  change (inner ℂ
      (HilbertVector.tensor (ψ : HilbertVector (Qubits n)) (φ : HilbertVector (Qubits n)))
      ((swapRegistersOp n).applyVec
        (HilbertVector.tensor
          (ψ : HilbertVector (Qubits n)) (φ : HilbertVector (Qubits n))))).re
    = ‖inner ℂ (ψ : HilbertVector (Qubits n)) (φ : HilbertVector (Qubits n))‖ ^ 2
  rw [swapRegisters_apply_tensor]
  rw [HilbertVector.inner_tensor_tensor,
    ← inner_conj_symm (φ : HilbertVector (Qubits n)) (ψ : HilbertVector (Qubits n)),
    Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- **SWAP test, outcome 0** [BCWdW01, main.tex:328]. -/
theorem swapTest_probQubit0_zero (ψ φ : NormalizedVector (Qubits n)) :
    NormalizedVector.probQubit0
        ((swapTest n).apply (ket0.tensor (ψ.tensor φ))) 0
      = (1 + ‖inner ℂ ψ φ‖ ^ 2) / 2 := by
  rw [swapTest, hadamardTest_probQubit0_zero, re_inner_swapRegisters]

/-- **SWAP test, outcome 1** [BCWdW01, main.tex:328]. -/
theorem swapTest_probQubit0_one (ψ φ : NormalizedVector (Qubits n)) :
    NormalizedVector.probQubit0
      ((swapTest n).apply (ket0.tensor (ψ.tensor φ))) 1 =
      (1 - ‖inner ℂ ψ φ‖ ^ 2) / 2 := by
  rw [swapTest, hadamardTest_probQubit0_one, re_inner_swapRegisters]

end

end QuantumAlg

end
