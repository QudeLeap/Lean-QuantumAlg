/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.State.Normalized

/-!
# One-qubit vector decomposition in the computational basis
-/

namespace QuantumAlg

open NormalizedVector

noncomputable section

/-- A one-qubit state is its `|0⟩`/`|1⟩` coordinate combination. -/
lemma single_qubit_vec_decomp (ψ : HilbertVector (Qubits 1)) :
    ψ =
      (ψ 0) • (ket0 : HilbertVector (Qubits 1)) + (ψ 1) • (ket1 : HilbertVector (Qubits 1)) := by
  ext i
  fin_cases i <;>
    simp [ket0, ket1, ket_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

lemma single_qubit_decomp (ψ : NormalizedVector (Qubits 1)) :
    (ψ : HilbertVector (Qubits 1)) =
      (ψ 0) • (ket0 : HilbertVector (Qubits 1)) + (ψ 1) • (ket1 : HilbertVector (Qubits 1)) :=
  single_qubit_vec_decomp (ψ : HilbertVector (Qubits 1))

end

end QuantumAlg
