/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.Xor

public import QuantumAlg.Components.Control
public import QuantumAlg.Components.Kets
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Oracle.Xor.Operator
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
public import Mathlib.Analysis.Complex.Exponential

/-!
# Phase kickback

Querying the XOR oracle of `f` with the target qubit in `|−⟩` leaves the
target untouched and kicks the value of `f` back into the phase of the
input register [dW19, qcnotes.tex:1167]:

`U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} · (|x⟩ ⊗ |−⟩)`,

the "phase kick-back trick" [dW19, qcnotes.tex:1173]. Dually, a `|+⟩`
target is left invariant, which lets circuits choose per-branch whether a
phase query happens [dW19, qcnotes.tex:1173].

The eigenvalue form replaces the oracle by a controlled unitary: if the
target register holds an eigenstate `|u⟩` of `U`, the eigenvalue `e^{iθ}`
is "kicked back" in front of the `|1⟩` component of the control
[CEMM98, cemm6.tex:163].

## Main results

- `QuantumAlg.PhaseKickback.xor_action` — `U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} (|x⟩ ⊗ |−⟩)`,
  with the sign written as `if f x then -1 else 1`.
- `QuantumAlg.xorOracleOp_apply_tensor_ketPlus` —
  `U_f (|x⟩ ⊗ |+⟩) = |x⟩ ⊗ |+⟩`.
- `QuantumAlg.GeneralizedPhaseKickback.eigenvalue_action` —
  `c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩` when
  `U |u⟩ = e^{iθ} |u⟩`.
-/

section

namespace QuantumAlg

open NormalizedVector

noncomputable section

variable {n : ℕ}

/-- **Eigenvalue phase kickback** [CEMM98, cemm6.tex:163]: if the target
register holds an eigenstate `|u⟩` of `U` with eigenvalue `e^{iθ}`, the
controlled `U` leaves the target unchanged and kicks the eigenvalue back
onto the `|1⟩` component of the control [CEMM98, cemm6.tex:142]:

`c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩`. -/
public theorem GeneralizedPhaseKickback.eigenvalue_action (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp (θ * Complex.I) • (u : HilbertVector (Qubits n))) (a b : ℂ) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor
          ((a • ket0 + b • ket1 : HilbertVector (Qubits 1))) (u : HilbertVector (Qubits n)))
      =
      HilbertVector.tensor
        ((a • ket0 + (Complex.exp (θ * Complex.I) * b) • ket1 : HilbertVector (Qubits 1)))
        (u : HilbertVector (Qubits n)) := by
  rw [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.smul_tensor,
    UnitaryOperator.applyVec_add, UnitaryOperator.applyVec_smul,
    UnitaryOperator.applyVec_smul,
    UnitaryOperator.controlledQubits_applyVec_ket0_tensor,
    UnitaryOperator.controlledQubits_applyVec_ket1_tensor]
  rw [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.smul_tensor]
  rw [hu, HilbertVector.tensor_smul, smul_smul]
  module


end

end QuantumAlg

end
