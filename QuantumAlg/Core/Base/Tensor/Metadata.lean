/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.State.Pure
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Metadata-aware tensor adapters

Placed states reuse the certified mathematical tensor product while composing
their physical placement metadata. Preparation resources stay with executable
preparation evidence.
-/

section

namespace QuantumAlg

variable {m n : ℕ}

namespace PureState

noncomputable section

/-- Tensor product of placed pure states. -/
def tensor (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    PureState (Qubits (m + n)) :=
  ofNormalized (ψ.state.tensor φ.state)
    (ψ.system_idx ++ φ.system_idx)

@[simp]
theorem coe_tensor (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    ((ψ.tensor φ : PureState (Qubits (m + n))) : HilbertVector (Qubits (m + n))) =
      HilbertVector.tensor (ψ : HilbertVector (Qubits m))
        (φ : HilbertVector (Qubits n)) := rfl

@[simp]
theorem tensor_system_idx (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    (ψ.tensor φ).system_idx = ψ.system_idx ++ φ.system_idx := rfl

@[simp]
theorem tensor_apply (ψ : PureState (Qubits m)) (φ : PureState (Qubits n))
    (i : Fin (2 ^ (m + n))) :
    ψ.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl

theorem tensor_apply_prod (ψ : PureState (Qubits m)) (φ : PureState (Qubits n))
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    ψ.tensor φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

/-- Placed basis states tensor by composing their labels and placements. -/
theorem tensor_basis (x : Fin (2 ^ m)) (y : Fin (2 ^ n))
    (leftSystem rightSystem : List Nat) :
    (basis x leftSystem).tensor (basis y rightSystem) =
      basis (prodEquiv (x, y)) (leftSystem ++ rightSystem) := by
  apply PureState.ext
  · intro i
    change (NormalizedVector.ket x).tensor (NormalizedVector.ket y) i =
      NormalizedVector.ket (prodEquiv (x, y)) i
    rw [NormalizedVector.tensor_ket]
  · rfl

theorem norm_tensor (ψ : PureState (Qubits m)) (φ : PureState (Qubits n)) :
    ‖ψ.tensor φ‖ = ‖ψ‖ * ‖φ‖ := by
  change
    ‖HilbertVector.tensor (ψ : HilbertVector (Qubits m))
      (φ : HilbertVector (Qubits n))‖ =
      ‖(ψ : HilbertVector (Qubits m))‖ * ‖(φ : HilbertVector (Qubits n))‖
  rw [HilbertVector.norm_tensor]

theorem inner_tensor_tensor (ψ ψ' : PureState (Qubits m))
    (φ φ' : PureState (Qubits n)) :
    inner ℂ (ψ.tensor φ) (ψ'.tensor φ') =
      inner ℂ ψ ψ' * inner ℂ φ φ' := by
  change inner ℂ
      (HilbertVector.tensor (ψ : HilbertVector (Qubits m))
        (φ : HilbertVector (Qubits n)))
      (HilbertVector.tensor (ψ' : HilbertVector (Qubits m))
        (φ' : HilbertVector (Qubits n))) =
    inner ℂ (ψ : HilbertVector (Qubits m)) (ψ' : HilbertVector (Qubits m)) *
      inner ℂ (φ : HilbertVector (Qubits n)) (φ' : HilbertVector (Qubits n))
  rw [HilbertVector.inner_tensor_tensor]

end

end PureState

end QuantumAlg

end
