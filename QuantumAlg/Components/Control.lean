/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Control.Operator
public import QuantumAlg.Core.Base.Tensor.Certified
public import QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Components.Kets

/-!
# Controlled unitary operators

`UnitaryOperator.controlledQubits U` is the metadata-free `(1 + n)`-qubit
operator that applies `U` when the leading control qubit is `|1>` and acts as
the identity on `|0>` [CEMM98, cemm6.tex:127]. It specializes the generic
activation-parametric `UnitaryOperator.controlled` construction and reindexes
the product register to the canonical flattened qubit register.

Physical control is represented by certified `UnitaryCircuit` construction; this
module contains only the metadata-free operator identities used there.
-/

section

namespace QuantumAlg

open NormalizedVector

noncomputable section

variable {n : ℕ}

namespace HilbertOperator

/-! ## Computational-basis projectors -/

/-- The one-qubit projector `|0><0| = [[1, 0], [0, 0]]`. -/
@[expose] public def proj0 : HilbertOperator (Qubits 1) := !![(1 : ℂ), 0; 0, 0]

/-- The one-qubit projector `|1><1| = [[0, 0], [0, 1]]`. -/
@[expose] public def proj1 : HilbertOperator (Qubits 1) := !![(0 : ℂ), 0; 0, 1]

@[simp]
theorem proj0_applyVec_ket0 :
    applyVec proj0 (ket0 : HilbertVector (Qubits 1)) =
      (ket0 : HilbertVector (Qubits 1)) := by
  ext i
  rw [ket0, HilbertOperator.applyVec_ket]
  fin_cases i <;> simp [proj0]

@[simp]
theorem proj0_applyVec_ket1 :
    applyVec proj0 (ket1 : HilbertVector (Qubits 1)) = 0 := by
  ext i
  rw [ket1, HilbertOperator.applyVec_ket]
  fin_cases i <;> simp [proj0]

@[simp]
theorem proj1_applyVec_ket0 :
    applyVec proj1 (ket0 : HilbertVector (Qubits 1)) = 0 := by
  ext i
  rw [ket0, HilbertOperator.applyVec_ket]
  fin_cases i <;> simp [proj1]

@[simp]
theorem proj1_applyVec_ket1 :
    applyVec proj1 (ket1 : HilbertVector (Qubits 1)) =
      (ket1 : HilbertVector (Qubits 1)) := by
  ext i
  rw [ket1, HilbertOperator.applyVec_ket]
  fin_cases i <;> simp [proj1]

end HilbertOperator

namespace UnitaryOperator

/-! ## Metadata-free qubit controls -/

/-- Add a leading qubit control, active on `|1>`, and flatten the product
register to the canonical `(1 + n)`-qubit indexing. -/
public def controlledQubits (U : UnitaryOperator (Qubits n)) :
    UnitaryOperator (Qubits (1 + n)) :=
  reindex (prodEquiv (m := 1) (n := n))
    (controlled (Qubits 1) (1 : Fin (2 ^ 1)) U)

/-- Add a leading qubit control active on `|0>`. -/
public def controlledQubitsOnZero (U : UnitaryOperator (Qubits n)) :
    UnitaryOperator (Qubits (1 + n)) :=
  reindex (prodEquiv (m := 1) (n := n))
    (controlled (Qubits 1) (0 : Fin (2 ^ 1)) U)

/-- Raw block-matrix view of a leading control active on `|1>`. -/
theorem coe_controlledQubits (U : UnitaryOperator (Qubits n)) :
    ((controlledQubits U : UnitaryOperator (Qubits (1 + n))) :
      HilbertOperator (Qubits (1 + n))) =
      HilbertOperator.tensor HilbertOperator.proj0
          (1 : HilbertOperator (Qubits n)) +
        HilbertOperator.tensor HilbertOperator.proj1
          (U : HilbertOperator (Qubits n)) := by
  ext i j
  change
    controlled (Qubits 1) (1 : Fin (2 ^ 1)) U
        ((prodEquiv (m := 1) (n := n)).symm i)
        ((prodEquiv (m := 1) (n := n)).symm j) =
      HilbertOperator.proj0
          ((prodEquiv (m := 1) (n := n)).symm i).1
          ((prodEquiv (m := 1) (n := n)).symm j).1 *
          (1 : HilbertOperator (Qubits n))
            ((prodEquiv (m := 1) (n := n)).symm i).2
            ((prodEquiv (m := 1) (n := n)).symm j).2 +
        HilbertOperator.proj1
          ((prodEquiv (m := 1) (n := n)).symm i).1
          ((prodEquiv (m := 1) (n := n)).symm j).1 *
          U ((prodEquiv (m := 1) (n := n)).symm i).2
            ((prodEquiv (m := 1) (n := n)).symm j).2
  generalize (prodEquiv (m := 1) (n := n)).symm i = input
  generalize (prodEquiv (m := 1) (n := n)).symm j = output
  rcases input with ⟨controlIn, targetIn⟩
  rcases output with ⟨controlOut, targetOut⟩
  change
    controlled (Qubits 1) (1 : Fin (2 ^ 1)) U
        (controlIn, targetIn) (controlOut, targetOut) = _
  rw [controlled_apply (Qubits 1) (1 : Fin (2 ^ 1)) U
    (controlIn, targetIn) (controlOut, targetOut)]
  fin_cases controlIn <;> fin_cases controlOut
  all_goals
    simp [HilbertOperator.proj0, HilbertOperator.proj1, Matrix.one_apply]

/-- Raw block-matrix view of a leading control active on `|0>`. -/
public theorem coe_controlledQubitsOnZero (U : UnitaryOperator (Qubits n)) :
    ((controlledQubitsOnZero U : UnitaryOperator (Qubits (1 + n))) :
      HilbertOperator (Qubits (1 + n))) =
      HilbertOperator.tensor HilbertOperator.proj0
          (U : HilbertOperator (Qubits n)) +
        HilbertOperator.tensor HilbertOperator.proj1
          (1 : HilbertOperator (Qubits n)) := by
  ext i j
  change
    controlled (Qubits 1) (0 : Fin (2 ^ 1)) U
        ((prodEquiv (m := 1) (n := n)).symm i)
        ((prodEquiv (m := 1) (n := n)).symm j) =
      HilbertOperator.proj0
          ((prodEquiv (m := 1) (n := n)).symm i).1
          ((prodEquiv (m := 1) (n := n)).symm j).1 *
          U ((prodEquiv (m := 1) (n := n)).symm i).2
            ((prodEquiv (m := 1) (n := n)).symm j).2 +
        HilbertOperator.proj1
          ((prodEquiv (m := 1) (n := n)).symm i).1
          ((prodEquiv (m := 1) (n := n)).symm j).1 *
          (1 : HilbertOperator (Qubits n))
            ((prodEquiv (m := 1) (n := n)).symm i).2
            ((prodEquiv (m := 1) (n := n)).symm j).2
  generalize (prodEquiv (m := 1) (n := n)).symm i = input
  generalize (prodEquiv (m := 1) (n := n)).symm j = output
  rcases input with ⟨controlIn, targetIn⟩
  rcases output with ⟨controlOut, targetOut⟩
  change
    controlled (Qubits 1) (0 : Fin (2 ^ 1)) U
        (controlIn, targetIn) (controlOut, targetOut) = _
  rw [controlled_apply (Qubits 1) (0 : Fin (2 ^ 1)) U
    (controlIn, targetIn) (controlOut, targetOut)]
  fin_cases controlIn <;> fin_cases controlOut
  all_goals
    simp [HilbertOperator.proj0, HilbertOperator.proj1, Matrix.one_apply]

/-- On the `|0>` branch a leading `|1>`-controlled operator is the identity. -/
@[simp]
theorem controlledQubits_applyVec_ket0_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits n)) :
    (controlledQubits U).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec
    (controlledQubits U : HilbertOperator (Qubits (1 + n))) _ i = _
  rw [coe_controlledQubits, HilbertOperator.add_applyVec,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.proj0_applyVec_ket0,
    HilbertOperator.proj1_applyVec_ket0,
    HilbertOperator.one_applyVec, HilbertVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|1>` branch a leading `|1>`-controlled operator applies `U`. -/
@[simp]
theorem controlledQubits_applyVec_ket1_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits n)) :
    (controlledQubits U).applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) ψ) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) (U.applyVec ψ) := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec
    (controlledQubits U : HilbertOperator (Qubits (1 + n))) _ i = _
  rw [coe_controlledQubits, HilbertOperator.add_applyVec,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.proj0_applyVec_ket1,
    HilbertOperator.proj1_applyVec_ket1,
    HilbertVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|0>` branch a zero-controlled operator applies `U`. -/
@[simp]
public theorem controlledQubitsOnZero_applyVec_ket0_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits n)) :
    (controlledQubitsOnZero U).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (U.applyVec ψ) := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec
    (controlledQubitsOnZero U : HilbertOperator (Qubits (1 + n))) _ i = _
  rw [coe_controlledQubitsOnZero, HilbertOperator.add_applyVec,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.proj0_applyVec_ket0,
    HilbertOperator.proj1_applyVec_ket0,
    HilbertVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|1>` branch a zero-controlled operator is the identity. -/
@[simp]
public theorem controlledQubitsOnZero_applyVec_ket1_tensor
    (U : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits n)) :
    (controlledQubitsOnZero U).applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) ψ) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) ψ := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec
    (controlledQubitsOnZero U : HilbertOperator (Qubits (1 + n))) _ i = _
  rw [coe_controlledQubitsOnZero, HilbertOperator.add_applyVec,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.proj0_applyVec_ket1,
    HilbertOperator.proj1_applyVec_ket1,
    HilbertOperator.one_applyVec, HilbertVector.zero_tensor, PiLp.add_apply]
  simp

end UnitaryOperator

end

end QuantumAlg

end
