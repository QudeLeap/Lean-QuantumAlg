/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Exact mathematical Pauli action on the one-qubit basis

These certified operator identities describe the original basis action with
its exact sign. They grant no native instruction or control implementation.
-/

namespace QuantumAlg.Gate

noncomputable section

open NormalizedVector

/-- X exchanges zero with one, with no additional phase. -/
theorem pauliXOperator_apply_ket0 : XOp.apply ket0 = ket1 := by
  simp only [XOp, ket0, ket1, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-- X exchanges one with zero, with no additional phase. -/
theorem pauliXOperator_apply_ket1 : XOp.apply ket1 = ket0 := by
  simp only [XOp, ket0, ket1, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-- Z leaves the zero basis vector unchanged. -/
theorem pauliZOperator_apply_ket0 : ZOp.apply ket0 = ket0 := by
  apply NormalizedVector.ext
  intro index
  change ZOp.applyVec ((ket (R := Qubits 1) 0) : HilbertVector (Qubits 1)) index = ket0 index
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  fin_cases index <;> simp [ZOp, UnitaryOperator.ofMatrix, ket0, NormalizedVector.ket_apply]

/-- Z negates the one basis vector; this exact phase is retained. -/
theorem pauliZOperator_applyVec_ket1 :
    ZOp.applyVec (ket1 : HilbertVector (Qubits 1)) = -(ket1 : HilbertVector (Qubits 1)) := by
  ext index
  change ZOp.applyVec ((ket (R := Qubits 1) 1) : HilbertVector (Qubits 1)) index = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  fin_cases index <;> simp [ZOp, UnitaryOperator.ofMatrix, ket1, NormalizedVector.ket_apply]

end

end QuantumAlg.Gate
