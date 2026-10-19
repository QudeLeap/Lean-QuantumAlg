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
# Exact mathematical Hadamard basis action

These operator identities use the certified two-dimensional matrix and do
not assume any native gate model or execution access.
-/

namespace QuantumAlg.Gate

noncomputable section

open NormalizedVector

/-- The Hadamard operator sends zero to the positive equal superposition. -/
public lemma hadamardOperator_apply_ket0 : HOp.apply ket0 = ketPlus := by
  apply NormalizedVector.ext
  intro index
  change HOp.applyVec ((ket (R := Qubits 1) 0) : HilbertVector (Qubits 1)) index = ketPlus index
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  fin_cases index <;> simp [HOp, UnitaryOperator.ofMatrix, ketPlus_apply]

/-- The Hadamard operator sends one to the signed equal superposition. -/
public lemma hadamardOperator_apply_ket1 : HOp.apply ket1 = ketMinus := by
  apply NormalizedVector.ext
  intro index
  change HOp.applyVec ((ket (R := Qubits 1) 1) : HilbertVector (Qubits 1)) index = ketMinus index
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  fin_cases index <;> simp [HOp, UnitaryOperator.ofMatrix, ketMinus_apply]

/-- Raw-vector form of the Hadamard action on zero. -/
public lemma hadamardOperator_applyVec_ket0 :
    HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) := by
  have normalized := congrArg
    (fun state : NormalizedVector (Qubits 1) =>
      (state : HilbertVector (Qubits 1))) hadamardOperator_apply_ket0
  simpa only [UnitaryOperator.apply_coe] using normalized

end

end QuantumAlg.Gate
