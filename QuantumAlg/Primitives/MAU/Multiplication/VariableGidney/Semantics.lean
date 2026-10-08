/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.WordAction
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.WordAction
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Program

/-!
# Native variable multiplication equals its independent full-state target

Equality of the whole operators includes every relative phase, arbitrary
coherent inputs, and mixed-state extensions with external references. The
specification operator is built only from finite arithmetic; the actual
program uses the previously proved native controlled MAC stages.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

/-- Exact binary matrix equality of the native program and independent arithmetic. -/
theorem variableGidney_matrix (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).binaryMatrix = wordVariableOperator width modulus := by
  apply Subtype.ext
  ext output input
  obtain ⟨⟨first, second, target⟩, rfl⟩ := (wordLabelEquiv width).surjective input
  have circuitAction :=
    UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
      (program width modulus) ((encoding width).encode (first, second, target))
        ((encoding width).encode
          (prefixOutput modulus width (first, second, target)))
          ((variableGidney_realizes width modulus).apply_encoded_ket
            (first, second, target))
  have circuit := congrArg
    (fun state : NormalizedVector (Qubits (width + (width + width))) => state output)
    circuitAction
  have semantic := congrArg
    (fun state : NormalizedVector (Qubits (width + (width + width))) => state output)
    (wordVariableOperator_ket width modulus first second target)
  have actualColumn :=
    (HilbertOperator.applyVec_ket
      ((program width modulus).binaryMatrix : HilbertOperator (Qubits (encoding width).width))
      ((encoding width).encode (first, second, target)) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (wordVariableOperator width modulus : HilbertOperator (Qubits (width + (width + width))))
      (wordLabelEquiv width (first, second, target)) output).symm.trans semantic
  exact actualColumn.trans semanticColumn.symm

end

end QuantumAlg.MAU.Multiplication.VariableGidney
