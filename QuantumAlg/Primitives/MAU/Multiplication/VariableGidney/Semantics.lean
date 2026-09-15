/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.WordAction
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

/-- Exact matrix equality of the actual three-word program and independent arithmetic target. -/
theorem variableGidney_matrix (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).matrix = wordVariableOperator width modulus := by
  apply Subtype.ext
  ext output input
  obtain ⟨⟨first, second, target⟩, rfl⟩ := (wordLabelEquiv width).surjective input
  have actual := congrArg
    (fun state : NormalizedVector (Qubits (encoding width).width) => state output)
    ((variableGidney_realizes width modulus).apply_encoded_ket (first, second, target))
  have expected := congrArg
    (fun state : NormalizedVector (Qubits (width + (width + width))) => state output)
    (wordVariableOperator_ket width modulus first second target)
  have actualColumn :=
    (HilbertOperator.applyVec_ket ((program width modulus).matrix :
      HilbertOperator (Qubits (encoding width).width))
      ((encoding width).encode (first, second, target)) output).symm.trans actual
  have expectedColumn :=
    (HilbertOperator.applyVec_ket (wordVariableOperator width modulus :
      HilbertOperator (Qubits (width + (width + width))))
      (wordLabelEquiv width (first, second, target)) output).symm.trans expected
  exact actualColumn.trans expectedColumn.symm

end

end QuantumAlg.MAU.Multiplication.VariableGidney
