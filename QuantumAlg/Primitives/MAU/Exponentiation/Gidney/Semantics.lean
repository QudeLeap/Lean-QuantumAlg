/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Exponentiation.WordAction
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Primitives.MAU.Exponentiation.WordAction
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Oracle

/-!
# Exact actual-oracle agreement with the independent exponentiation operator

The selected-multiplier fold, literal CNOT copy, and actual adjoint equal
the independent finite arithmetic operator on the complete four-field
carrier. Exact matrix equality preserves every relative phase and permits
arbitrary external reference correlations.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

theorem gidneyExponentOracle_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (oracleProgram exponentWidth width modulus base).matrix =
      wordExponentiationOperator exponentWidth width modulus base := by
  apply Subtype.ext
  ext output input
  obtain ⟨state, rfl⟩ := (wordExponentiationBasis exponentWidth width).surjective input
  have circuit := congrArg
    (fun result : NormalizedVector (Qubits ((exponentWidth + (width + width)) + width)) =>
      result output)
    ((gidneyExponentOracle_realizes exponentWidth width modulus base).apply_encoded_ket state)
  have semantic := congrArg
    (fun result : NormalizedVector (Qubits ((exponentWidth + (width + width)) + width)) =>
      result output)
    (wordExponentiationOperator_ket exponentWidth width modulus base state)
  have actualColumn :=
    (HilbertOperator.applyVec_ket
      ((oracleProgram exponentWidth width modulus base).matrix :
        HilbertOperator (Qubits (oracleEncoding exponentWidth width).width))
      ((oracleEncoding exponentWidth width).encode state) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (wordExponentiationOperator exponentWidth width modulus base :
        HilbertOperator (Qubits ((exponentWidth + (width + width)) + width)))
      (wordExponentiationBasis exponentWidth width state) output).symm.trans semantic
  exact actualColumn.trans semanticColumn.symm

end

end QuantumAlg.MAU.Exponentiation.Gidney
