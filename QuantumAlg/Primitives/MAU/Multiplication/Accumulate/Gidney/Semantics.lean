/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Multiplication.Accumulate.WordAction
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.WordAction
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Program

/-!
# Exact equality with the independent accumulation operator

The actual internally borrowed stage sequence equals the finite arithmetic
permutation on the whole two-word carrier. Equality includes phase, extends
to every incoming mixed or pure state, and preserves correlations with
arbitrary external references.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

lemma gidneyAccumulate_matrix (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (program width modulus coefficient).binaryMatrix environment =
      wordAccumulateOperator width modulus coefficient := by
  apply Subtype.ext
  ext output input
  obtain ⟨⟨source, target⟩, rfl⟩ := (prodEquiv (m := width) (n := width)).surjective input
  have circuitAction :=
    UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
      (environment := environment)
      (program width modulus coefficient) ((encoding width).encode (source, target))
        ((encoding width).encode
          (prefixOutput modulus coefficient width (source, target)))
          ((gidneyAccumulate_realizes width modulus coefficient).apply_encoded_ket
            (source, target))
  have circuit := congrArg (fun state : NormalizedVector (Qubits (width + width)) => state output)
    circuitAction
  have semantic := congrArg (fun state : NormalizedVector (Qubits (width + width)) => state output)
    (wordAccumulateOperator_ket width modulus coefficient source target)
  have actualColumn :=
    (HilbertOperator.applyVec_ket
      ((program width modulus coefficient).binaryMatrix environment :
        HilbertOperator (Qubits (encoding width).width))
      ((encoding width).encode (source, target)) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (wordAccumulateOperator width modulus coefficient : HilbertOperator (Qubits (width + width)))
      (prodEquiv (m := width) (n := width) (source, target)) output).symm.trans semantic
  exact actualColumn.trans semanticColumn.symm

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
