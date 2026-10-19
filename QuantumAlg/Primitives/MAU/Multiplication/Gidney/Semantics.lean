/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Multiplication.WordAction
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Multiplication.WordAction
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program

/-!
# Exact agreement with the independent unit-multiplication operator

The actual MAC/swap/adjoint-MAC sequence equals the separately specified
two-word unitary on the complete carrier. This exact matrix equality
includes phase and therefore supports arbitrary quantum correlations.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

lemma gidneyUnitMultiplication_matrix (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.binaryMatrix (width := (Accumulate.Gidney.encoding width).width)
      (program width modulus coefficient) environment =
      wordUnitMultiplicationOperator width modulus coefficient := by
  apply Subtype.ext
  ext output input
  obtain ⟨state, rfl⟩ := (prodEquiv (m := width) (n := width)).surjective input
  have circuitAction :=
    UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
      (environment := environment)
      (program width modulus coefficient) ((Accumulate.Gidney.encoding width).encode state)
        ((Accumulate.Gidney.encoding width).encode
          (unitMultiplicationPairEquiv modulus coefficient state))
          ((gidneyUnitMultiplication_realizes width modulus coefficient).apply_encoded_ket state)
  have circuit := congrArg (fun result : NormalizedVector (Qubits (width + width)) => result output)
    circuitAction
  have semantic := congrArg
    (fun result : NormalizedVector (Qubits (width + width)) => result output)
    (wordUnitMultiplicationOperator_ket width modulus coefficient state)
  have actualColumn :=
    (HilbertOperator.applyVec_ket
      ((program width modulus coefficient).binaryMatrix environment :
        HilbertOperator (Qubits (Accumulate.Gidney.encoding width).width))
      ((Accumulate.Gidney.encoding width).encode state) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (wordUnitMultiplicationOperator width modulus coefficient :
        HilbertOperator (Qubits (width + width)))
      (prodEquiv (m := width) (n := width) state) output).symm.trans semantic
  exact actualColumn.trans semanticColumn.symm

end

end QuantumAlg.MAU.Multiplication.Gidney
