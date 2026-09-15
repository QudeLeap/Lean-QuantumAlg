/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Multiplication.WordAction
import all QuantumAlg.Core.Base.Gate.Unitary
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

theorem gidneyUnitMultiplication_matrix (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).matrix =
      wordUnitMultiplicationOperator width modulus coefficient := by
  apply Subtype.ext
  ext output input
  obtain ⟨state, rfl⟩ := (prodEquiv (m := width) (n := width)).surjective input
  have circuit := congrArg (fun result : NormalizedVector (Qubits (width + width)) => result output)
    ((gidneyUnitMultiplication_realizes width modulus coefficient).apply_encoded_ket state)
  have semantic := congrArg
    (fun result : NormalizedVector (Qubits (width + width)) => result output)
    (wordUnitMultiplicationOperator_ket width modulus coefficient state)
  have actualColumn :=
    (HilbertOperator.applyVec_ket
      ((program width modulus coefficient).matrix :
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
