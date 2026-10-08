/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Original addressed SWAP operator

The target retains the original three addressed CNOT operators on the full
qubit register. Its semantics is independent of any executable native model
or resource coordinate.
-/

namespace QuantumAlg

noncomputable section

/-- A genuine addressed wire swap, decomposed semantically into the usual
three addressed CNOT permutations. -/
public def qftSwapOperator {n : Nat} (left right : Fin n) (hne : left ≠ right) :
    UnitaryOperator (Qubits n) :=
  Mul.mul
    (Mul.mul
      (QubitPrimitive.operator (.cnot left right hne))
      (QubitPrimitive.operator (.cnot right left hne.symm)))
    (QubitPrimitive.operator (.cnot left right hne))

end

end QuantumAlg
