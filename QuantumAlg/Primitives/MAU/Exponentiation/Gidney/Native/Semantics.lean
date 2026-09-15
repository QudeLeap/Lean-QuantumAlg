/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Program
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Semantics

/-!
# Independent exponentiation operator in the actual prepared context

The target operator transports only the independent finite arithmetic
specification to the declared work/input basis order. The actual relabeled
oracle implements that same operator exactly. No execution projection
appears in the target operator.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

/-- Independent full-state action on the actual input and internally prepared work systems. -/
def nativeOperator (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) : UnitaryOperator (preparedContext exponentWidth width).register :=
  UnitaryOperator.reindex (preparedBasisEquiv exponentWidth width).symm
    (wordExponentiationOperator exponentWidth width modulus base)

/-- The actual placed gates equal the independent operator on the full prepared carrier. -/
theorem gidneyExponentNativeUnitary_semantics (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (nativeUnitary exponentWidth width modulus base).matrix =
      nativeOperator exponentWidth width modulus base :=
  (gidneyExponentNativeUnitary_matrix exponentWidth width modulus base).trans
    (congrArg (fun operator : UnitaryOperator (Qubits (oracleEncoding exponentWidth width).width) =>
      UnitaryOperator.reindex (preparedBasisEquiv exponentWidth width).symm operator)
      (gidneyExponentOracle_matrix exponentWidth width modulus base))

end

end QuantumAlg.MAU.Exponentiation.Gidney
