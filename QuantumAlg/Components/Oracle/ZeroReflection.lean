/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Mathematical all-zero computational-basis reflection

The independent operator fixes the all-zero state and negates its orthogonal
complement. Native implementations live in the small-width and restored-work
program modules; this operator itself grants no gate or oracle instruction.
-/

section

namespace QuantumAlg
namespace ZeroReflection

/-- The direct unitary `2|0^n><0^n| - I`. -/
def zeroReflectionOperator (n : Nat) : UnitaryOperator (Qubits n) :=
  OrthogonalProjector.rankOneReflectionOp
    (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)))

end ZeroReflection
end QuantumAlg

end
