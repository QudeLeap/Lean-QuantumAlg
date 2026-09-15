/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Direct all-zero computational-basis reflection

This component owns the opaque direct-gate boundary for the reusable
all-zero-state reflection. Algorithms may compose the leaf but do not declare
their own reusable gate/operator pairing.
-/

section

namespace QuantumAlg
namespace ZeroReflection

/-- The direct unitary `2|0^n><0^n| - I`. -/
def zeroReflectionOperator (n : Nat) : UnitaryOperator (Qubits n) :=
  OrthogonalProjector.rankOneReflectionOp
    (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)))

/-- Stable resource coordinate for the opaque all-zero reflection. -/
def gateLabel (n : Nat) : Resource.GateLabel :=
  { family := "QuantumAlg.Components.Oracle.ZeroReflection"
    name := "zero-state-reflection"
    parameters := [n] }

/-- Strict event coordinate of one direct all-zero reflection. -/
def event (n : Nat) : Resource.Event .quantum :=
  .gate (gateLabel n)

/-- Direct all-zero-reflection occurrence at a caller-supplied placement. -/
def zeroReflectionLeafAt (n : Nat) (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.gate (gateLabel n) systemIdx (zeroReflectionOperator n)

end ZeroReflection
end QuantumAlg

end
