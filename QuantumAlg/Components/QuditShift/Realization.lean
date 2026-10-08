/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QuditShift
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization

/-!
# Actual realizations of finite-dimensional shifts

Each requested amount requires an actual circuit in the selected model and an
exact-phase equality to the independent shift operator. This family grants no
native shift, inverse, or control operation. Resources come from its circuits.
-/

namespace QuantumAlg.QuditShift

/-- Implement every requested shift amount on this actual physical wire. -/
@[expose, implicit_reducible]
public def Realizations (gates : GateModel) (oracles : OracleModel) {count : Nat}
    (layout : QuantumLayout count) (wire : Fin count) :=
  (amount : Fin (layout.wire wire).dimension) →
    UnitaryCircuit.ExactRealization gates oracles layout (operator layout wire amount)

end QuantumAlg.QuditShift
