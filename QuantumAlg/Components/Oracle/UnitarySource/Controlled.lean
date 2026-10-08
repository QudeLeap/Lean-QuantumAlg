/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Oracle.UnitarySource.Model
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# One explicitly granted controlled source query

The access model grants the controlled query on the complete leading-control
and target word. It has its own oracle coordinate and exact source operator
[CEMM98, cemm6.tex:140-166]. Ordinary access alone does not supply this query.
-/

namespace QuantumAlg.UnitarySource

noncomputable section

/-- Execute the granted controlled query on its complete canonical physical word. -/
public def controlledProgram (gates : GateModel) {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    UnitaryCircuit gates (model unitary true)
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  .query (OracleModel.Application.onPlacement (model unitary true) (.controlled rfl)
    (QuantumSignature.qubits (1 + width)).canonicalPlacement)

/-- The query's actual physical matrix is exactly the declared controlled source operator. -/
theorem controlledProgram_matrix (gates : GateModel) {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (controlledProgram gates unitary).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
        (UnitaryOperator.controlledQubits unitary) := by
  rw [controlledProgram, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  apply Subtype.ext
  rfl

/-- The complete event pool contains one granted controlled query. -/
theorem controlledProgram_events (gates : GateModel) {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (controlledProgram gates unitary).eventCost =
      ResourcePool.singleton (model := .quantum gates (model unitary true))
        (.oracle Coordinate.controlled) := rfl

/-- The abstract controlled query occupies one dependency step. -/
theorem controlledProgram_depth (gates : GateModel) {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (controlledProgram gates unitary).evaluatedEventDepth (fun _ => 1) = 1 := rfl

end

end QuantumAlg.UnitarySource
