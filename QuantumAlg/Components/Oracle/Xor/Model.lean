/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.Xor.Operator
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Oracle.Xor.Operator
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.Oracle.Model
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Explicit Boolean XOR oracle access

A declaration fixes the Boolean function and grants its XOR query on the
ordered input and target qubits [dW19, qcnotes.tex:1149-1173]. The actual circuit
emits one oracle event; the black-box implementation is not a native gate.
-/

namespace QuantumAlg.XorOracle

noncomputable section

/-- The one query coordinate of a fixed Boolean XOR oracle. -/
public inductive Coordinate where
  | xor
  deriving DecidableEq

/-- Exactly one access form with the declared Boolean function's fixed semantics. -/
@[expose, implicit_reducible]
public def model {width : Nat} (function : Fin (2 ^ width) → Bool) : OracleModel where
  Query := Unit
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature _ := QuantumSignature.qubits (width + 1)
  operator _ :=
    UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (width + 1)).symm
      (xorOracleOp function)
  coordinate _ := .xor

/-- One actual granted XOR query on its canonical ordered input and target systems. -/
public def circuit (gates : GateModel) {width : Nat} (function : Fin (2 ^ width) → Bool) :
    UnitaryCircuit gates (model function)
      (QuantumSignature.qubits (width + 1)).canonicalPlacement.layout :=
  .query (OracleModel.Application.onPlacement (model function) ()
    (QuantumSignature.qubits (width + 1)).canonicalPlacement)

/-- The actual query has precisely the declared full XOR operator on physical coordinates. -/
public theorem xorOracle_native_matrix (gates : GateModel) {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    (circuit gates function).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (width + 1)).symm
        (xorOracleOp function) := by
  rw [circuit, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  apply Subtype.ext
  rfl

/-- The executable query emits exactly one oracle event and no native gate events. -/
public theorem xorOracle_native_eventCost (gates : GateModel) {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    (circuit gates function).eventCost =
      ResourcePool.singleton (model := .quantum gates (model function)) (.oracle .xor) := by
  rfl

/-- One abstract query occupies one dependency step. -/
public theorem xorOracle_native_unit_depth (gates : GateModel) {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    (circuit gates function).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

end

end QuantumAlg.XorOracle
