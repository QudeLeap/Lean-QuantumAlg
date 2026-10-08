/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Control.Operator
public import QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Operator

/-!
# Strict Clifford+T gate model

The elementary tokens are H, S, T and CNOT. This model has no implicit Toffoli,
inverse, rotation or controlled token. Such operations need actual circuits
over these tokens before they can contribute target-model native counts.
-/

namespace QuantumAlg

namespace CliffordTGate

/-- Exactly the strict target alphabet, also used as its counting coordinates. -/
public inductive Token where
  | hadamard
  | s
  | t
  | cnot
deriving DecidableEq

/-- Each target gate acts on one or two actual qubits. -/
@[expose, implicit_reducible]
public def signature : Token → QuantumSignature
  | .hadamard | .s | .t => .qubits 1
  | .cnot => .qubits 2

noncomputable section

/-- Exact fixed operators of the strict target tokens. -/
@[expose]
public def operator : (token : Token) → UnitaryOperator (signature token).register
  | .hadamard => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm Gate.HOp
  | .s => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm Gate.SOp
  | .t => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm Gate.TOp
  | .cnot => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm Gate.CNOTOp

/-- The strict Clifford+T model for certified target circuits. -/
@[expose, implicit_reducible]
public def model : GateModel where
  Token := Token
  Coordinate := Token
  coordinateDecidableEq := inferInstance
  signature := signature
  operator := operator
  coordinate := id

/-- A strict target token emits precisely its own native coordinate. -/
@[simp] public theorem coordinate_identity (token : Token) :
    model.coordinate token = token := rfl

/-- The strict target's T coordinate retains the exact named T operator. -/
public theorem t_operator :
    model.operator .t =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm Gate.TOp := rfl

end

end CliffordTGate

end QuantumAlg
