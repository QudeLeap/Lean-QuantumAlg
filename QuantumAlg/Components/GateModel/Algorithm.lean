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
public import QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Components.QubitPrimitive.Operator
public import QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Operator

/-!
# Default algorithm gate model

Elementary operations are Toffoli, CNOT, and an arbitrary one-qubit unitary.
The one-qubit coordinate counts the actual unitary token without discarding it.
Preparation, measurement and oracle access are separate execution operations.
-/

namespace QuantumAlg

namespace AlgorithmGate

/-- The default algorithm model's three independent native gate counts. -/
public inductive Coordinate where
  | toffoli
  | cnot
  | singleQubit
deriving DecidableEq

/-- Gate instances retain the full one-qubit operator parameter. -/
public inductive Token where
  | toffoli
  | cnot
  | singleQubit (operator : UnitaryOperator (Qubits 1))

/-- Each default-model token has its fixed physical arity. -/
@[expose, implicit_reducible]
public def signature : Token → QuantumSignature
  | .toffoli => .qubits 3
  | .cnot => .qubits 2
  | .singleQubit _ => .qubits 1

/-- Resource coordinates classify tokens without replacing their semantics. -/
@[expose]
public def coordinate : Token → Coordinate
  | .toffoli => .toffoli
  | .cnot => .cnot
  | .singleQubit _ => .singleQubit

noncomputable section

/-- Fixed canonical Toffoli, CNOT and parameterized one-qubit semantics. -/
@[expose]
public def operator : (token : Token) → UnitaryOperator (signature token).register
  | .toffoli =>
    UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 3).symm
      (QubitPrimitive.operator
        (.toffoli 0 1 2 (by decide) (by decide) (by decide) : QubitPrimitive 3))
  | .cnot => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm Gate.CNOTOp
  | .singleQubit op => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm op

/-- The default native model used for logical algorithm resource claims. -/
@[expose, implicit_reducible]
public def model : GateModel where
  Token := Token
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature := signature
  operator := operator
  coordinate := coordinate

/-- Every one-qubit parameter contributes to the same one-qubit count. -/
@[simp] public lemma singleQubit_coordinate (op : UnitaryOperator (Qubits 1)) :
    model.coordinate (.singleQubit op) = Coordinate.singleQubit := rfl

/-- The counted one-qubit token retains its exact operator parameter. -/
public lemma singleQubit_operator (op : UnitaryOperator (Qubits 1)) :
    model.operator (.singleQubit op) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm op := rfl

end

end AlgorithmGate

end QuantumAlg
