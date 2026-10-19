/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Layout.Signature
public import QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
public import QuantumAlg.Components.Gates.Swap
import all QuantumAlg.Components.Gates.Swap

/-!
# The natural gate model of the quantum Fourier transform

Hadamard, an exact controlled phase with its real angle, and SWAP are native
instructions in this model. Their operators are independent of any later
compilation into the default algorithm gate model.
-/

namespace QuantumAlg.FourierGate

/-- The three independently counted Fourier instructions. -/
public inductive Coordinate where
  | hadamard
  | controlledPhase
  | swap
deriving DecidableEq

/-- A controlled-phase token retains its full angle, including its sign. -/
public inductive Token where
  | hadamard
  | controlledPhase (angle : Real)
  | swap

/-- A Hadamard acts on one qubit; each phase or SWAP acts on two qubits. -/
@[expose, implicit_reducible]
public def signature : Token → QuantumSignature
  | .hadamard => .qubits 1
  | .controlledPhase _ => .qubits 2
  | .swap => .qubits 2

/-- Count source instructions without discarding their operator parameters. -/
@[expose]
public def coordinate : Token → Coordinate
  | .hadamard => .hadamard
  | .controlledPhase _ => .controlledPhase
  | .swap => .swap

noncomputable section

/-- Exact local operators, with no identification modulo global phase. -/
@[expose]
public def operator : (token : Token) → UnitaryOperator (signature token).register
  | .hadamard =>
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm Gate.HOp
  | .controlledPhase angle => Gate.ControlledPhase.operator angle
  | .swap => Gate.Swap.operator

/-- The natural native language of the canonical Fourier construction. -/
@[expose, implicit_reducible]
public def model : GateModel where
  Token := Token
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature := signature
  operator := operator
  coordinate := coordinate

end
end QuantumAlg.FourierGate
