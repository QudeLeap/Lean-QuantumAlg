/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Model
public import QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.PhaseOperator

/-!
# Native gates of semiclassical Fourier readout

Hadamard and an exact single-qubit phase are separately counted native
instructions. Each phase retains its real angle and exact operator. This
language makes the two independent gate bounds visible in the measured
Fourier problem, without hiding either behind a combined one-qubit budget
[GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.SemiclassicalFourierGate

/-- The two independent native gate coordinates of measured Fourier readout. -/
public inductive Coordinate where
  | hadamard
  | phase
deriving DecidableEq

/-- A feedback phase retains its complete angle, including the inverse-transform sign. -/
public inductive Token where
  | hadamard
  | phase (angle : Real)

/-- Both native instructions act on exactly one dimension-two system. -/
@[expose, implicit_reducible]
public def signature (_ : Token) : QuantumSignature := .qubits 1

/-- Count the actual declared instruction without discarding its operator parameter. -/
@[expose]
public def coordinate : Token → Coordinate
  | .hadamard => .hadamard
  | .phase _ => .phase

noncomputable section

/-- Exact local operators in the model's intrinsic physical signature coordinates. -/
@[expose]
public def operator : (token : Token) → UnitaryOperator (signature token).register
  | .hadamard =>
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm Gate.HOp
  | .phase angle =>
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm (phaseGateOp angle)

/-- The native measured-Fourier language has no two-qubit instruction. -/
@[expose, implicit_reducible]
public def model : GateModel where
  Token := Token
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature := signature
  operator := operator
  coordinate := coordinate

end

end QuantumAlg.SemiclassicalFourierGate
