/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.ControlledPhase.QubitRegister
import all QuantumAlg.Components.Gates.ControlledPhase.QubitRegister
public import QuantumAlg.Components.Gates.Swap.QubitRegister
import all QuantumAlg.Components.Gates.Swap.QubitRegister

/-!
# Native realizations of QFT subroutines

Controlled phases and swaps keep their original addressed target operators.
Their executable realizations retain the complete native expansion.
-/

namespace QuantumAlg

noncomputable section

/-- The only non-Hadamard primitive kinds used by the recursive QFT circuit. -/
public inductive QFTPrimitive (n : Nat) where
  /-- One addressed controlled phase with its semantic angle. -/
  | controlledPhase (control target : Fin n) (angle : Real)
      (hne : control ≠ target)
  /-- One addressed wire swap. -/
  | swap (left right : Fin n) (hne : left ≠ right)

namespace QFTPrimitive

/-- Certified operator denoted by one QFT primitive. -/
public def operator {n : Nat} : QFTPrimitive n → UnitaryOperator (Qubits n)
  | .controlledPhase control target angle _ =>
      qftControlledPhaseOperator control target angle
  | .swap left right hne => qftSwapOperator left right hne

/-- The same canonical ordered qubit register for both QFT subroutines. -/
@[expose, implicit_reducible]
public def layout (width : Nat) : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

/-- Each QFT subroutine executes its full native expansion on the selected positions. -/
public def circuit (oracles : OracleModel) {width : Nat} :
    QFTPrimitive width → UnitaryCircuit AlgorithmGate.model oracles (layout width)
  | .controlledPhase control target angle distinct =>
      Gate.ControlledPhase.qubitCircuit oracles control target distinct angle
  | .swap left right distinct => Gate.Swap.qubitCircuit left right distinct oracles

/-- The native implementation has exactly the original addressed mathematical target. -/
public theorem qftPrimitive_circuit_matrix (oracles : OracleModel) {width : Nat}
    (primitive : QFTPrimitive width) :
    (primitive.circuit oracles).matrix =
      UnitaryOperator.reindex
        (QuantumSignature.qubitsIndexEquiv width).symm primitive.operator := by
  cases primitive with
  | controlledPhase control target angle distinct =>
      exact Gate.ControlledPhase.controlledPhase_qubitCircuit_matrix oracles
        control target distinct angle
  | swap left right distinct =>
      exact Gate.Swap.swap_qubitCircuit_matrix left right distinct oracles

/-- Counts are read from complete native event sequences, without an atomic phase or SWAP event. -/
public theorem qftPrimitive_circuit_events (oracles : OracleModel) {width : Nat}
    (primitive : QFTPrimitive width) :
    (primitive.circuit oracles).eventTrace = match primitive with
      | .controlledPhase _ _ _ _ =>
          [.gate .singleQubit, .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot]
      | .swap _ _ _ => [.gate .cnot, .gate .cnot, .gate .cnot] := by
  cases primitive with
  | controlledPhase control target angle distinct =>
      exact Gate.ControlledPhase.controlledPhase_qubitCircuit_events oracles
        control target distinct angle
  | swap left right distinct =>
      exact Gate.Swap.swap_qubitCircuit_events left right distinct oracles

end QFTPrimitive

end

end QuantumAlg
