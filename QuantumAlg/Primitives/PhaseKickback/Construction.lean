/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.Basic
public import QuantumAlg.Components.Oracle.UnitarySource.Controlled
import all QuantumAlg.Primitives.PhaseKickback.Basic
import all QuantumAlg.Components.Oracle.UnitarySource.Controlled

/-!
# Concrete phase-kickback queries

Each construction uses one declared source query, preserves its exact phase,
and touches only the complete supplied control/input word
[dW19, qcnotes.tex:1145-1173; CEMM98, cemm6.tex:140-166].
-/

namespace QuantumAlg

noncomputable section

namespace PhaseKickback

/-- One actual XOR query on the complete supplied input and target. -/
public def circuit {n : Nat} (f : Fin (2 ^ n) → Bool) :
    UnitaryCircuit (Qubits (n + 1)) := Gate.xorOracle f

theorem circuit_matrix {n : Nat} (f : Fin (2 ^ n) → Bool) :
    (circuit f).matrix = xorOracleOp f := rfl

theorem circuit_physicalIdx {n : Nat} (f : Fin (2 ^ n) → Bool) :
    (circuit f).physical_idx = List.range (n + 1) := rfl

theorem circuit_events {n : Nat} (f : Fin (2 ^ n) → Bool) :
    (circuit f).eventCost = ResourcePool.singleton (phaseKickbackEvent n) := rfl

theorem circuit_depth {n : Nat} (f : Fin (2 ^ n) → Bool) :
    (circuit f).evaluatedEventDepth (fun _ => 1) ≤ 1 := le_rfl

end PhaseKickback

namespace GeneralizedPhaseKickback

/-- One structurally controlled query to the supplied source unitary. -/
public def circuit {n : Nat} (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits (1 + n)) := UnitarySource.controlledProgram U

theorem circuit_matrix {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (circuit U).matrix = UnitaryOperator.controlledQubits U :=
  UnitarySource.controlledProgram_matrix U

theorem circuit_physicalIdx {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (circuit U).physical_idx = List.range (1 + n) :=
  UnitarySource.controlledProgram_physicalIdx U

theorem circuit_events {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (circuit U).eventCost = ResourcePool.singleton (UnitarySource.controlledEvent n) :=
  UnitarySource.controlledProgram_events U

theorem circuit_depth {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (circuit U).evaluatedEventDepth (fun _ => 1) ≤ 1 :=
  le_of_eq (UnitarySource.controlledProgram_depth U)

end GeneralizedPhaseKickback

end

end QuantumAlg
