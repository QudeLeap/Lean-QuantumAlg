/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.Basic
public import QuantumAlg.Components.Oracle.Xor.Model
public import QuantumAlg.Components.Oracle.UnitarySource.Controlled
public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.Oracle.Xor.Model
import all QuantumAlg.Components.Oracle.UnitarySource.Controlled
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Concrete phase-kickback queries

Each construction executes exactly one explicitly granted source query on
its complete control/input word and retains its exact operator and phase
[dW19, qcnotes.tex:1145-1173; CEMM98, cemm6.tex:140-166].
-/

namespace QuantumAlg

noncomputable section

namespace PhaseKickback

/-- One actual XOR query on the complete supplied input and target word. -/
public def circuit {n : Nat} (f : Fin (2 ^ n) → Bool) :
    UnitaryCircuit AlgorithmGate.model (XorOracle.model f)
      (QuantumSignature.qubits (n + 1)).canonicalPlacement.layout :=
  XorOracle.circuit AlgorithmGate.model f

theorem circuit_matrix {n : Nat} (f : Fin (2 ^ n) → Bool) :
    (circuit f).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (n + 1)).symm
        (xorOracleOp f) := XorOracle.xorOracle_native_matrix AlgorithmGate.model f

theorem circuit_events {n : Nat} (f : Fin (2 ^ n) → Bool) :
    (circuit f).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (XorOracle.model f))
      (.oracle XorOracle.Coordinate.xor) := rfl

theorem circuit_depth {n : Nat} (f : Fin (2 ^ n) → Bool) :
    (circuit f).evaluatedEventDepth (fun _ => 1) ≤ 1 := le_rfl

end PhaseKickback

namespace GeneralizedPhaseKickback

/-- One actual granted controlled source query on the complete control/target word. -/
public def circuit {n : Nat} (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U true)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout :=
  UnitarySource.controlledProgram AlgorithmGate.model U

theorem circuit_matrix {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (circuit U).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n)).symm
        (UnitaryOperator.controlledQubits U) :=
  UnitarySource.controlledProgram_matrix AlgorithmGate.model U

theorem circuit_events {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (circuit U).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true))
      (.oracle UnitarySource.Coordinate.controlled) := rfl

theorem circuit_depth {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (circuit U).evaluatedEventDepth (fun _ => 1) ≤ 1 := le_rfl

end GeneralizedPhaseKickback

end

end QuantumAlg
