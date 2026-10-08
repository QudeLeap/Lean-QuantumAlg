/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Components.Oracle.UnitarySource.Circuit
public import QuantumAlg.Components.Gates.Hadamard.Layer
public import QuantumAlg.Primitives.QFT.Native.Inverse.Resources
public import QuantumAlg.Primitives.QFT.Native.Inverse.Depth
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Components.Oracle.UnitarySource.Circuit
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources
import all QuantumAlg.Primitives.QFT.Native.Inverse.Depth
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Native source order-finding unitary

The source sampler has parallel phase Hadamards, one declared modular-
exponentiation query, and the generated inverse native QFT. The query grants
only ordinary access to the specified XOR permutation. Its implementation is
separate from this abstract source call [dW19, qcnotes.tex:2203-2225].
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

/-- The supplied modular-exponentiation operator grants one ordinary query. -/
public abbrev sourceModel {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    OracleModel := UnitarySource.model (modExpOracle access)

/-- Execute the phase Hadamards on the original prefix of the full register. -/
public def initialLayer {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    UnitaryCircuit AlgorithmGate.model (sourceModel access)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix width (Gate.HadamardLayer.circuit (sourceModel access) t)

/-- The source's single granted query occupies all original register wires. -/
public def oracleLayer {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    UnitaryCircuit AlgorithmGate.model (sourceModel access)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  UnitarySource.Circuit.program AlgorithmGate.model (modExpOracle access)
    false false false .ordinary (QuantumSignature.qubits (t + width)).canonicalPlacement

/-- The generic native adjoint reads the phase prefix without touching the target. -/
public def readoutLayer {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    UnitaryCircuit AlgorithmGate.model (sourceModel access)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix width
    (QuantumFourierTransform.Native.inverseCircuit (sourceModel access) t)

/-- The complete source unitary retains its actual native expansion and query. -/
public def circuit {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    UnitaryCircuit AlgorithmGate.model (sourceModel access)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  ((initialLayer access).seq (oracleLayer access)).seq (readoutLayer access)

/-- Each source call has one query and its own full-register operator. -/
public theorem oracleLayer_eventCost {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (oracleLayer access).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model (sourceModel access))
        (.oracle UnitarySource.Coordinate.ordinary) := by
  rw [oracleLayer, UnitarySource.Circuit.program_eventCost]
  simp only [UnitarySource.model]

/-- Parallel phase preparation has depth one exactly for a nonempty phase register. -/
public theorem initialLayer_unit_depth {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (initialLayer access).evaluatedEventDepth (fun _ => 1) =
      if t = 0 then 0 else 1 := by
  rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth (sourceModel access) t

/-- The one granted source query occupies one abstract dependency step. -/
public theorem oracleLayer_unit_depth {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (oracleLayer access).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [oracleLayer]
  exact UnitarySource.Circuit.program_unitDepth AlgorithmGate.model
    (modExpOracle access) false false false .ordinary _

/-- The generated adjoint retains every inverse Fourier native layer. -/
public theorem readoutLayer_unit_depth {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (readoutLayer access).evaluatedEventDepth (fun _ => 1) =
      t + 5 * t.choose 2 + 3 * (t / 2) := by
  rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth
    (sourceModel access) t

/-- Count actual default-model gates and the single granted query on one word. -/
public theorem circuit_event_count {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (event : Resource.Event (.quantum AlgorithmGate.model (sourceModel access))) :
    ResourcePool.count event (circuit access).eventCost =
      (2 * t + 3 * t.choose 2) *
        (if .gate .singleQubit = event then 1 else 0) +
      (2 * t.choose 2 + 3 * (t / 2)) *
        (if .gate .cnot = event then 1 else 0) +
      (if .oracle UnitarySource.Coordinate.ordinary = event then 1 else 0) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    initialLayer, readoutLayer,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    Gate.HadamardLayer.hadamardLayer_circuit_eventCost (sourceModel access) t,
    oracleLayer_eventCost,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count
      (sourceModel access) event t]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton]
  ring

/-- The query and each expanded native layer remain on the same dependency path. -/
public theorem circuit_unit_depth {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (circuit access).evaluatedEventDepth (fun _ => 1) =
      (if t = 0 then 0 else 1) + 1 +
        (t + 5 * t.choose 2 + 3 * (t / 2)) := by
  change (initialLayer access).evaluatedEventDepth (fun _ => 1) +
    (oracleLayer access).evaluatedEventDepth (fun _ => 1) +
      (readoutLayer access).evaluatedEventDepth (fun _ => 1) = _
  rw [initialLayer_unit_depth, oracleLayer_unit_depth, readoutLayer_unit_depth]

end

end QuantumAlg.OrderFinding.Native
