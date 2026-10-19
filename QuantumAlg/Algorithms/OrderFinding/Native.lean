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

/-- Fixed register dimensions with only ordinary modular-exponentiation access. -/
public abbrev sourceModel (t width : Nat) : OracleModel :=
  UnitarySource.model (t + width)

/-- The modular source permutation is supplied only to the interpreter. -/
@[expose] public def interpretation {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) : (sourceModel t width).Interpretation :=
  UnitarySource.interpretation (modExpOracle access)

/-- Execute the phase Hadamards on the original prefix of the full register. -/
public def initialLayer (t width : Nat) :
    UnitaryCircuit AlgorithmGate.model (sourceModel t width)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix width (Gate.HadamardLayer.circuit (sourceModel t width) t)

/-- The source's single granted query occupies all original register wires. -/
public def oracleLayer (t width : Nat) :
    UnitaryCircuit AlgorithmGate.model (sourceModel t width)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  UnitarySource.Circuit.program AlgorithmGate.model (t + width)
    false false false .ordinary (QuantumSignature.qubits (t + width)).canonicalPlacement

/-- The generic native adjoint reads the phase prefix without touching the target. -/
public def readoutLayer (t width : Nat) :
    UnitaryCircuit AlgorithmGate.model (sourceModel t width)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix width
    (QuantumFourierTransform.Native.inverseCircuit (sourceModel t width) t)

/-- The complete source unitary retains its actual native expansion and query. -/
public def circuit (t width : Nat) :
    UnitaryCircuit AlgorithmGate.model (sourceModel t width)
      (QuantumSignature.qubits (t + width)).canonicalPlacement.layout :=
  ((initialLayer t width).seq (oracleLayer t width)).seq (readoutLayer t width)

/-- Each source call has one query and its own full-register operator. -/
public lemma oracleLayer_eventCost (t width : Nat) :
    (oracleLayer t width).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model (sourceModel t width))
        (.oracle UnitarySource.Coordinate.ordinary) := by
  rw [oracleLayer, UnitarySource.Circuit.program_eventCost]
  simp only [UnitarySource.model]

/-- Parallel phase preparation has depth one exactly for a nonempty phase register. -/
public lemma initialLayer_unit_depth (t width : Nat) :
    (initialLayer t width).evaluatedEventDepth (fun _ => 1) =
      if t = 0 then 0 else 1 := by
  rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth (sourceModel t width) t

/-- The one granted source query occupies one abstract dependency step. -/
public lemma oracleLayer_unit_depth (t width : Nat) :
    (oracleLayer t width).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [oracleLayer]
  exact UnitarySource.Circuit.program_unitDepth AlgorithmGate.model
    (t + width) false false false .ordinary _

/-- The generated adjoint retains every inverse Fourier native layer. -/
public lemma readoutLayer_unit_depth (t width : Nat) :
    (readoutLayer t width).evaluatedEventDepth (fun _ => 1) =
      t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3) := by
  rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth
    (sourceModel t width) t

/-- Count actual default-model gates and the single granted query on one word. -/
public lemma circuit_event_count (t width : Nat)
    (event : Resource.Event (.quantum AlgorithmGate.model (sourceModel t width))) :
    ResourcePool.count event (circuit t width).eventCost =
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
    Gate.HadamardLayer.hadamardLayer_circuit_eventCost (sourceModel t width) t,
    oracleLayer_eventCost,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count
      (sourceModel t width) event t]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton]
  ring

/-- The query and each expanded native layer remain on the same dependency path. -/
public lemma circuit_unit_depth (t width : Nat) :
    (circuit t width).evaluatedEventDepth (fun _ => 1) =
      (if t = 0 then 0 else 1) + 1 +
        (t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3)) := by
  change (initialLayer t width).evaluatedEventDepth (fun _ => 1) +
    (oracleLayer t width).evaluatedEventDepth (fun _ => 1) +
      (readoutLayer t width).evaluatedEventDepth (fun _ => 1) = _
  rw [initialLayer_unit_depth, oracleLayer_unit_depth, readoutLayer_unit_depth]

end

end QuantumAlg.OrderFinding.Native
