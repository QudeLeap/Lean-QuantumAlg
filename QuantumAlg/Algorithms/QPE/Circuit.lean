/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Query.Ladder
public import QuantumAlg.Algorithms.QPE.Readout
public import QuantumAlg.Components.Gates.Hadamard.Layer
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Algorithms.QPE.Query.Ladder
import all QuantumAlg.Algorithms.QPE.Readout
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# The actual three-stage native phase-estimation word

The initial Hadamards and inverse Fourier readout act only on the original
phase prefix. Between them, the declared controlled source queries execute at
their original stage wires [Lin22, phaseestimation.tex:514-523,647-670]. This
unitary word is one part of the complete preparation and measured execution.
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

/-- The parallel phase-register Hadamards preserve the complete supplied source register. -/
public def initialLayer (phaseWidth : Nat) (systemWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model systemWidth true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix systemWidth
    (Gate.HadamardLayer.circuit (UnitarySource.model systemWidth true) phaseWidth)

/-- The actual generic-adjoint Fourier readout preserves the same complete source register. -/
public def readoutLayer (phaseWidth : Nat) (systemWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model systemWidth true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix systemWidth
    (qpeReadoutCircuit (UnitarySource.model systemWidth true) phaseWidth)

/-- Execute the original Hadamard, controlled-query and inverse-Fourier stages. -/
public def circuit (phaseWidth : Nat) (systemWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model systemWidth true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout :=
  ((initialLayer phaseWidth systemWidth).seq
    (queryLadder AlgorithmGate.model phaseWidth systemWidth)).seq (readoutLayer phaseWidth
      systemWidth)

/-- The initial layer has parallel depth one exactly when the phase prefix is nonempty. -/
public lemma qpeNative_initialLayer_unit_depth (phaseWidth : Nat) (systemWidth : Nat) :
    (initialLayer phaseWidth systemWidth).evaluatedEventDepth (fun _ => 1) =
      if phaseWidth = 0 then 0 else 1 := by
  rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth
    (UnitarySource.model systemWidth true) phaseWidth

/-- Readout depth comes from the expanded generic adjoint, including physical SWAPs. -/
public lemma qpeNative_readoutLayer_unit_depth (phaseWidth : Nat) (systemWidth : Nat) :
    (readoutLayer phaseWidth systemWidth).evaluatedEventDepth (fun _ => 1) =
      phaseWidth + 5 * phaseWidth.choose 2 + (if phaseWidth / 2 = 0 then 0 else 3) := by
  rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact qpeReadout_native_unit_depth (UnitarySource.model systemWidth true) phaseWidth

/-- Actual unitary depth retains the complete sequential query ladder and native readout. -/
public lemma qpeNative_circuit_unit_depth (phaseWidth : Nat) (systemWidth : Nat) :
    (circuit phaseWidth systemWidth).evaluatedEventDepth (fun _ => 1) =
      ((if phaseWidth = 0 then 0 else 1) + (2 ^ phaseWidth - 1)) +
        (phaseWidth + 5 * phaseWidth.choose 2 +
          (if phaseWidth / 2 = 0 then 0 else 3)) := by
  change ((initialLayer phaseWidth systemWidth).evaluatedEventDepth (fun _ => 1) +
    (queryLadder AlgorithmGate.model phaseWidth systemWidth).evaluatedEventDepth (fun _ => 1)) +
      (readoutLayer phaseWidth systemWidth).evaluatedEventDepth (fun _ => 1) = _
  rw [qpeNative_initialLayer_unit_depth, qpeNative_queryLadder_unit_depth,
    qpeNative_readoutLayer_unit_depth]

end

end QuantumAlg.QuantumPhaseEstimation.Native
