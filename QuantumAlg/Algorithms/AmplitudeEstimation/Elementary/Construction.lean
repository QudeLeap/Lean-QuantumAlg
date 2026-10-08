/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Queries
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Reflection
import all QuantumAlg.Algorithms.QPE.Readout
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction

/-!
# The actual native amplitude-estimation ladder

Every binary-power occurrence contains a granted controlled recognizer, an
ordinary inverse preparation, the real controlled zero reflection and ordinary
preparation. The original phase Hadamards and inverse QFT leave the selected
work and source suffix untouched. Every source stage retains its original power.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

private def castCircuit (queries : OracleModel) {left right : Nat} (same : left = right)
    (body : UnitaryCircuit AlgorithmGate.model queries
      (QuantumSignature.qubits left).canonicalPlacement.layout) :
    UnitaryCircuit AlgorithmGate.model queries
      (QuantumSignature.qubits right).canonicalPlacement.layout := same ▸ body

/-- The original parallel Hadamards act on exactly the t phase wires. -/
def phaseHadamards (queries : OracleModel) (t n : Nat) :
    UnitaryCircuit AlgorithmGate.model queries
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  castCircuit queries (Nat.add_assoc t (helperWidth t n) n).symm
    ((Gate.HadamardLayer.circuit queries t).onBinaryPrefix (helperWidth t n + n))

/-- The actual generic-dagger Fourier word acts on the same original phase prefix. -/
def phaseReadout (queries : OracleModel) (t n : Nat) :
    UnitaryCircuit AlgorithmGate.model queries
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  castCircuit queries (Nat.add_assoc t (helperWidth t n) n).symm
    ((qpeReadoutCircuit queries t).onBinaryPrefix (helperWidth t n + n))

/-- One full actual source iterate with separately granted query forms. -/
def step {n t : Nat} (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n))
    (stage : Fin t) : UnitaryCircuit AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  (((controlledGoodReflection U good stage).seq (inversePreparation t U good)).seq
    (reflection (oracles U good) n stage)).seq (preparation t U good)

/-- A stage executes exactly the original binary-power multiplicity. -/
def powerStage {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    UnitaryCircuit AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  .iterate (2 ^ stage.val) (step U good stage)

/-- The original finite t-stage ladder has no stage when t is zero. -/
def ladder {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    UnitaryCircuit AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  UnitaryCircuit.indexedProduct "amplitude-estimation-source-ladder" t
    (UnitaryCircuit.identity AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout)
    (powerStage U good)

/-- Source preparation, phase Hadamards, actual controlled ladder and inverse Fourier readout. -/
def program {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    UnitaryCircuit AlgorithmGate.model (oracles U good)
      (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout :=
  (preparation t U good).seq ((phaseHadamards (oracles U good) t n).seq
    ((ladder t U good).seq (phaseReadout (oracles U good) t n)))

end

end QuantumAlg.AmplitudeEstimation.Elementary
