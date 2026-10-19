/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Model
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Primitives.QFT.Native.Inverse

/-!
# Actual native stages around the declared Shor query

Every base uses one fixed oracle model, the same parallel phase Hadamards,
one ordinary query, and the generated native inverse Fourier transform.
The query instance supplies only the stored base and its physical placement.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource

noncomputable section

variable (width phaseBits : Nat)

/-- The phase prefix is prepared by the actual parallel Hadamard word. -/
def initialLayer :
    UnitaryCircuit AlgorithmGate.model (model width phaseBits)
      (QuantumSignature.qubits (phaseBits + width)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix width
    (Gate.HadamardLayer.circuit (model width phaseBits) phaseBits)

/-- Execute one model-owned modular-exponentiation query at the canonical placement. -/
def oracleLayer (gates : GateModel) (base : Fin (2 ^ width)) :
    UnitaryCircuit gates (model width phaseBits)
      (QuantumSignature.qubits (phaseBits + width)).canonicalPlacement.layout :=
  .query (OracleModel.Application.onPlacement (model width phaseBits) base
    (QuantumSignature.qubits (phaseBits + width)).canonicalPlacement)

/-- Native inverse Fourier gates act on the phase prefix and preserve the target. -/
def readoutLayer :
    UnitaryCircuit AlgorithmGate.model (model width phaseBits)
      (QuantumSignature.qubits (phaseBits + width)).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryPrefix width
    (QuantumFourierTransform.Native.inverseCircuit (model width phaseBits) phaseBits)

/-- The complete selected member retains its native peripherals and ordinary query. -/
def circuit (base : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model (model width phaseBits)
      (QuantumSignature.qubits (phaseBits + width)).canonicalPlacement.layout :=
  ((initialLayer width phaseBits).seq
    (oracleLayer width phaseBits AlgorithmGate.model base)).seq
      (readoutLayer width phaseBits)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource
