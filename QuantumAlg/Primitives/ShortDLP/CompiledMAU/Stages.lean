/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage

/-!
# Native preparation and readout for compiled short DLP

Both exponent words receive one parallel Hadamard layer. The two native
inverse Fourier words execute in parallel on those same physical registers;
the arithmetic workspace remains resident throughout both stages.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Actual Hadamard preparation, leaving the arithmetic workspace untouched. -/
def preparationCircuit (params : RegisterParameters) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (totalQubits params)).toQuantum :=
  (Gate.HadamardLayer.circuit .empty
    (firstBits params + params.ell)).onBinaryPrefix params.workspaceBits

/-- Actual inverse Fourier readout on the two original exponent words. -/
def readoutCircuit (params : RegisterParameters) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (totalQubits params)).toQuantum :=
  (DeclaredStage.readoutPair .empty params).onBinaryPrefix params.workspaceBits

end

end QuantumAlg.ShortDLP.CompiledMAU
