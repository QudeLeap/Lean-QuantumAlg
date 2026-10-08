/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
public import QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive

/-!
# Inverse QFT through the generic native circuit adjoint

The forward construction uses no oracle. Its actual native word is reversed
by the generic transformation, using one default-model inverse per gate.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

/-- Reverse the actual oracle-free QFT word using default native inverse implementations. -/
public def inverseCircuit (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout n) :=
  (circuit .empty n).dagger (AlgorithmGate.oracleFreeAdjoints oracles)

end

end QuantumAlg.QuantumFourierTransform.Native
