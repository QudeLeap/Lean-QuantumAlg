/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint

/-!
# Exact adjoint matrix of the generated inverse QFT

This is the generic circuit adjoint theorem applied to the forward word.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

/-- The generated inverse has the exact adjoint of the actual forward circuit's matrix. -/
public theorem qftNative_inverseCircuit_matrix (oracles : OracleModel) (n : Nat) :
    (inverseCircuit oracles n).matrix = star (circuit .empty n).matrix :=
  UnitaryCircuit.dagger_matrix (circuit .empty n) (AlgorithmGate.oracleFreeAdjoints oracles)

end

end QuantumAlg.QuantumFourierTransform.Native
