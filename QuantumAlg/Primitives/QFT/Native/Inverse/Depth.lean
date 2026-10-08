/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Depth
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources

/-!
# Dependency depth of the generated inverse QFT

Default-model native adjoints each take one native instruction. The generic
preservation theorem therefore transfers the forward word's complete depth.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

/-- Inversion retains all layers of the actual phase and SWAP expansions. -/
public theorem qftNative_inverseCircuit_unit_depth (oracles : OracleModel) (n : Nat) :
    (inverseCircuit oracles n).evaluatedEventDepth (fun _ => 1) =
      n + 5 * n.choose 2 + 3 * (n / 2) := by
  exact (AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth oracles
    (circuit .empty n)).trans (qftNative_circuit_unit_depth .empty n)

end

end QuantumAlg.QuantumFourierTransform.Native
