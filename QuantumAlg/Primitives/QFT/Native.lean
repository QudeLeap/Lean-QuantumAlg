/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Primitives.QFT.Source

/-!
# The standard-model lowering of the canonical Fourier circuit

The algorithm consumer interface is preserved. Its circuit is obtained by
verified instruction refinement of the native H/controlled-phase/SWAP source;
there is no second recursive implementation with an independent event ledger.
-/

namespace QuantumAlg.QuantumFourierTransform.Native
noncomputable section

/-- Execute the exact standard-model expansion of the canonical source QFT. -/
public def circuit (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout n) :=
  Lowering.lower oracles (Source.circuit .empty n)

/-- The production consumer circuit is the actual generic source refinement. -/
public lemma qftNative_circuit_eq_refine (oracles : OracleModel) (n : Nat) :
    circuit oracles n = (Source.circuit .empty n).refine (Lowering.instructions oracles) := by
  rfl

end
end QuantumAlg.QuantumFourierTransform.Native
