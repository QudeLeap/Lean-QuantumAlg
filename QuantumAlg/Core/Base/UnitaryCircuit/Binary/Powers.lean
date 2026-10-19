/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Binary matrices of actual repeated execution

Repeated native execution computes the corresponding matrix power. Changing
only its mathematical labels preserves that power and introduces no gate.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- The matrix of actual repetitions is the same power in binary coordinates. -/
public lemma unitaryCircuit_binaryMatrix_iterate {gates : GateModel} {oracles : OracleModel}
    {width : Nat} (repetitions : Nat)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    ((iterate repetitions body).binaryMatrix environment) = (body.binaryMatrix environment) ^
      repetitions := by
  unfold binaryMatrix
  rw [iterate_matrix]
  induction repetitions with
  | zero => rw [pow_zero, pow_zero, UnitaryOperator.unitaryOperator_reindex_one]
  | succ repetitions ih =>
      simp only [pow_succ, UnitaryOperator.unitaryOperator_reindex_mul, ih]

end

end QuantumAlg.UnitaryCircuit
