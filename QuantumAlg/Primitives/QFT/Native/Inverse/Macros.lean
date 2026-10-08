/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Macros
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Descriptive counts on the actual generated inverse QFT

The native adjoint replacement introduces no descriptive macro. Thus the
existing source macro occurrences survive the actual generated inverse word.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

/-- Inverse QFT macros describe the generated native word and retain the original exact formula. -/
public theorem qftNative_inverseCircuit_macro_count
    (oracles : OracleModel) (name : String) (n : Nat) :
    (inverseCircuit oracles n).macroCount name =
      n * (if "hadamard" = name then 1 else 0) +
        n.choose 2 * (if "controlled-phase" = name then 1 else 0) +
          (n / 2) * (if "swap" = name then 1 else 0) := by
  unfold inverseCircuit
  rw [UnitaryCircuit.dagger_macroCount name _ (AlgorithmGate.oracleFreeAdjoints oracles)
    (fun _ => rfl)
    (fun application => False.elim
      (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence))]
  exact qftNative_circuit_macro_count .empty name n

end

end QuantumAlg.QuantumFourierTransform.Native
