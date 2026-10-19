/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Lowering.Macros
import all QuantumAlg.Primitives.QFT.Source.Macros
import all QuantumAlg.Primitives.QFT.Source.Resources

/-! # Descriptive macro observations of the actual compiled Fourier circuit -/

namespace QuantumAlg.QuantumFourierTransform.Native
noncomputable section

/-- Each source occurrence contributes its one descriptive expansion annotation. -/
public lemma qftNative_circuit_macro_count (oracles : OracleModel) (name : String) (n : Nat) :
    (circuit oracles n).macroCount name =
      n * (if "hadamard" = name then 1 else 0) +
        n.choose 2 * (if "controlled-phase" = name then 1 else 0) +
          (n / 2) * (if "swap" = name then 1 else 0) := by
  rw [circuit, Lowering.lower_macroCount, Source.qftSource_circuit_macroCount,
    Source.qftSource_circuit_eventCost]
  simp only [Nat.zero_add, map_add, Lowering.macroBudget_singleton, Lowering.macroWeight]

end
end QuantumAlg.QuantumFourierTransform.Native
