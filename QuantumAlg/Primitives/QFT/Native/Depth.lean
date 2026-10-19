/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Lowering.Depth
import all QuantumAlg.Primitives.QFT.Source.Depth

/-! # Exact standard-model dependency depth of the lowered QFT -/

namespace QuantumAlg.QuantumFourierTransform.Native
noncomputable section

/-- The actual lowered reversal has no exchange at width zero or one, otherwise three layers. -/
public lemma qftNative_bitReverse_unit_depth (oracles : OracleModel) (n : Nat) :
    (Lowering.lower oracles (Source.bitReverse .empty n)).evaluatedEventDepth (fun _ => 1) =
      if n / 2 = 0 then 0 else 3 := by
  rw [Lowering.lower_unit_depth]
  simpa only [Source.bitReverse, Lowering.standardDuration] using
    Source.reversePrefix_evaluatedEventDepth .empty Lowering.standardDuration n (n / 2) le_rfl

/-- Every nonempty symmetric-pair bank uses exactly the three real CNOT layers. -/
public lemma qftNative_bitReverse_unit_depth_nonempty (oracles : OracleModel) (n : Nat)
    (nonempty : 2 ≤ n) :
    (Lowering.lower oracles (Source.bitReverse .empty n)).evaluatedEventDepth (fun _ => 1) =
      3 := by
  rw [qftNative_bitReverse_unit_depth, if_neg (by omega)]

/-- The phase stages retain their depths; all nonempty reversal swaps share three layers. -/
public lemma qftNative_circuit_unit_depth (oracles : OracleModel) (n : Nat) :
    (circuit oracles n).evaluatedEventDepth (fun _ => 1) =
      n + 5 * n.choose 2 + (if n / 2 = 0 then 0 else 3) := by
  rw [circuit, Lowering.lower_unit_depth, Source.qftSource_circuit_depth]
  simp only [Lowering.standardDuration, Nat.mul_one]
  omega

end
end QuantumAlg.QuantumFourierTransform.Native
