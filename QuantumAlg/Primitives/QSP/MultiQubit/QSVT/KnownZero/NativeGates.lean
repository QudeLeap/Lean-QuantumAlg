/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Bounds
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Bounds

/-!
# Native gate bound of the restored-work known-projector construction

The complete count includes both zero-control masks and the full conjunction
word, with the zero- and one-control cases charged to their actual native gates.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
open Gate.Toffoli
noncomputable section

private lemma sourceWork_native_gate_bound (oracles : OracleModel) (width : Nat) :
    nativeGateCount (ZeroProjector.SourceWork.budget oracles width) ≤ 10 * width + 1 := by
  have bound := KnownZero.conjunction_bound width 1 (by decide)
  unfold ZeroProjector.SourceWork.budget
  split_ifs <;>
    simp only [nativeGateCount_add, nativeGateCount_nsmul, nativeGateCount_singleton_gate,
      Nat.mul_one] <;> omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
