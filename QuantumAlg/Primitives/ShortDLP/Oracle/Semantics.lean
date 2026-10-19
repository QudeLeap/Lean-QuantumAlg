/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation

/-!
# Exact short-DLP query semantics

The declared group's operator is the basis permutation from the source
registers, with no separately supplied oracle action.
-/

namespace QuantumAlg.ShortDLP

noncomputable section

/-- Matrix entries of the group query are precisely the source-register
permutation. The permutation matrix uses the row-to-column convention. -/
lemma oracleOperator_entry {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (output input :
      (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) :
    oracleOperator encoding g x
        (tripleEquiv params output) (tripleEquiv params input) =
      if oraclePerm encoding g x output = input then 1 else 0 := by
  rw [oracleOperator, UnitaryOperator.ofPerm_entry,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  simp only [Equiv.apply_eq_iff_eq]

/-- A basis state is relabelled by the exact reversible group query. -/
lemma oracleOperator_apply_ket {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (input :
      (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) :
    (oracleOperator encoding g x).apply
        (NormalizedVector.ket (tripleEquiv params input)) =
      NormalizedVector.ket
        (tripleEquiv params (oraclePerm encoding g x input)) := by
  rw [oracleOperator, UnitaryOperator.ofPerm_apply_ket]
  simp [Equiv.permCongr_def, oraclePerm_symm]

end

end QuantumAlg.ShortDLP
