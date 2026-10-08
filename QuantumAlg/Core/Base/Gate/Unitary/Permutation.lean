/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Exact permutation-operator calculus

Permutation matrices retain exact phase under composition and basis transport.
These mathematical identities introduce no executable gate, resource coordinate
or automatic inverse operation in a selected native language.
-/

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S : Register}

/-- A permutation matrix compares the image of the row with the column. -/
public theorem ofPerm_entry (permutation : Equiv.Perm R.Index) (row column : R.Index) :
    ofPerm permutation row column = if permutation row = column then 1 else 0 := by
  simp [ofPerm, Equiv.toPEquiv_apply]

/-- Operator multiplication reverses the row-permutation composition order. -/
public theorem ofPerm_mul (first second : Equiv.Perm R.Index) :
    ofPerm first * ofPerm second = ofPerm (second * first) := by
  apply Subtype.ext
  exact (Matrix.permMatrix_mul second first).symm

/-- Transporting a permutation operator conjugates its row permutation by the same equivalence. -/
public theorem reindex_ofPerm (equivalence : R.Index ≃ S.Index)
    (permutation : Equiv.Perm R.Index) :
    reindex equivalence (ofPerm permutation) =
      ofPerm ((equivalence.symm.trans permutation).trans equivalence) := by
  apply Subtype.ext
  ext row column
  change ofPerm permutation (equivalence.symm row) (equivalence.symm column) = _
  rw [ofPerm_entry, ofPerm_entry]
  simp only [Equiv.trans_apply]
  exact if_congr equivalence.eq_symm_apply rfl rfl

end

end QuantumAlg.UnitaryOperator
