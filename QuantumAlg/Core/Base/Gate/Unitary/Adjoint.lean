/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Control.Operator
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Adjoint operators under physical basis transport

These identities describe mathematical targets for actual inverse words.
They do not grant an inverse gate or an inverse oracle query.
-/

namespace QuantumAlg.UnitaryOperator

noncomputable section

/-- Taking the adjoint commutes with a bijective relabelling of basis states. -/
public lemma unitaryOperator_reindex_star {R S : Register}
    (equivalence : R.Index ≃ S.Index) (operator : UnitaryOperator R) :
    reindex equivalence (star operator) = star (reindex equivalence operator) := by
  apply Subtype.ext
  rfl

/-- The adjoint of a tensor product acts by the adjoint on each factor. -/
public lemma unitaryOperator_prodTensor_star {R S : Register}
    (left : UnitaryOperator R) (right : UnitaryOperator S) :
    prodTensor (star left) (star right) = star (prodTensor left right) := by
  apply Subtype.ext
  ext row column
  change star (left column.1 row.1) * star (right column.2 row.2) =
    star (prodTensor left right column row)
  rw [unitaryOperator_prodTensor_apply]
  exact (map_mul (starRingEnd Complex) _ _).symm

end

end QuantumAlg.UnitaryOperator
