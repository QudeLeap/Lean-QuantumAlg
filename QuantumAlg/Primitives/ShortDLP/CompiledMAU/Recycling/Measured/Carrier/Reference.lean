/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Tensor.Reference

/-!
# Complete logical operators beside an unchanged external reference

The operator is indexed by the complete product register. Every reference
matrix entry is retained, including off-diagonal input coherences.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open scoped Kronecker

/-- A logical operator acts on its local index and as identity on the external reference. -/
def sourceWithReference {Local : Register} (operator : HilbertOperator Local)
    (Reference : Register) : HilbertOperator (Local.prod Reference) :=
  fun row column => operator row.1 column.1 * (1 : HilbertOperator Reference) row.2 column.2

/-- The explicitly indexed complete operator is the ordinary tensor with the reference identity. -/
lemma sourceWithReference_kronecker {Local : Register} (operator : HilbertOperator Local)
    (Reference : Register) :
    sourceWithReference operator Reference = operator ⊗ₖ (1 : HilbertOperator Reference) := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
