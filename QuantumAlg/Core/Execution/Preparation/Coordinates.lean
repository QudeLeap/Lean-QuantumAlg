/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Preparation.Borrowed.Positions

/-!
# Actual per-wire values of the preparation basis assembly

The existing preparation correspondence joins the new physical wires with
the complete old context. Both coordinate laws below hold for arbitrary
finite labels on those wires, independently of the fixed preparation seed.
They connect subsequent single-wire instructions to the same interpreter
basis assembly without using a dimension-only correspondence.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {count : Nat} (ctx : RuntimeCtx .quantum) (key : StorageKey)
  (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)

/-- Every original physical position keeps its finite value through the actual basis assembly. -/
lemma preparedLocalBasisEquiv_old_value (newBasis : layout.register.Index)
    (oldBasis : ctx.register.Index) (index : Fin ctx.systemCount) :
    (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis)
      (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint (.inr index))).val =
        (oldBasis index).val := by
  let joined := QuantumLayout.appendJoinBasis layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint) newBasis oldBasis
  have transported := ctx.addOwnedLayout_basis_value_preserved key layout fresh disjoint
    joined (Fin.natAdd count index)
  exact transported.trans (QuantumLayout.appendJoinBasis_right_value layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint) newBasis oldBasis index)

/-- Every newly adjoined physical position receives its own finite input label. -/
lemma preparedLocalBasisEquiv_new_value (newBasis : layout.register.Index)
    (oldBasis : ctx.register.Index) (index : Fin count) :
    (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis)
      (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint (.inl index))).val =
        (newBasis index).val := by
  let joined := QuantumLayout.appendJoinBasis layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint) newBasis oldBasis
  have transported := ctx.addOwnedLayout_basis_value_preserved key layout fresh disjoint
    joined (Fin.castAdd ctx.systemCount index)
  exact transported.trans (QuantumLayout.appendJoinBasis_left_value layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint) newBasis oldBasis index)

end

end QuantumAlg.Execution
