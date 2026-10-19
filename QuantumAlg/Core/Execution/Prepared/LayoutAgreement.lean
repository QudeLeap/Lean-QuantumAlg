/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout

/-!
# Preparation agrees with the same complete physical layout

When the incoming context has no quantum systems, the interpreter's tensor
assembly and the correspondence between equal ordered wire lists assign
the identical finite value to every actual physical wire. The agreement
uses identities, dimensions and positions, with no cardinality-based basis
identification.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {systemCount : Nat} (ctx : RuntimeCtx .quantum) (key : StorageKey)
  (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx) (empty : ctx.systemCount = 0)
  (sameWires : layout.wires = (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wires)

private lemma prepared_corresponding_value (basis : layout.register.Index)
    (index : Fin systemCount) :
    (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty basis
      (positionsOfEqualWires layout
        (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout sameWires index)).val =
      (basis index).val := by
  let joined := QuantumLayout.appendJoinBasis layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint) basis (emptyContextBasis ctx empty)
  let assembled := ctx.addOwnedLayoutBasisEquiv key layout fresh disjoint joined
  have position : ctx.addOwnedLayoutPositionEquiv key layout fresh disjoint
      (Fin.castAdd ctx.systemCount index) =
        positionsOfEqualWires layout
          (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout sameWires index := by
    apply Fin.ext
    rfl
  have assembledValue := RuntimeCtx.addOwnedLayout_basis_value_preserved
    ctx key layout fresh disjoint joined (Fin.castAdd ctx.systemCount index)
  have sourceValue := QuantumLayout.appendJoinBasis_left_value layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint) basis (emptyContextBasis ctx empty) index
  change (assembled (positionsOfEqualWires layout
    (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout sameWires index)).val = _
  exact (congrArg (fun wire => (assembled wire).val) position.symm).trans
    (assembledValue.trans sourceValue)

/-- Actual empty-context preparation agrees with the correspondence of the same physical wires. -/
lemma preparedEmptyBasisEquiv_eq_basisOfEqualWires (basis : layout.register.Index) :
    preparedEmptyBasisEquiv ctx key layout fresh disjoint empty basis =
      basisOfEqualWires layout
        (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout sameWires basis := by
  funext wire
  obtain ⟨index, rfl⟩ := (positionsOfEqualWires layout
    (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout sameWires).surjective wire
  apply Fin.ext
  exact (prepared_corresponding_value ctx key layout fresh disjoint empty sameWires
    basis index).trans
    (basisOfEqualWires_value layout
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout sameWires basis index).symm

end

end QuantumAlg.Execution
