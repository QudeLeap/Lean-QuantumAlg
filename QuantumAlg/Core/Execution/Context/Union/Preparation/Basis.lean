/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Preparation
import all QuantumAlg.Core.Execution.Context.Union.Basis
import all QuantumAlg.Core.Execution.Preparation.Coordinates

/-!
# Exact preparation coordinates beside a resident context

The actual preparation places the new systems before the complete old union.
Splitting that result along the original context and resident frame gives the
same per-wire values as preparing the original context alone. This is a basis
identity on the actual physical wires, with no extra circuit instruction.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

variable {ctx frame : RuntimeCtx .quantum} {count : Nat}
  (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
  (separate : RuntimeCtx.StorageDisjoint (ctx.addOwnedLayout key layout fresh disjoint) frame)

/-- The actual framed preparation assembles the new basis beside the complete incoming union. -/
def preparedFramedBasisEquiv :
    (layout.register.Index ×
      (ctx.disjointUnion frame
        (preparation_original_disjoint key layout fresh disjoint separate)).register.Index) ≃
        (RuntimeCtx.register
          ((ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame separate)).Index :=
  preparedLocalBasisEquiv _ key layout (preparation_fresh_union key layout fresh disjoint separate)
    (preparation_wires_union key layout fresh disjoint separate)

/-- Preparation retains each original and framed coordinate, including arbitrary fresh labels. -/
lemma preparedFramedBasis_join (newBasis : layout.register.Index)
    (oldBasis : ctx.register.Index) (frameBasis : frame.register.Index) :
    preparedFramedBasisEquiv key layout fresh disjoint separate
      (newBasis, (unionBasisEquiv ctx frame
        (preparation_original_disjoint key layout fresh disjoint separate)).symm
          (oldBasis, frameBasis)) =
      (unionBasisEquiv (ctx.addOwnedLayout key layout fresh disjoint) frame separate).symm
        (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis),
          frameBasis) := by
  let originalSeparate := preparation_original_disjoint key layout fresh disjoint separate
  let joined := ctx.disjointUnion frame originalSeparate
  let actualFresh := preparation_fresh_union key layout fresh disjoint separate
  let actualDisjoint := preparation_wires_union key layout fresh disjoint separate
  let prepared := ctx.addOwnedLayout key layout fresh disjoint
  let complete := prepared.disjointUnion frame separate
  let actualBasis : complete.register.Index :=
    preparedFramedBasisEquiv key layout fresh disjoint separate
      (newBasis, (unionBasisEquiv ctx frame originalSeparate).symm (oldBasis, frameBasis))
  funext position
  apply Fin.ext
  obtain ⟨side, rfl⟩ := (unionPositionEquiv prepared frame separate).surjective position
  cases side with
  | inl index =>
      obtain ⟨part, rfl⟩ :=
        (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint).surjective index
      cases part with
      | inl index =>
          have positions : leftPosition prepared frame separate
              (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint (.inl index)) =
                PreparationBorrowed.fullPositionEquiv joined key layout actualFresh
                  actualDisjoint (.inl index) := by
            apply complete.quantumLayout.position_eq_of_identity_eq
            apply congrArg QuantumWire.identity
            exact ((contextUnion_left_wire prepared frame separate _).trans
              (PreparationBorrowed.fullPositionEquiv_new_wire ctx key layout fresh
                disjoint index)).trans
                (PreparationBorrowed.fullPositionEquiv_new_wire joined key layout
                  actualFresh actualDisjoint index).symm
          have left := preparedLocalBasisEquiv_new_value joined key layout actualFresh
            actualDisjoint newBasis
            ((unionBasisEquiv ctx frame originalSeparate).symm (oldBasis, frameBasis)) index
          have right := contextUnion_join_left_value prepared frame separate
            (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis))
            frameBasis (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint
              (.inl index))
          rw [preparedLocalBasisEquiv_new_value] at right
          exact (congrArg (fun position => (actualBasis position).val) positions).trans
            (left.trans right.symm)
      | inr index =>
          have positions : leftPosition prepared frame separate
              (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint (.inr index)) =
                PreparationBorrowed.fullPositionEquiv joined key layout actualFresh
                  actualDisjoint (.inr (leftPosition ctx frame originalSeparate index)) := by
            apply complete.quantumLayout.position_eq_of_identity_eq
            apply congrArg QuantumWire.identity
            exact ((contextUnion_left_wire prepared frame separate _).trans
              (PreparationBorrowed.fullPositionEquiv_old_wire ctx key layout fresh
                disjoint index)).trans
                ((PreparationBorrowed.fullPositionEquiv_old_wire joined key layout
                  actualFresh actualDisjoint _).trans
                    (contextUnion_left_wire ctx frame originalSeparate index)).symm
          have left := preparedLocalBasisEquiv_old_value joined key layout actualFresh
            actualDisjoint newBasis
            ((unionBasisEquiv ctx frame originalSeparate).symm (oldBasis, frameBasis))
            (leftPosition ctx frame originalSeparate index)
          rw [contextUnion_join_left_value] at left
          have right := contextUnion_join_left_value prepared frame separate
            (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis))
            frameBasis (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint
              (.inr index))
          rw [preparedLocalBasisEquiv_old_value] at right
          exact (congrArg (fun position => (actualBasis position).val) positions).trans
            (left.trans right.symm)
  | inr index =>
      have positions : rightPosition prepared frame separate index =
          PreparationBorrowed.fullPositionEquiv joined key layout actualFresh actualDisjoint
            (.inr (rightPosition ctx frame originalSeparate index)) := by
        apply complete.quantumLayout.position_eq_of_identity_eq
        apply congrArg QuantumWire.identity
        exact (contextUnion_right_wire prepared frame separate index).trans
          ((PreparationBorrowed.fullPositionEquiv_old_wire joined key layout actualFresh
            actualDisjoint _).trans
              (contextUnion_right_wire ctx frame originalSeparate index)).symm
      have left := preparedLocalBasisEquiv_old_value joined key layout actualFresh actualDisjoint
        newBasis ((unionBasisEquiv ctx frame originalSeparate).symm (oldBasis, frameBasis))
        (rightPosition ctx frame originalSeparate index)
      rw [contextUnion_join_right_value] at left
      have right := contextUnion_join_right_value prepared frame separate
        (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis))
        frameBasis index
      exact (congrArg (fun position => (actualBasis position).val) positions).trans
        (left.trans right.symm)

end

end QuantumAlg.Execution.ContextUnion
