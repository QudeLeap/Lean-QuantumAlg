/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.Layout
import all QuantumAlg.Core.Execution.Context.Union.Basis
import all QuantumAlg.Core.Execution.Preparation.Coordinates

/-!
# Preparation coordinates under a complete entry permutation

When the resident prepared bank has the exact new wire list, the original
context followed by that bank has the same physical values as the actual
preparation's new-bank-before-old-context order. The entry permutation retains
all keys and roles, and the wire equality retains every physical identity and
dimension. This theorem adds no runtime permutation or state preparation.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

open ContextUnion

/-- Exact new-bank wire records and complete entry permutation determine preparation coordinates. -/
lemma preparation_basis_union {ctx bank : RuntimeCtx .quantum} {count : Nat}
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (bankWires : layout.wires = bank.quantumLayout.wires)
    (separate : RuntimeCtx.StorageDisjoint ctx bank)
    (same : (ctx.disjointUnion bank separate).entries.Perm
      (ctx.addOwnedLayout key layout fresh disjoint).entries)
    (newBasis : layout.register.Index) (oldBasis : ctx.register.Index) :
    basis same ((unionBasisEquiv ctx bank separate).symm
      (oldBasis, basisOfEqualWires layout bank.quantumLayout bankWires newBasis)) =
        preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis) := by
  let target := ctx.addOwnedLayout key layout fresh disjoint
  let bankBasis := basisOfEqualWires layout bank.quantumLayout bankWires newBasis
  let original := (unionBasisEquiv ctx bank separate).symm (oldBasis, bankBasis)
  funext position
  apply Fin.ext
  obtain ⟨side, rfl⟩ :=
    (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint).surjective position
  cases side with
  | inl index =>
      let inBank := positionsOfEqualWires layout bank.quantumLayout bankWires index
      let inSource := rightPosition ctx bank separate inBank
      have positionsMatch : positions same inSource =
          PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint (.inl index) := by
        apply target.quantumLayout.position_eq_of_identity_eq
        apply congrArg QuantumWire.identity
        exact ((positions_wire same inSource).trans
          ((contextUnion_right_wire ctx bank separate inBank).trans
            (wireAtCorrespondingPosition layout bank.quantumLayout bankWires index))).trans
              (PreparationBorrowed.fullPositionEquiv_new_wire ctx key layout fresh disjoint
                index).symm
      have left := (basis_value same original inSource).trans
        ((contextUnion_join_right_value ctx bank separate oldBasis bankBasis inBank).trans
          (basisOfEqualWires_value layout bank.quantumLayout bankWires newBasis index))
      have right := preparedLocalBasisEquiv_new_value ctx key layout fresh disjoint
        newBasis oldBasis index
      exact (congrArg (fun position => (basis same original position).val)
        positionsMatch.symm).trans (left.trans right.symm)
  | inr index =>
      let inSource := leftPosition ctx bank separate index
      have positionsMatch : positions same inSource =
          PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint (.inr index) := by
        apply target.quantumLayout.position_eq_of_identity_eq
        apply congrArg QuantumWire.identity
        exact ((positions_wire same inSource).trans
          (contextUnion_left_wire ctx bank separate index)).trans
            (PreparationBorrowed.fullPositionEquiv_old_wire ctx key layout fresh disjoint
              index).symm
      have left := (basis_value same original inSource).trans
        (contextUnion_join_left_value ctx bank separate oldBasis bankBasis index)
      have right := preparedLocalBasisEquiv_old_value ctx key layout fresh disjoint
        newBasis oldBasis index
      exact (congrArg (fun position => (basis same original position).val)
        positionsMatch.symm).trans (left.trans right.symm)

end

end QuantumAlg.Execution.ContextPermutation
