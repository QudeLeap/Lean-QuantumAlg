/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
public import QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation

/-!
# Permutation semantics of an entire placed native word

The selected source action and identity on the complete complement determine
one ambient permutation. This is a theorem about the existing placement of
an operator; it does not introduce an executable gate or grant oracle access.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {small large : Nat} (source : QuantumLayout small) (target : QuantumLayout large)
variable (position : Fin small ↪ Fin large)
variable (dimensions : ∀ index,
  (source.wire index).dimension = (target.wire (position index)).dimension)

/-- Extend a source permutation by identity on all unselected physical values. -/
public def permutationAt (permutation : Equiv.Perm source.Basis) : Equiv.Perm target.Basis :=
  let frame := (relocatedPlacement source target position dimensions).splitBasis
  (frame.trans (Equiv.prodCongr permutation (Equiv.refl _))).trans frame.symm

/-- Equality of placed basis actions checks the selected output and every spectator. -/
public lemma permutationAt_eq_iff (permutation : Equiv.Perm source.Basis)
    (row column : target.Basis) :
    permutationAt source target position dimensions permutation row = column ↔
      permutation (selectedInput source target position dimensions row) =
          selectedInput source target position dimensions column ∧
        target.restrictComplementBasis (Finset.univ.map position) row =
          target.restrictComplementBasis (Finset.univ.map position) column := by
  let frame := (relocatedPlacement source target position dimensions).splitBasis
  have selected (basis : target.Basis) :
      (frame basis).1 = selectedInput source target position dimensions basis := by
    funext index
    apply Fin.ext
    rfl
  change frame.symm (permutation (frame row).1, (frame row).2) = column ↔ _
  rw [Equiv.symm_apply_eq]
  simp only [Prod.ext_iff, selected]
  rfl

/-- Placing an exact permutation operator preserves its complete phase and spectator action. -/
public lemma operatorAt_ofPerm (permutation : Equiv.Perm source.Basis) :
    operatorAt source target position dimensions (UnitaryOperator.ofPerm permutation) =
      UnitaryOperator.ofPerm (permutationAt source target position dimensions permutation) := by
  apply Subtype.ext
  ext row column
  rw [operatorAt_entry, UnitaryOperator.ofPerm_entry, UnitaryOperator.ofPerm_entry]
  have matching := permutationAt_eq_iff source target position dimensions permutation row column
  by_cases actual : permutationAt source target position dimensions permutation row = column
  · obtain ⟨localMatch, complementMatch⟩ := matching.mp actual
    rw [if_pos actual, if_pos localMatch, if_pos complementMatch, one_mul]
  · by_cases localMatch :
        permutation (selectedInput source target position dimensions row) =
          selectedInput source target position dimensions column
    · have complementMismatch :
          target.restrictComplementBasis (Finset.univ.map position) row ≠
            target.restrictComplementBasis (Finset.univ.map position) column :=
        fun same => actual (matching.mpr ⟨localMatch, same⟩)
      rw [if_neg actual, if_pos localMatch, if_neg complementMismatch, mul_zero]
    · rw [if_neg actual, if_neg localMatch, zero_mul]

end

end QuantumAlg.UnitaryCircuit
