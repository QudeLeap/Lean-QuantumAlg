/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Borrowed.Positions
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow

/-!
# Separate binary coordinates for the actual owned and borrowed words

The owned coordinates are precisely the actual complementary positions. The
borrowed coordinates follow their original ordered wire records. Combining
these explicit coordinate maps gives the ordinary word-pair basis without
allocating, discarding, or relabeling any physical wire.
-/

namespace QuantumAlg.Execution.OwnedBorrowedQubits

noncomputable section

def ownedPositionEquiv (owned borrowed : Nat) :
    QuantumLayout.SelectedPosition (context owned borrowed).borrowedSelectionᶜ ≃ Fin owned where
  toFun position :=
    ⟨((positionEquiv owned borrowed).symm position.val).val, by
      apply (owned_position_iff owned borrowed _).mp
      simpa only [Equiv.apply_symm_apply] using position.property⟩
  invFun index :=
    ⟨positionEquiv owned borrowed (index.castAdd borrowed),
      (owned_position_iff owned borrowed _).mpr index.isLt⟩
  left_inv position := by
    apply Subtype.ext
    apply (positionEquiv owned borrowed).symm.injective
    apply Fin.ext
    simp only [Equiv.symm_apply_apply, Fin.val_castAdd]
  right_inv index := by
    apply Fin.ext
    simp only [Equiv.symm_apply_apply, Fin.val_castAdd]

private lemma owned_position_dimension (owned borrowed : Nat)
    (position : QuantumLayout.SelectedPosition (context owned borrowed).borrowedSelectionᶜ) :
    ((context owned borrowed).quantumLayout.wire position.val).dimension = 2 := by
  have wire := position_wire owned borrowed ((positionEquiv owned borrowed).symm position.val)
  rw [Equiv.apply_symm_apply] at wire
  exact congrArg QuantumWire.dimension wire

/-- Encode exactly the actual owned prefix of the full context in big-endian order. -/
def ownedBinaryEquiv (owned borrowed : Nat) :
    (context owned borrowed).quantumLayout.ComplementBasis
      (context owned borrowed).borrowedSelection ≃ (Qubits owned).Index :=
  (Equiv.piCongr (ownedPositionEquiv owned borrowed) fun position =>
    finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
      (owned_position_dimension owned borrowed position))).trans
        (BinaryBasis.bigEndianEquiv owned)

private lemma borrowed_ordered_wires (owned borrowed : Nat) :
    (borrowedLayout owned borrowed).toQuantumLayout.wires =
      (context owned borrowed).borrowedQuantumLayout.wires := by
  rw [RuntimeCtx.borrowedQuantumLayout_wires, context_borrowedWires]

/-- Encode the actual borrowed suffix by its supplied physical wire order. -/
def borrowedBinaryEquiv (owned borrowed : Nat) :
    (context owned borrowed).quantumLayout.SelectedBasis
      (context owned borrowed).borrowedSelection ≃ (Qubits borrowed).Index :=
  (context owned borrowed).borrowedBasisEquiv.trans
    ((Execution.basisOfEqualWires (borrowedLayout owned borrowed).toQuantumLayout
      (context owned borrowed).borrowedQuantumLayout
      (borrowed_ordered_wires owned borrowed)).symm.trans
        (borrowedLayout owned borrowed).binaryIndexEquiv)

/-- Exact word-pair coordinates assembled from the actual selected and complementary systems. -/
def wordPairEquiv (owned borrowed : Nat) :
    (context owned borrowed).register.Index ≃ (Qubits owned).Index × (Qubits borrowed).Index :=
  ((context owned borrowed).quantumLayout.selectionBasisEquiv
    (context owned borrowed).borrowedSelection).trans
      (((borrowedBinaryEquiv owned borrowed).prodCongr (ownedBinaryEquiv owned borrowed)).trans
        (Equiv.prodComm _ _))

/-- The standard tensor encoding of the same physical owned and borrowed words. -/
def wordBinaryEquiv (owned borrowed : Nat) :
    (context owned borrowed).register.Index ≃ (Qubits (owned + borrowed)).Index :=
  (wordPairEquiv owned borrowed).trans (prodEquiv (m := owned) (n := borrowed))

private lemma selected_pair_join {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) {A B : Type}
    (selectedEquiv : layout.SelectedBasis selection ≃ A)
    (complementEquiv : layout.ComplementBasis selection ≃ B)
    (selected : layout.SelectedBasis selection) (complement : layout.ComplementBasis selection) :
    ((layout.selectionBasisEquiv selection).trans
      ((selectedEquiv.prodCongr complementEquiv).trans (Equiv.prodComm A B)))
        (layout.joinSelectedBasis selection selected complement) =
      (complementEquiv complement, selectedEquiv selected) :=
  congrArg
    (fun pair : layout.SelectedBasis selection × layout.ComplementBasis selection =>
      (complementEquiv pair.2, selectedEquiv pair.1))
    (layout.selectionBasisEquiv_join selection selected complement)

/-- Reassembly gives the supplied word pair with the owned word first. -/
lemma wordPairEquiv_join (owned borrowed : Nat)
    (selected : (context owned borrowed).quantumLayout.SelectedBasis
      (context owned borrowed).borrowedSelection)
    (complement : (context owned borrowed).quantumLayout.ComplementBasis
      (context owned borrowed).borrowedSelection) :
    wordPairEquiv owned borrowed
      ((context owned borrowed).quantumLayout.joinSelectedBasis
        (context owned borrowed).borrowedSelection selected complement) =
      (ownedBinaryEquiv owned borrowed complement, borrowedBinaryEquiv owned borrowed selected) :=
  selected_pair_join (context owned borrowed).quantumLayout
    (context owned borrowed).borrowedSelection
    (borrowedBinaryEquiv owned borrowed) (ownedBinaryEquiv owned borrowed) selected complement

end

end QuantumAlg.Execution.OwnedBorrowedQubits
