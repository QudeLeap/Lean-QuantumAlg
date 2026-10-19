/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Borrowed.Coordinates
import all QuantumAlg.Core.Execution.Owned.Borrowed.Positions
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow

/-!
# Agreement of complete and separated physical word coordinates

Encoding the complete ordered frame agrees with encoding its actual owned
prefix and borrowed suffix separately. The proof compares the finite value
on each physical wire; no cardinality-selected equivalence is introduced.
-/

namespace QuantumAlg.Execution.OwnedBorrowedQubits

noncomputable section

private lemma finiteBit_value (value : Fin 2) :
    finTwoEquiv value = decide (value.val = 1) := by
  fin_cases value <;> rfl

/-- The complete encoding reads the original finite value at the corresponding physical wire. -/
lemma basisEquiv_bit (owned borrowed : Nat) (basis : (context owned borrowed).register.Index)
    (index : Fin (owned + borrowed)) :
    (basisEquiv owned borrowed basis).val.testBit index.rev.val =
      decide ((basis (positionEquiv owned borrowed index)).val = 1) := by
  let original := (Execution.basisOfEqualWires
    (wordLayout (owned + borrowed)).toQuantumLayout
    (context owned borrowed).quantumLayout (context_wires owned borrowed)).symm basis
  have values := Execution.basisOfEqualWires_value
    (wordLayout (owned + borrowed)).toQuantumLayout
    (context owned borrowed).quantumLayout (context_wires owned borrowed) original index
  rw [Equiv.apply_symm_apply] at values
  exact ((wordLayout (owned + borrowed)).binaryIndexEquiv_bit original index).trans
    ((finiteBit_value (original index)).trans
      (congrArg (fun value => decide (value = 1)) values.symm))

/-- The separate owned encoding reads precisely the complementary physical prefix. -/
lemma ownedBinaryEquiv_bit (owned borrowed : Nat)
    (basis : (context owned borrowed).quantumLayout.ComplementBasis
      (context owned borrowed).borrowedSelection) (index : Fin owned) :
    (ownedBinaryEquiv owned borrowed basis).val.testBit index.rev.val =
      decide ((basis ((ownedPositionEquiv owned borrowed).symm index)).val = 1) := by
  let position := (ownedPositionEquiv owned borrowed).symm index
  let dimensions := fun item =>
    finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
      (owned_position_dimension owned borrowed item))
  let encoded : Fin owned → Fin 2 :=
    Equiv.piCongr (ownedPositionEquiv owned borrowed) dimensions basis
  have values : (encoded index).val = (basis position).val := by
    have actual := Equiv.piCongr_apply_apply
      (W := fun item => Fin ((context owned borrowed).quantumLayout.wire item.val).dimension)
      (Z := fun _ : Fin owned => Fin 2)
      (ownedPositionEquiv owned borrowed) dimensions basis position
    rw [Equiv.apply_symm_apply] at actual
    exact congrArg Fin.val actual
  exact (BinaryBasis.bigEndianEquiv_bit owned encoded index).trans
    ((finiteBit_value (encoded index)).trans
      (congrArg (fun value => decide (value = 1)) values))

private def borrowedWire (owned borrowed : Nat) (index : Fin borrowed) :
    QuantumLayout.SelectedPosition (context owned borrowed).borrowedSelection :=
  ⟨positionEquiv owned borrowed (Fin.natAdd owned index),
    (borrowed_position_iff owned borrowed _).mpr (by simp only [Fin.val_natAdd]; omega)⟩

private lemma borrowedWire_position (owned borrowed : Nat) (index : Fin borrowed) :
    (context owned borrowed).borrowedPositionEquiv (borrowedWire owned borrowed index) =
      Execution.positionsOfEqualWires (borrowedLayout owned borrowed).toQuantumLayout
        (context owned borrowed).borrowedQuantumLayout
        (borrowed_ordered_wires owned borrowed) index := by
  apply (context owned borrowed).borrowedQuantumLayout.identityInjective
  change ((context owned borrowed).borrowedQuantumLayout.wire
    ((context owned borrowed).borrowedPositionEquiv (borrowedWire owned borrowed index))).identity =
      ((context owned borrowed).borrowedQuantumLayout.wire
        (Execution.positionsOfEqualWires (borrowedLayout owned borrowed).toQuantumLayout
          (context owned borrowed).borrowedQuantumLayout
          (borrowed_ordered_wires owned borrowed) index)).identity
  rw [(context owned borrowed).borrowedPositionEquiv_wire,
    Execution.wireAtCorrespondingPosition]
  change ((context owned borrowed).quantumLayout.wire
    (positionEquiv owned borrowed (Fin.natAdd owned index))).identity = _
  rw [position_wire]
  rfl

/-- The separate borrowed encoding follows the original source-wire order and finite values. -/
lemma borrowedBinaryEquiv_bit (owned borrowed : Nat)
    (basis : (context owned borrowed).quantumLayout.SelectedBasis
      (context owned borrowed).borrowedSelection) (index : Fin borrowed) :
    (borrowedBinaryEquiv owned borrowed basis).val.testBit index.rev.val =
      decide ((basis (borrowedWire owned borrowed index)).val = 1) := by
  let original := (Execution.basisOfEqualWires
    (borrowedLayout owned borrowed).toQuantumLayout
    (context owned borrowed).borrowedQuantumLayout
    (borrowed_ordered_wires owned borrowed)).symm
      ((context owned borrowed).borrowedBasisEquiv basis)
  have originalValues := Execution.basisOfEqualWires_value
    (borrowedLayout owned borrowed).toQuantumLayout
    (context owned borrowed).borrowedQuantumLayout
    (borrowed_ordered_wires owned borrowed) original index
  rw [Equiv.apply_symm_apply] at originalValues
  have selectedValues := (context owned borrowed).borrowedBasisEquiv_value basis
    (borrowedWire owned borrowed index)
  rw [borrowedWire_position] at selectedValues
  exact ((borrowedLayout owned borrowed).binaryIndexEquiv_bit original index).trans
    ((finiteBit_value (original index)).trans
      (congrArg (fun value => decide (value = 1))
        (originalValues.symm.trans selectedValues)))

/-- Full-frame binary encoding equals the tensor encoding of its actual owned and borrowed words. -/
lemma basisEquiv_eq_wordBinaryEquiv (owned borrowed : Nat) :
    basisEquiv owned borrowed = wordBinaryEquiv owned borrowed := by
  apply Equiv.ext
  intro basis
  apply (BinaryBasis.bigEndianEquiv (owned + borrowed)).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  refine Fin.addCases (fun phase => ?_) (fun source => ?_) index
  · have reversed : (Fin.castAdd borrowed phase).rev.val = borrowed + phase.rev.val := by
      simp only [Fin.rev, Fin.val_castAdd]
      omega
    rw [basisEquiv_bit]
    change _ = (prodEquiv
      (ownedBinaryEquiv owned borrowed
        ((context owned borrowed).quantumLayout.restrictComplementBasis
          (context owned borrowed).borrowedSelection basis),
       borrowedBinaryEquiv owned borrowed
        ((context owned borrowed).quantumLayout.restrictSelectedBasis
          (context owned borrowed).borrowedSelection basis))).val.testBit
            (Fin.castAdd borrowed phase).rev.val
    rw [reversed, prodEquiv_testBit_left, ownedBinaryEquiv_bit]
    rfl
  · have reversed : (Fin.natAdd owned source).rev.val = source.rev.val := by
      simp only [Fin.rev, Fin.val_natAdd]
      omega
    rw [basisEquiv_bit]
    change _ = (prodEquiv
      (ownedBinaryEquiv owned borrowed
        ((context owned borrowed).quantumLayout.restrictComplementBasis
          (context owned borrowed).borrowedSelection basis),
       borrowedBinaryEquiv owned borrowed
        ((context owned borrowed).quantumLayout.restrictSelectedBasis
          (context owned borrowed).borrowedSelection basis))).val.testBit
            (Fin.natAdd owned source).rev.val
    rw [reversed, prodEquiv_testBit_right, borrowedBinaryEquiv_bit]
    rfl

/-- Reassembling the actual selections has the standard owned-first tensor label. -/
lemma basisEquiv_join (owned borrowed : Nat)
    (selected : (context owned borrowed).quantumLayout.SelectedBasis
      (context owned borrowed).borrowedSelection)
    (complement : (context owned borrowed).quantumLayout.ComplementBasis
      (context owned borrowed).borrowedSelection) :
    basisEquiv owned borrowed
      ((context owned borrowed).quantumLayout.joinSelectedBasis
        (context owned borrowed).borrowedSelection selected complement) =
      prodEquiv (ownedBinaryEquiv owned borrowed complement,
        borrowedBinaryEquiv owned borrowed selected) := by
  rw [basisEquiv_eq_wordBinaryEquiv]
  exact congrArg (prodEquiv (m := owned) (n := borrowed))
    (wordPairEquiv_join owned borrowed selected complement)

end

end QuantumAlg.Execution.OwnedBorrowedQubits
