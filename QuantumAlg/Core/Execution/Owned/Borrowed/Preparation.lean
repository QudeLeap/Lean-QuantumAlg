/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Borrowed.CoordinateAgreement
import all QuantumAlg.Core.Execution.Owned.Borrowed.Positions
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow

/-!
# Preparation coordinates for an owned prefix and borrowed suffix

The actual preparation constructor adds its new physical word before the
entire existing borrowed register. Its tensor coordinates agree with the
complete big-endian frame. The coordinate statement does not require a
state or independence promise and does not charge the borrowed word again.
-/

namespace QuantumAlg.Execution.OwnedBorrowedQubits

noncomputable section

private lemma borrowedInput_wires (owned borrowed : Nat) :
    (borrowedLayout owned borrowed).toQuantumLayout.wires =
      (borrowedContext owned borrowed).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change _ = (borrowedLayout owned borrowed).toQuantumLayout.wires ++ []
  exact (List.append_nil _).symm

/-- Encode the original borrowed input by its ordered physical wire values. -/
def borrowedInputBasisEquiv (owned borrowed : Nat) :
    (borrowedContext owned borrowed).register.Index ≃ (Qubits borrowed).Index :=
  (Execution.basisOfEqualWires (borrowedLayout owned borrowed).toQuantumLayout
    (borrowedContext owned borrowed).quantumLayout
    (borrowedInput_wires owned borrowed)).symm.trans
      (borrowedLayout owned borrowed).binaryIndexEquiv

private def borrowedInputPosition (owned borrowed : Nat) (index : Fin borrowed) :
    Fin (borrowedContext owned borrowed).systemCount :=
  Execution.positionsOfEqualWires (borrowedLayout owned borrowed).toQuantumLayout
    (borrowedContext owned borrowed).quantumLayout (borrowedInput_wires owned borrowed) index

private lemma borrowedInput_bit (owned borrowed : Nat)
    (basis : (borrowedContext owned borrowed).register.Index) (index : Fin borrowed) :
    (borrowedInputBasisEquiv owned borrowed basis).val.testBit index.rev.val =
      decide ((basis (borrowedInputPosition owned borrowed index)).val = 1) := by
  let original := (Execution.basisOfEqualWires (borrowedLayout owned borrowed).toQuantumLayout
    (borrowedContext owned borrowed).quantumLayout
    (borrowedInput_wires owned borrowed)).symm basis
  have values := Execution.basisOfEqualWires_value (borrowedLayout owned borrowed).toQuantumLayout
    (borrowedContext owned borrowed).quantumLayout (borrowedInput_wires owned borrowed)
    original index
  rw [Equiv.apply_symm_apply] at values
  exact ((borrowedLayout owned borrowed).binaryIndexEquiv_bit original index).trans
    ((finiteBit_value (original index)).trans
      (congrArg (fun value => decide (value = 1)) values.symm))

private lemma ownedKey_fresh (owned borrowed : Nat) :
    (⟨0⟩ : StorageKey) ∉ (borrowedContext owned borrowed).keys := by
  change (⟨0⟩ : StorageKey) ∉ [⟨1⟩]
  decide

/-- The tensor map used by the actual owned-prefix preparation instruction. -/
def preparationBasisEquiv (owned borrowed : Nat) :
    ((wordLayout owned).toQuantumLayout.register.Index ×
      (borrowedContext owned borrowed).register.Index) ≃
        (context owned borrowed).register.Index :=
  Execution.preparedLocalBasisEquiv (borrowedContext owned borrowed) ⟨0⟩
    (wordLayout owned).toQuantumLayout (ownedKey_fresh owned borrowed)
    (disjointWords owned borrowed)

private lemma preparationBasisEquiv_owned_value (owned borrowed : Nat)
    (newBasis : (wordLayout owned).toQuantumLayout.register.Index)
    (oldBasis : (borrowedContext owned borrowed).register.Index) (index : Fin owned) :
    (preparationBasisEquiv owned borrowed (newBasis, oldBasis)
      (positionEquiv owned borrowed (Fin.castAdd borrowed index))).val = (newBasis index).val := by
  have positions : positionEquiv owned borrowed (Fin.castAdd borrowed index) =
      (borrowedContext owned borrowed).addOwnedLayoutPositionEquiv ⟨0⟩
        (wordLayout owned).toQuantumLayout (ownedKey_fresh owned borrowed)
        (disjointWords owned borrowed)
        (Fin.castAdd (borrowedContext owned borrowed).systemCount index) := by
    apply Fin.ext
    rfl
  rw [positions]
  exact ((borrowedContext owned borrowed).addOwnedLayout_basis_value_preserved ⟨0⟩
    (wordLayout owned).toQuantumLayout (ownedKey_fresh owned borrowed)
    (disjointWords owned borrowed) _
    (Fin.castAdd (borrowedContext owned borrowed).systemCount index)).trans
      (QuantumLayout.appendJoinBasis_left_value _ _ _ newBasis oldBasis index)

private lemma preparationBasisEquiv_borrowed_value (owned borrowed : Nat)
    (newBasis : (wordLayout owned).toQuantumLayout.register.Index)
    (oldBasis : (borrowedContext owned borrowed).register.Index) (index : Fin borrowed) :
    (preparationBasisEquiv owned borrowed (newBasis, oldBasis)
      (positionEquiv owned borrowed (Fin.natAdd owned index))).val =
      (oldBasis (borrowedInputPosition owned borrowed index)).val := by
  have positions : positionEquiv owned borrowed (Fin.natAdd owned index) =
      (borrowedContext owned borrowed).addOwnedLayoutPositionEquiv ⟨0⟩
        (wordLayout owned).toQuantumLayout (ownedKey_fresh owned borrowed)
        (disjointWords owned borrowed)
        (Fin.natAdd owned (borrowedInputPosition owned borrowed index)) := by
    apply Fin.ext
    rfl
  rw [positions]
  exact ((borrowedContext owned borrowed).addOwnedLayout_basis_value_preserved ⟨0⟩
    (wordLayout owned).toQuantumLayout (ownedKey_fresh owned borrowed)
    (disjointWords owned borrowed) _
    (Fin.natAdd owned (borrowedInputPosition owned borrowed index))).trans
      (QuantumLayout.appendJoinBasis_right_value _ _ _ newBasis oldBasis
        (borrowedInputPosition owned borrowed index))

/-- The actual preparation tensor map agrees with the complete binary frame encoding. -/
lemma basisEquiv_preparation (owned borrowed : Nat)
    (newBasis : (wordLayout owned).toQuantumLayout.register.Index)
    (oldBasis : (borrowedContext owned borrowed).register.Index) :
    basisEquiv owned borrowed (preparationBasisEquiv owned borrowed (newBasis, oldBasis)) =
      prodEquiv ((wordLayout owned).binaryIndexEquiv newBasis,
        borrowedInputBasisEquiv owned borrowed oldBasis) := by
  apply (BinaryBasis.bigEndianEquiv (owned + borrowed)).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  refine Fin.addCases (fun phase => ?_) (fun source => ?_) index
  · have reversed : (Fin.castAdd borrowed phase).rev.val = borrowed + phase.rev.val := by
      simp only [Fin.rev, Fin.val_castAdd]
      omega
    rw [basisEquiv_bit, preparationBasisEquiv_owned_value, reversed,
      prodEquiv_testBit_left, (wordLayout owned).binaryIndexEquiv_bit]
    let value : Fin 2 := newBasis phase
    exact (finiteBit_value value).symm
  · have reversed : (Fin.natAdd owned source).rev.val = source.rev.val := by
      simp only [Fin.rev, Fin.val_natAdd]
      omega
    rw [basisEquiv_bit, preparationBasisEquiv_borrowed_value, reversed,
      prodEquiv_testBit_right, borrowedInput_bit]

end

end QuantumAlg.Execution.OwnedBorrowedQubits
