/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow

/-!
# Agreement of canonical and prepared owned-word coordinates

A fresh owned prefix and the supplied owned suffix retain the same ordered
physical values under both the interpreter tensor map and the canonical
binary encoding. This is a coordinate identity without an input-state premise.
-/

namespace QuantumAlg.Execution.OwnedQubitPrefix

noncomputable section

private lemma finiteBit_value (value : Fin 2) :
    finTwoEquiv value = decide (value.val = 1) := by
  fin_cases value <;> rfl

private def positionEquiv (freshWidth width : Nat) :
    Fin (freshWidth + width) ≃ Fin (post freshWidth width).systemCount :=
  positionsOfEqualWires (QuantumSignature.qubits (freshWidth + width)).canonicalPlacement.layout
    (post freshWidth width).quantumLayout (post_canonical_wires freshWidth width)

/-- Complete binary coordinates obtained from the equality of ordered physical wire records. -/
def canonicalBasisEquiv (freshWidth width : Nat) :
    (post freshWidth width).register.Index ≃ (Qubits (freshWidth + width)).Index :=
  (basisOfEqualWires (QuantumSignature.qubits (freshWidth + width)).canonicalPlacement.layout
    (post freshWidth width).quantumLayout (post_canonical_wires freshWidth width)).symm.trans
      (QuantumSignature.qubitsIndexEquiv (freshWidth + width))

private lemma canonicalBasisEquiv_bit (freshWidth width : Nat)
    (basis : (post freshWidth width).register.Index) (index : Fin (freshWidth + width)) :
    (canonicalBasisEquiv freshWidth width basis).val.testBit index.rev.val =
      decide ((basis (positionEquiv freshWidth width index)).val = 1) := by
  let original := (basisOfEqualWires
    (QuantumSignature.qubits (freshWidth + width)).canonicalPlacement.layout
    (post freshWidth width).quantumLayout (post_canonical_wires freshWidth width)).symm basis
  have values := basisOfEqualWires_value
    (QuantumSignature.qubits (freshWidth + width)).canonicalPlacement.layout
    (post freshWidth width).quantumLayout (post_canonical_wires freshWidth width) original index
  rw [Equiv.apply_symm_apply] at values
  exact (BinaryBasis.bigEndianEquiv_bit (freshWidth + width) original index).trans
    ((finiteBit_value (original index)).trans
      (congrArg (fun value => decide (value = 1)) values.symm))

private def originalPosition (freshWidth width : Nat) (index : Fin width) :
    Fin (pre freshWidth width).systemCount :=
  Execution.positionsOfEqualWires (inputLayout freshWidth width).toQuantumLayout
    (pre freshWidth width).quantumLayout (input_wires freshWidth width) index

private lemma original_bit (freshWidth width : Nat)
    (basis : (pre freshWidth width).register.Index) (index : Fin width) :
    (inputBasisEquiv freshWidth width basis).val.testBit index.rev.val =
      decide ((basis (originalPosition freshWidth width index)).val = 1) := by
  let original := (Execution.basisOfEqualWires (inputLayout freshWidth width).toQuantumLayout
    (pre freshWidth width).quantumLayout
    (input_wires freshWidth width)).symm basis
  have values := Execution.basisOfEqualWires_value (inputLayout freshWidth width).toQuantumLayout
    (pre freshWidth width).quantumLayout (input_wires freshWidth width)
    original index
  rw [Equiv.apply_symm_apply] at values
  exact ((inputLayout freshWidth width).binaryIndexEquiv_bit original index).trans
    ((finiteBit_value (original index)).trans
      (congrArg (fun value => decide (value = 1)) values.symm))

private lemma assembly_owned_value (freshWidth width : Nat)
    (newBasis : (prefixLayout freshWidth).toQuantumLayout.register.Index)
    (oldBasis : (pre freshWidth width).register.Index) (index : Fin freshWidth) :
    (assembly freshWidth width (newBasis, oldBasis)
      (positionEquiv freshWidth width (Fin.castAdd width index))).val = (newBasis index).val := by
  have positions : positionEquiv freshWidth width (Fin.castAdd width index) =
      (pre freshWidth width).addOwnedLayoutPositionEquiv ⟨0⟩
        (prefixLayout freshWidth).toQuantumLayout (prefix_fresh freshWidth width)
        (prefix_disjoint freshWidth width)
        (Fin.castAdd (pre freshWidth width).systemCount index) := by
    apply Fin.ext
    rfl
  rw [positions]
  exact ((pre freshWidth width).addOwnedLayout_basis_value_preserved ⟨0⟩
    (prefixLayout freshWidth).toQuantumLayout (prefix_fresh freshWidth width)
    (prefix_disjoint freshWidth width) _
    (Fin.castAdd (pre freshWidth width).systemCount index)).trans
      (QuantumLayout.appendJoinBasis_left_value _ _ _ newBasis oldBasis index)

private lemma assembly_original_value (freshWidth width : Nat)
    (newBasis : (prefixLayout freshWidth).toQuantumLayout.register.Index)
    (oldBasis : (pre freshWidth width).register.Index) (index : Fin width) :
    (assembly freshWidth width (newBasis, oldBasis)
      (positionEquiv freshWidth width (Fin.natAdd freshWidth index))).val =
      (oldBasis (originalPosition freshWidth width index)).val := by
  have positions : positionEquiv freshWidth width (Fin.natAdd freshWidth index) =
      (pre freshWidth width).addOwnedLayoutPositionEquiv ⟨0⟩
        (prefixLayout freshWidth).toQuantumLayout (prefix_fresh freshWidth width)
        (prefix_disjoint freshWidth width)
        (Fin.natAdd freshWidth (originalPosition freshWidth width index)) := by
    apply Fin.ext
    rfl
  rw [positions]
  exact ((pre freshWidth width).addOwnedLayout_basis_value_preserved ⟨0⟩
    (prefixLayout freshWidth).toQuantumLayout (prefix_fresh freshWidth width)
    (prefix_disjoint freshWidth width) _
    (Fin.natAdd freshWidth (originalPosition freshWidth width index))).trans
      (QuantumLayout.appendJoinBasis_right_value _ _ _ newBasis oldBasis
        (originalPosition freshWidth width index))

/-- The actual preparation tensor map agrees with the complete binary frame encoding. -/
lemma canonicalBasisEquiv_assembly (freshWidth width : Nat)
    (newBasis : (prefixLayout freshWidth).toQuantumLayout.register.Index)
    (oldBasis : (pre freshWidth width).register.Index) :
    canonicalBasisEquiv freshWidth width (assembly freshWidth width (newBasis, oldBasis)) =
      prodEquiv ((prefixLayout freshWidth).binaryIndexEquiv newBasis,
        inputBasisEquiv freshWidth width oldBasis) := by
  apply (BinaryBasis.bigEndianEquiv (freshWidth + width)).symm.injective
  funext index
  apply finTwoEquiv.injective
  simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
  refine Fin.addCases (fun phase => ?_) (fun source => ?_) index
  · have reversed : (Fin.castAdd width phase).rev.val = width + phase.rev.val := by
      simp only [Fin.rev, Fin.val_castAdd]
      omega
    rw [canonicalBasisEquiv_bit, assembly_owned_value, reversed,
      prodEquiv_testBit_left, (prefixLayout freshWidth).binaryIndexEquiv_bit]
    let value : Fin 2 := newBasis phase
    exact (finiteBit_value value).symm
  · have reversed : (Fin.natAdd freshWidth source).rev.val = source.rev.val := by
      simp only [Fin.rev, Fin.val_natAdd]
      omega
    rw [canonicalBasisEquiv_bit, assembly_original_value, reversed,
      prodEquiv_testBit_right, original_bit]

/-- The actual preparation frame and canonical physical-wire frame encode identical values. -/
lemma canonicalBasisEquiv_eq_basisEquiv (freshWidth width : Nat) :
    canonicalBasisEquiv freshWidth width = basisEquiv freshWidth width := by
  apply Equiv.ext
  intro basis
  obtain ⟨⟨fresh, original⟩, rfl⟩ := (assembly freshWidth width).surjective basis
  rw [canonicalBasisEquiv_assembly, basisEquiv_assembly]

end

end QuantumAlg.Execution.OwnedQubitPrefix
