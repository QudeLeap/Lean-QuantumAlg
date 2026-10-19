/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.Preparation
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Exact source coordinates after preparing the fixed shared-EEA auxiliary state

Runtime preparation places the new auxiliary wires before the original
input. This owner reassembles the canonical source order: auxiliary prefix,
original Work2 input, and auxiliary suffix. Every coordinate has an explicit
inverse and is checked against the original physical identities
[LYL+26, sec_EEA/sub_regshare.tex:16-26; sec_EEA/sub_4phase.tex:104-110].

The basis equivalence retains every possible finite value on every wire.
It is independent of the initialized values and does not choose an
identification merely from the register dimensions. The prepared-value
specialization reads the same actual auxiliary preparation, and every
original input bit retains its full unknown value.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InputAssembly

noncomputable section

open Execution InputPreparation

/-- An auxiliary coordinate has exactly its already declared canonical source physical identity. -/
def auxiliaryPosition (width : Nat) (index : Fin (auxiliaryWidth width)) :
    Fin (encoding width).width :=
  ⟨auxiliaryPhysicalIndex width index, by
    have bound := index.isLt
    have complete := complete_width width
    unfold auxiliaryPhysicalIndex
    split <;> omega⟩

/-- An input coordinate remains at its original physical position inside Work2. -/
def inputPosition (width : Nat) (index : Fin width) : Fin (encoding width).width :=
  ⟨prefixWidth width + index.val, by
    have bound := index.isLt
    have complete := complete_width width
    unfold auxiliaryWidth at complete
    omega⟩

/-- Reassemble all actual binary cells by their source physical positions. -/
def joinCells (width : Nat) (auxiliary : Fin (auxiliaryWidth width) → Fin 2)
    (input : Fin width → Fin 2) (wire : Fin (encoding width).width) : Fin 2 :=
  if beforeInput : wire.val < prefixWidth width then
    auxiliary ⟨wire.val, by unfold auxiliaryWidth; omega⟩
  else if inInput : wire.val < prefixWidth width + width then
    input ⟨wire.val - prefixWidth width, by omega⟩
  else
    auxiliary ⟨wire.val - width, by
      have bound := wire.isLt
      have complete := complete_width width
      omega⟩

/-- The exact split reads each new coordinate at its actual original source address. -/
lemma joinCells_auxiliary (width : Nat) (auxiliary : Fin (auxiliaryWidth width) → Fin 2)
    (input : Fin width → Fin 2) (index : Fin (auxiliaryWidth width)) :
    joinCells width auxiliary input (auxiliaryPosition width index) = auxiliary index := by
  by_cases beforeInput : index.val < prefixWidth width
  · simp [joinCells, auxiliaryPosition, auxiliaryPhysicalIndex, beforeInput]
  · have afterPrefix : ¬width + index.val < prefixWidth width := by omega
    have afterInput : ¬width + index.val < prefixWidth width + width := by omega
    simp [joinCells, auxiliaryPosition, auxiliaryPhysicalIndex, beforeInput,
      afterPrefix, afterInput]

/-- Every originally supplied input coordinate is preserved exactly by the reassembly. -/
lemma joinCells_input (width : Nat) (auxiliary : Fin (auxiliaryWidth width) → Fin 2)
    (input : Fin width → Fin 2) (index : Fin width) :
    joinCells width auxiliary input (inputPosition width index) = input index := by
  have beforeInput : ¬prefixWidth width + index.val < prefixWidth width := by omega
  have inInput : prefixWidth width + index.val < prefixWidth width + width := by
    have bound := index.isLt
    omega
  simp [joinCells, inputPosition, beforeInput, inInput]

private lemma joinCells_split (width : Nat) (cells : Fin (encoding width).width → Fin 2) :
    joinCells width (fun index => cells (auxiliaryPosition width index))
      (fun index => cells (inputPosition width index)) = cells := by
  funext wire
  by_cases beforeInput : wire.val < prefixWidth width
  · rw [joinCells, dif_pos beforeInput]
    apply congrArg cells
    apply Fin.ext
    change (if wire.val < prefixWidth width then wire.val else width + wire.val) = wire.val
    rw [if_pos beforeInput]
  · by_cases inInput : wire.val < prefixWidth width + width
    · rw [joinCells, dif_neg beforeInput, dif_pos inInput]
      apply congrArg cells
      apply Fin.ext
      change prefixWidth width + (wire.val - prefixWidth width) = wire.val
      omega
    · rw [joinCells, dif_neg beforeInput, dif_neg inInput]
      apply congrArg cells
      apply Fin.ext
      change (if wire.val - width < prefixWidth width then wire.val - width
        else width + (wire.val - width)) = wire.val
      rw [if_neg (by omega)]
      omega

/-- Every finite full-source assignment is equivalent to its actual auxiliary and input cells. -/
def cellsEquiv (width : Nat) :
    ((Fin (auxiliaryWidth width) → Fin 2) × (Fin width → Fin 2)) ≃
      (Fin (encoding width).width → Fin 2) where
  toFun pair := joinCells width pair.1 pair.2
  invFun cells := (fun index => cells (auxiliaryPosition width index),
    fun index => cells (inputPosition width index))
  left_inv pair := by
    apply Prod.ext
    · funext index
      exact joinCells_auxiliary width pair.1 pair.2 index
    · funext index
      exact joinCells_input width pair.1 pair.2 index
  right_inv := joinCells_split width

/-- Reuse the actual preparation's physical fresh/old basis assembly. -/
def assembly (width : Nat) :
    ((auxiliaryLayout width).register.Index × (before width).register.Index) ≃
      (after width).register.Index :=
  preparedLocalBasisEquiv (before width) auxiliaryKey (auxiliaryLayout width)
    (auxiliary_fresh width) (auxiliary_disjoint width)

private def inputCells (width : Nat) :
    (before width).register.Index ≃ (Fin width → Fin 2) :=
  (inputBasisEquiv width).trans (BinaryBasis.bigEndianEquiv width).symm

/-- The runtime register and the canonical source binary label agree through actual wire cells. -/
def basisEquiv (width : Nat) :
    (after width).register.Index ≃ (Qubits (encoding width).width).Index :=
  (assembly width).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (inputCells width)).trans
      ((cellsEquiv width).trans (BinaryBasis.bigEndianEquiv (encoding width).width)))

/-- The exact binary label retains the three original physical segments in source order. -/
lemma basisEquiv_assembly (width : Nat)
    (fresh : (auxiliaryLayout width).register.Index) (old : (before width).register.Index) :
    basisEquiv width (assembly width (fresh, old)) =
      BinaryBasis.bigEndianEquiv (encoding width).width
        (joinCells width fresh (inputCells width old)) := by
  let encodePair :
      ((auxiliaryLayout width).register.Index × (before width).register.Index) →
        (Qubits (encoding width).width).Index := fun pair =>
    BinaryBasis.bigEndianEquiv (encoding width).width
      (joinCells width pair.1 (inputCells width pair.2))
  change encodePair ((assembly width).symm (assembly width (fresh, old))) = encodePair (fresh, old)
  exact congrArg encodePair ((assembly width).symm_apply_apply (fresh, old))

/-- Every auxiliary binary bit reads its actual prepared physical wire value without alteration. -/
lemma basisEquiv_auxiliary (width : Nat)
    (fresh : (auxiliaryLayout width).register.Index) (old : (before width).register.Index)
    (index : Fin (auxiliaryWidth width)) :
    (basisEquiv width (assembly width (fresh, old))).val.testBit
      (auxiliaryPosition width index).rev.val = finTwoEquiv (fresh index) := by
  rw [basisEquiv_assembly, BinaryBasis.bigEndianEquiv_bit]
  exact congrArg finTwoEquiv
    (joinCells_auxiliary width (fun position => fresh position) (inputCells width old) index)

/-- Every original input bit retains the supplied unknown value at its actual source address. -/
lemma basisEquiv_input (width : Nat)
    (fresh : (auxiliaryLayout width).register.Index) (old : (before width).register.Index)
    (index : Fin width) :
    (basisEquiv width (assembly width (fresh, old))).val.testBit
      (inputPosition width index).rev.val =
        (inputBasisEquiv width old).val.testBit index.rev.val := by
  rw [basisEquiv_assembly, BinaryBasis.bigEndianEquiv_bit]
  calc
    _ = finTwoEquiv (inputCells width old index) := congrArg finTwoEquiv
      (joinCells_input width (fun position => fresh position) (inputCells width old) index)
    _ = _ := by
      change finTwoEquiv ((BinaryBasis.bigEndianEquiv width).symm
        (inputBasisEquiv width old) index) = _
      rw [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]

/-- Actual preparation supplies the fixed source value on each new physical identity. -/
lemma basisEquiv_prepared_auxiliary (modulus : Nat)
    (old : (before modulus.size).register.Index) (index : Fin (auxiliaryWidth modulus.size)) :
    (basisEquiv modulus.size (assembly modulus.size ((preparation modulus).value, old))).val.testBit
      (auxiliaryPosition modulus.size index).rev.val =
        fixedBit modulus (auxiliaryPhysicalIndex modulus.size index) := by
  rw [basisEquiv_auxiliary, preparation_bit]

end

end QuantumAlg.MAU.Inversion.SharedEEA.InputAssembly
