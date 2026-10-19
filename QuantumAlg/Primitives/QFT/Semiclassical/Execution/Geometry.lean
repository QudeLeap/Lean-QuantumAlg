/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import all QuantumAlg.Primitives.QFT.Semiclassical.PhaseMatrix.Source
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Fourier bank coordinates from actual physical wire positions

The selected bank is constructed from the supplied injection of real wire
positions. Every local coordinate is a dimension cast; all remaining wires
and the external reference remain explicit complementary coordinates. These
equivalences describe coordinates, not a SWAP, state reset or runtime action.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- The selected physical bank retains every ambient wire identity and dimension. -/
def physicalBankLayout {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount) : QuantumLayout n where
  wire := fun index => ctx.quantumLayout.wire (wires index)
  identityInjective := fun _ _ same => wires.injective (ctx.quantumLayout.identityInjective same)

/-- Only the existing physical position injection embeds the bank. -/
def physicalBankEmbedding {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount) :
    QuantumLayout.Embedding (physicalBankLayout wires) ctx.quantumLayout where
  position := wires
  wire_eq := fun _ => rfl

/-- The supplied qubit dimension proofs provide canonical local basis casts. -/
def physicalBankPlacement {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) :
    QuantumSignature.Placement (QuantumSignature.qubits n) where
  layout := physicalBankLayout wires
  dimension_eq := qubits

/-- The physical bank in MSB-first tuple order, with all unselected systems retained. -/
def bankCoordinates {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) :
    ctx.register.Index ≃ Bits n ×
      ctx.quantumLayout.ComplementBasis (physicalBankEmbedding wires).selection :=
  (physicalBankEmbedding wires).splitBasis.trans
    (Equiv.prodCongr
      ((physicalBankPlacement wires qubits).indexEquiv.trans
        ((QuantumSignature.qubitsIndexEquiv n).trans (binaryEquiv n).symm))
      (Equiv.refl _))

/-- The selected tuple label is exactly the native feedback's physical tail label. -/
lemma bankCoordinates_label {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index) :
    binaryEquiv n (bankCoordinates wires qubits basis).1 =
      physicalTailLabel wires qubits basis := by
  change (binaryEquiv n) ((binaryEquiv n).symm
    (QuantumSignature.qubitsIndexEquiv n
      ((physicalBankPlacement wires qubits).indexEquiv
        ((physicalBankEmbedding wires).splitBasis basis).1))) = _
  rw [Equiv.apply_symm_apply]
  apply congrArg (BinaryBasis.bigEndianEquiv n)
  funext index
  apply Fin.ext
  exact QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (physicalBankEmbedding wires) basis index

/-- Source tuple coordinates read the selected physical values without any permutation. -/
lemma bankCoordinates_values {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index) :
    tupleCoordinates n (bankCoordinates wires qubits basis).1 =
      fun index => Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits index))
        (basis (wires index)) := by
  unfold tupleCoordinates
  rw [bankCoordinates_label]
  exact (BinaryBasis.bigEndianEquiv n).symm_apply_apply _

/-- The leading tuple bit is the actual selected physical head value. -/
lemma bankCoordinates_head_value {n : Nat} (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index) :
    (bankCoordinates wires qubits basis).1.1 =
      Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)) (basis (wires 0)) := by
  exact (tupleCoordinates_head n _ _).symm.trans
    (congrFun (bankCoordinates_values wires qubits basis) 0)

/-- The remaining source tuple reads the actual selected tail values. -/
lemma bankCoordinates_tail_values {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index) (index : Fin n) :
    tupleCoordinates n (bankCoordinates wires qubits basis).1.2 index =
      Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits index.succ))
        (basis (wires index.succ)) := by
  exact (tupleCoordinates_tail n _ _ index).symm.trans
    (congrFun (bankCoordinates_values wires qubits basis) index.succ)

/-- The selected bank consists of exactly the supplied actual positions. -/
lemma physicalBankEmbedding_member {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (position : Fin ctx.systemCount) :
    position ∈ (physicalBankEmbedding wires).selection ↔
      ∃ index : Fin n, wires index = position := by
  constructor
  · intro member
    rcases Finset.mem_map.mp member with ⟨index, _, equal⟩
    exact ⟨index, equal⟩
  · rintro ⟨index, rfl⟩
    exact Finset.mem_map_of_mem _ (Finset.mem_univ _)

/-- Every unselected physical coordinate is retained literally in the bank complement. -/
lemma bankCoordinates_complement_value {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index)
    (index : QuantumLayout.SelectedPosition (physicalBankEmbedding wires).selectionᶜ) :
    (bankCoordinates wires qubits basis).2 index = basis index.val := rfl

/-- Complement agreement compares all actual unselected systems at their original positions. -/
lemma bankCoordinates_complement_eq_iff {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (row column : ctx.register.Index) :
    (bankCoordinates wires qubits row).2 = (bankCoordinates wires qubits column).2 ↔
      ∀ position : Fin ctx.systemCount,
        position ∉ (physicalBankEmbedding wires).selection → row position = column position := by
  constructor
  · intro same position outside
    exact congrFun same ⟨position, Finset.mem_compl.mpr outside⟩
  · intro same
    funext index
    exact same index.val (Finset.mem_compl.mp index.property)

/-- Tail tuple agreement is exactly agreement of all actual selected tail values. -/
lemma bankCoordinates_tail_eq_iff {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (row column : ctx.register.Index) :
    (bankCoordinates wires qubits row).1.2 = (bankCoordinates wires qubits column).1.2 ↔
      ∀ index : Fin n, row (wires index.succ) = column (wires index.succ) := by
  constructor
  · intro same index
    have values := congrArg (fun tail => tupleCoordinates n tail index) same
    rw [bankCoordinates_tail_values, bankCoordinates_tail_values] at values
    apply Fin.ext
    exact congrArg (fun bit : Fin 2 => bit.val) values
  · intro same
    apply tupleCoordinates_injective n
    funext index
    rw [bankCoordinates_tail_values, bankCoordinates_tail_values, same index]

/-- All physical positions except the head are exactly the tail and bank complement. -/
lemma bankCoordinates_outside_head_iff {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (row column : ctx.register.Index) :
    (∀ position : Fin ctx.systemCount, position ≠ wires 0 → row position = column position) ↔
      (bankCoordinates wires qubits row).1.2 = (bankCoordinates wires qubits column).1.2 ∧
        (bankCoordinates wires qubits row).2 = (bankCoordinates wires qubits column).2 := by
  rw [bankCoordinates_tail_eq_iff, bankCoordinates_complement_eq_iff]
  constructor
  · intro outside
    constructor
    · intro index
      exact outside (wires index.succ) (fun same =>
        Fin.succ_ne_zero index (wires.injective same))
    · intro position unselected
      exact outside position (fun same => unselected
        ((physicalBankEmbedding_member wires position).mpr ⟨0, same.symm⟩))
  · rintro ⟨tail, complement⟩ position different
    by_cases selected : position ∈ (physicalBankEmbedding wires).selection
    · rcases (physicalBankEmbedding_member wires position).mp selected with ⟨index, equal⟩
      subst position
      revert different
      refine Fin.cases ?_ (fun index => ?_) index
      · intro impossible
        exact False.elim (impossible rfl)
      · intro _
        exact tail index
    · exact complement position selected

/-- External-reference coordinates remain beside the untouched physical complement. -/
def bankReferenceCoordinates {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (Reference : Register) :
    (ctx.register.prod Reference).Index ≃ Bits n ×
      (ctx.quantumLayout.ComplementBasis
        (physicalBankEmbedding wires).selection × Reference.Index) :=
  (Equiv.prodCongr (bankCoordinates wires qubits) (Equiv.refl Reference.Index)).trans
    (Equiv.prodAssoc _ _ _)

/-- Decoding a classical Fourier frequency leaves the actual bank at reverseBits of that value. -/
lemma bankCoordinates_frequency_label {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index) (frequency : Fin (2 ^ n))
    (physical : (bankCoordinates wires qubits basis).1 = frequencyBits n frequency) :
    physicalTailLabel wires qubits basis = qftReverseBits n frequency := by
  rw [← bankCoordinates_label, physical]
  exact qftSemiclassical_frequencyBits_physicalLabel n frequency

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
