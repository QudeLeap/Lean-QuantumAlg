/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Registers
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Place an actual low-counter program on the original shared registers

The complete Work1 word, low shift, and Phase2 form the native arithmetic
interface. Every other named source field is tensored alongside it
[LYL+26, sec_EEA/sub_regshare.tex:16-26]. The exact basis map decodes and
reassembles those same named fields through their actual binary encodings.
Its inverse is the same proved field grouping, rather than an equivalence
chosen from cardinalities.

The physical map is applied to the existing native leaves and uses exactly
the addresses checked by the corresponding semantic bit lenses. The
original ordered events remain intact. This is placement of an existing
program, not an implementation of an arbitrary semantic permutation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LowShiftPlacement

noncomputable section

open LowShiftRegisters

private def remainderEncoding (width : Nat) : BinaryLabelEncoding (Remainder width) :=
  BinaryLabelEncoding.prod (wordEncoding (width + 3))
    (BinaryLabelEncoding.prod (lengthPairEncoding width)
      (BinaryLabelEncoding.prod (wordEncoding width.size) flagEncoding))

private theorem remainder_surjective (width : Nat) :
    Function.Surjective (remainderEncoding width).encode :=
  prod_surjective _ _ (word_surjective _) (prod_surjective _ _
    (prod_surjective _ _ (word_surjective _) (word_surjective _))
    (prod_surjective _ _ (word_surjective _)
      (prod_surjective _ _ (prod_surjective _ _ bool_surjective bool_surjective)
        (prod_surjective _ _ bool_surjective bool_surjective))))

private theorem focus_surjective (width : Nat) :
    Function.Surjective (Addition.HRS.bridgeEncoding (width + 3) width.size).encode :=
  prod_surjective _ _ (prod_surjective _ _ Function.surjective_id Function.surjective_id)
    bool_surjective

@[implicit_reducible]
private def groupedEncoding (width : Nat) : BinaryLabelEncoding
    (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size × Remainder width) :=
  BinaryLabelEncoding.prod (Addition.HRS.bridgeEncoding (width + 3) width.size)
    (remainderEncoding width)

private def groupedLabelEquiv (width : Nat) :
    (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size × Remainder width) ≃
      (Qubits (groupedEncoding width).width).Index :=
  Equiv.ofBijective (groupedEncoding width).encode
    ⟨(groupedEncoding width).encode_injective,
      prod_surjective _ _ (focus_surjective width) (remainder_surjective width)⟩

private def registerLabelEquiv (width : Nat) :
    Registers width ≃ (Qubits (encoding width).width).Index :=
  Equiv.ofBijective (encoding width).encode
    ⟨(encoding width).encode_injective, encoding_surjective width⟩

/-- Decode the actual product fields and reassemble the same full source register label. -/
def indexEquiv (width : Nat) :
    (Qubits (groupedEncoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  (groupedLabelEquiv width).symm.trans
    ((grouping width).symm.trans (registerLabelEquiv width))

/-- The complete explicit grouping is exactly the basis transport, for every field value. -/
theorem indexEquiv_encode (width : Nat) (state : Registers width) :
    indexEquiv width ((groupedEncoding width).encode (grouping width state)) =
      (encoding width).encode state := by
  change registerLabelEquiv width ((grouping width).symm
    ((groupedLabelEquiv width).symm (groupedLabelEquiv width (grouping width state)))) =
      registerLabelEquiv width state
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private def raw (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.reindex (indexEquiv width)
    (UnitaryCircuit.prodLeft (n := (remainderEncoding width).width) body)

private theorem raw_range (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width))
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1)) :
    (raw width body).physical_idx ⊆ List.range (width + 3 + width.size + 1) := by
  change (UnitaryCircuit.prodLeft (n := (remainderEncoding width).width) body).physical_idx ⊆ _
  unfold UnitaryCircuit.prodLeft
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · exact within
  · simp only [UnitaryCircuit.identity, List.nil_subset]

private theorem mapped_nodup (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width))
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1)) :
    ((raw width body).physical_idx.map (physicalIndex width)).Nodup := by
  apply List.Nodup.map_on _ (raw width body).physical_idx_nodup
  intro left leftPresent right rightPresent same
  have leftBound := List.mem_range.mp (raw_range width body within leftPresent)
  have rightBound := List.mem_range.mp (raw_range width body within rightPresent)
  exact congrArg Fin.val (physicalIndex_injective width
    (a₁ := ⟨left, leftBound⟩) (a₂ := ⟨right, rightBound⟩) same)

private def addressed (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width))
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.relabel (raw width body)
    { toFun := physicalIndex width
      map_layout := rfl
      old_nodup := (raw width body).physical_idx_nodup
      new_nodup := mapped_nodup width body within }

private theorem addressed_range (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width))
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1)) :
    (addressed width body within).physical_idx ⊆ List.range (encoding width).width := by
  intro wire present
  change wire ∈ (raw width body).physical_idx.map (physicalIndex width) at present
  rcases List.mem_map.mp present with ⟨old, oldPresent, rfl⟩
  exact List.mem_range.mpr (physicalIndex_within width
    ⟨old, List.mem_range.mp (raw_range width body within oldPresent)⟩)

/-- Place the existing native arithmetic among the exact full original live source fields. -/
def place (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width))
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (addressed width body within).seq
    (UnitaryCircuit.identity (Qubits (encoding width).width)
      (List.range (encoding width).width) List.nodup_range)

/-- The full semantic action retains every explicit complementary field. -/
def placedStep {width : Nat}
    (action : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size →
      Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size)
    (state : Registers width) : Registers width :=
  (grouping width).symm (action (grouping width state).1, (grouping width state).2)

/-- Exact basis amplitudes are preserved by the same actual tensor and wire transport. -/
theorem place_realizes (width : Nat)
    {body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width)}
    {action : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size →
      Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size}
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1))
    (realizes : UnitaryCircuit.Realizes
      (Addition.HRS.bridgeEncoding (width + 3) width.size) body action) :
    UnitaryCircuit.Realizes (encoding width) (place width body within) (placedStep action) where
  apply_encoded_ket := by
    intro state
    have extended := (realizes.prodLeft (right := remainderEncoding width)).apply_encoded_ket
      (grouping width state)
    have transported := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (groupedEncoding width).width) (S := Qubits (encoding width).width)
      (indexEquiv width) (UnitaryCircuit.prodLeft (n := (remainderEncoding width).width) body)
        _ _ extended
    have output : (action (grouping width state).1, (grouping width state).2) =
        grouping width (placedStep action state) :=
      ((grouping width).apply_symm_apply _).symm
    rw [output] at transported
    have inputKet := congrArg
      (fun label : (Qubits (encoding width).width).Index =>
        NormalizedVector.ket (R := Qubits (encoding width).width) label)
      (indexEquiv_encode width state)
    have outputKet := congrArg
      (fun label : (Qubits (encoding width).width).Index =>
        NormalizedVector.ket (R := Qubits (encoding width).width) label)
      (indexEquiv_encode width (placedStep action state))
    have encodedRun := (congrArg (raw width body).applyNormalized inputKet.symm).trans
      (transported.trans outputKet)
    unfold place
    rw [UnitaryCircuit.applyNormalized_seq, UnitaryCircuit.applyNormalized_identity]
    unfold addressed
    rw [UnitaryCircuit.Realizes.applyNormalized_relabel]
    exact encodedRun

/-- The complete declared footprint is exactly the original frame; no helper wire is added. -/
theorem place_physical (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width))
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1)) :
    (place width body within).physical_idx = List.range (encoding width).width := by
  change UnitaryCircuit.unionPhysicalIdx (addressed width body within).physical_idx
    (List.range (encoding width).width) = _
  exact UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _ (addressed_range width body within)

/-- Tensor spectators and physical placement preserve every original native event in order. -/
theorem place_eventTrace (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width))
    (within : body.physical_idx ⊆ List.range (width + 3 + width.size + 1)) :
    (place width body within).eventTrace = body.eventTrace := by
  have empty : (UnitaryCircuit.identity (Qubits (encoding width).width)
      (List.range (encoding width).width) List.nodup_range).eventTrace = [] := rfl
  rw [place, UnitaryCircuit.seq_eventTrace, empty, List.append_nil, addressed,
    UnitaryCircuit.relabel_eventTrace, raw]
  exact (UnitaryCircuit.reindex_eventTrace
    (R := Qubits (groupedEncoding width).width) (S := Qubits (encoding width).width)
    (indexEquiv width) (UnitaryCircuit.prodLeft (n := (remainderEncoding width).width) body)).trans
      (UnitaryCircuit.prodLeft_eventTrace body)

end

end QuantumAlg.MAU.Inversion.SharedEEA.LowShiftPlacement
