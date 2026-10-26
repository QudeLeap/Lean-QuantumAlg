/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Address
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Selection
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.BitVec
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber

/-!
# The actual source feed selects the same complete physical table row

The mathematical feed's physical projection is the original complete Raw
label with exactly its current digit replaced. This names an observation-
space basis permutation, not a new executed overwrite or free gate. Every
other physical coordinate is retained, including the other stream top and
the twelve unused tail suffix bits. The same complete unsigned source digit
is the actual table row, with no nonzero or point-domain premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution EncodedBit.WindowLookup
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

private def placedLabel {Data : Type} {ctx : RuntimeCtx .quantum}
    (encoding : BinaryLabelEncoding Data) (physical : QubitLayout encoding.width)
    (same : physical.toQuantum.wires = ctx.quantumLayout.wires) (state : Data) :
    ctx.register.Index :=
  basisOfEqualWires physical.toQuantum ctx.quantumLayout same
    (physical.basisEquiv.symm (encoding.encode state))

private lemma placedLabel_bit {Data : Type} {ctx : RuntimeCtx .quantum}
    (encoding : BinaryLabelEncoding Data) (physical : QubitLayout encoding.width)
    (same : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bit : EncodedBit encoding) (state : Data) :
    (placedLabel encoding physical same state
      (positionsOfEqualWires physical.toQuantum ctx.quantumLayout same bit.wire)).val =
        (finTwoEquiv.symm (bit.get state)).val :=
  (basisOfEqualWires_value physical.toQuantum ctx.quantumLayout same _ bit.wire).trans
    (congrArg Fin.val (encodedPhysicalBit physical bit state))

private lemma basisOfEqualWires_at {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (same : left.wires = right.wires) (first last : left.Basis)
    (position : Fin rightCount)
    (retained : first ((positionsOfEqualWires left right same).symm position) =
      last ((positionsOfEqualWires left right same).symm position)) :
    basisOfEqualWires left right same first position =
      basisOfEqualWires left right same last position := by
  let original := (positionsOfEqualWires left right same).symm position
  have image : positionsOfEqualWires left right same original = position :=
    (positionsOfEqualWires left right same).apply_symm_apply position
  have updated := basisOfEqualWires_value left right same first original
  have initial := basisOfEqualWires_value left right same last original
  rw [image] at updated initial
  apply Fin.ext
  exact updated.trans ((congrArg Fin.val retained).trans initial.symm)

private lemma placedLabel_set_complement {Data : Type} {ctx : RuntimeCtx .quantum}
    {totalBits active : Nat} (encoding : BinaryLabelEncoding Data)
    (physical : QubitLayout encoding.width)
    (same : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : EncodedBit.Word encoding active)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (ports : Ports ctx totalBits active)
    (wiresMatch : ∀ index, ports.wires index =
      positionsOfEqualWires physical.toQuantum ctx.quantumLayout same
        (target.bit index.rev).wire)
    (value : Fin (2 ^ active)) (state : Data) :
    (bankCoordinates ports.wires ports.qubits
      (placedLabel encoding physical same (resultSetConstant target value state))).2 =
      (bankCoordinates ports.wires ports.qubits
        (placedLabel encoding physical same state)).2 := by
  apply (bankCoordinates_complement_eq_iff ports.wires ports.qubits _ _).mpr
  intro position outside
  let original := (positionsOfEqualWires physical.toQuantum ctx.quantumLayout same).symm position
  have originalOutside : original ∉ Finset.univ.map (wordPosition target distinct) := by
    intro member
    obtain ⟨index, _, equal⟩ := Finset.mem_map.mp member
    apply outside
    apply (physicalBankEmbedding_member ports.wires position).mpr
    refine ⟨index.rev, ?_⟩
    have matched : ports.wires index.rev =
        positionsOfEqualWires physical.toQuantum ctx.quantumLayout same
          (target.bit index).wire := by
      simpa only [Fin.rev_rev] using wiresMatch index.rev
    exact matched.trans
      ((congrArg (positionsOfEqualWires physical.toQuantum ctx.quantumLayout same)
        equal).trans ((positionsOfEqualWires _ _ same).apply_symm_apply position))
  have retained := congrFun
    (resultSetConstant_complement physical target distinct value state)
    ⟨original, Finset.mem_compl.mpr originalOutside⟩
  exact basisOfEqualWires_at physical.toQuantum ctx.quantumLayout same _ _ position retained

private lemma placedLabel_set_bank {Data : Type} {ctx : RuntimeCtx .quantum}
    {totalBits active : Nat} (encoding : BinaryLabelEncoding Data)
    (physical : QubitLayout encoding.width)
    (same : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : EncodedBit.Word encoding active)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (ports : Ports ctx totalBits active)
    (wiresMatch : ∀ index, ports.wires index =
      positionsOfEqualWires physical.toQuantum ctx.quantumLayout same
        (target.bit index.rev).wire)
    (value : Fin (2 ^ active)) (state : Data) :
    bankCoordinates ports.wires ports.qubits
        (placedLabel encoding physical same (resultSetConstant target value state)) =
      ((binaryEquiv active).symm value,
        (bankCoordinates ports.wires ports.qubits
          (placedLabel encoding physical same state)).2) := by
  apply Prod.ext
  · apply tupleCoordinates_injective active
    funext index
    rw [bankCoordinates_values]
    apply Fin.ext
    change (placedLabel encoding physical same (resultSetConstant target value state)
      (ports.wires index)).val =
        ((tupleCoordinates active ((binaryEquiv active).symm value)) index).val
    rw [wiresMatch]
    have actual := placedLabel_bit encoding physical same (target.bit index.rev)
      (resultSetConstant target value state)
    rw [resultSetConstant_get target distinct] at actual
    simpa only [tupleCoordinates, Equiv.apply_symm_apply,
      BinaryBasis.bigEndianEquiv_symm_value] using actual
  · exact placedLabel_set_complement encoding physical same target distinct ports
      wiresMatch value state

private lemma selectedFeed_set_label {Data : Type} {ctx : RuntimeCtx .quantum}
    {totalBits active : Nat} {S Rest : Register} (encoding : BinaryLabelEncoding Data)
    (physical : QubitLayout encoding.width)
    (same : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : EncodedBit.Word encoding active)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (ports : Ports ctx totalBits active)
    (wiresMatch : ∀ index, ports.wires index =
      positionsOfEqualWires physical.toQuantum ctx.quantumLayout same
        (target.bit index.rev).wire)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (state : Data) (source : S.Index) (reference : Reference.Index) :
    (selectedFeedBasis ports partition Reference
      (placedLabel encoding physical same state, source, reference)).1 =
      placedLabel encoding physical same
        (resultSetConstant target (partition source).1 state) := by
  apply (bankCoordinates ports.wires ports.qubits).injective
  have set := placedLabel_set_bank encoding physical same target distinct ports wiresMatch
    (partition source).1 state
  simpa only [selectedFeedBasis, Equiv.apply_symm_apply] using set.symm

/-- Original MSB-first digit as a little-endian numerical setter word. -/
def digitWord (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    EncodedBit.Word encoding (width + 1) where
  bit index := Enable.digitBit stream width bounded index.rev

lemma digitWord_distinct (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    Function.Injective fun index => ((digitWord stream width bounded).bit index).wire :=
  (Enable.digitBit_injective stream width bounded).comp Fin.rev_injective

/-- Mathematical Raw label of the same source feed, with every complement retained. -/
def sourceFedRaw {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
    (index : WindowIndex) (source : SourceRegister.Index) (state : Raw) : Raw :=
  resultSetConstant (digitWord index.stream index.lowerWidth index.lowerWidth_bound)
    (parameters.sourcePartition index source).1 state

lemma sourceFedRaw_digit {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
    (index : WindowIndex) (source : SourceRegister.Index) (state : Raw)
    (bit : Fin (index.lowerWidth + 1)) :
    (Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit).get
        (sourceFedRaw parameters index source state) =
      (parameters.sourcePartition index source).1.val.testBit bit.rev.val := by
  have actual := resultSetConstant_get
    (digitWord index.stream index.lowerWidth index.lowerWidth_bound)
    (digitWord_distinct _ _ _) (parameters.sourcePartition index source).1 state bit.rev
  simpa only [sourceFedRaw, digitWord, Fin.rev_rev] using actual

/-- Every genuinely unselected original bit, including saved tail suffix bits, is unchanged. -/
lemma sourceFedRaw_other {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
    (index : WindowIndex) (source : SourceRegister.Index) (state : Raw)
    (observed : EncodedBit encoding)
    (outside : ∀ bit, (Enable.digitBit index.stream index.lowerWidth
      index.lowerWidth_bound bit).wire ≠ observed.wire) :
    observed.get (sourceFedRaw parameters index source state) = observed.get state :=
  resultSetConstant_observed _ _ observed (fun bit => outside bit.rev) state

namespace Parameters

/-- Same complete encoded label in the actual caller's original ordered wire coordinates. -/
def physicalLabel {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx) (state : Raw) :
    ctx.register.Index :=
  placedLabel encoding (QubitLayout.canonical encoding.width) parameters.sameWires state

/-- Exact full physical projection of the original mathematical source feed. -/
lemma sourceFeed_physicalLabel {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
    (index : WindowIndex) (Reference : Register) (state : Raw)
    (source : SourceRegister.Index) (reference : Reference.Index) :
    (selectedFeedBasis (parameters.ports index) (parameters.sourcePartition index) Reference
      (parameters.physicalLabel state, source, reference)).1 =
        parameters.physicalLabel (sourceFedRaw parameters index source state) := by
  exact selectedFeed_set_label (S := SourceRegister)
    (Rest := labelRemainder (streamPositions (parameters.ports index)))
    encoding (QubitLayout.canonical encoding.width)
    parameters.sameWires (digitWord index.stream index.lowerWidth index.lowerWidth_bound)
    (digitWord_distinct _ _ _) (parameters.ports index) (fun bit => by
      change parameters.wire index bit = parameters.wire index bit.rev.rev
      exact congrArg (parameters.wire index) (Fin.rev_rev bit).symm)
    (parameters.sourcePartition index) Reference state source reference

end Parameters

private lemma index_of_parts (width : Nat) (top : Bool) (address : Fin (2 ^ width))
    (value : Fin (2 ^ (width + 1))) (topRead : top = value.val.testBit width)
    (addressRead : address.val = value.val % 2 ^ width) :
    RuntimeTable.index top address = value := by
  apply Fin.ext
  change address.val + (if top then 2 ^ width else 0) = value.val
  rw [topRead, addressRead]
  have split := EncodedBit.WindowLookup.SelectorFrame.mod_two_pow_succ_bit value.val width
  rw [Nat.mod_eq_of_lt value.isLt] at split
  omega

private lemma selectedRow_of_digit (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Raw) (value : Fin (2 ^ (width + 1)))
    (reads : ∀ bit, (Enable.digitBit stream width bounded bit).get state =
      value.val.testBit bit.rev.val) :
    Tables.selectedRow stream width bounded state = value := by
  let low : BitVec width := BitVec.ofNat width value.val
  have addressBits (bit : Fin width) :
      ((selector stream width bounded).address bit).get state = low.getMsbD bit.val := by
    have actual := reads bit.succ
    change (addressBit ⟨bit.val, by omega⟩).get state = _ at actual
    change (addressBit ⟨bit.val, by omega⟩).get state = _
    rw [actual]
    have lower : width - 1 - bit.val < width := by omega
    simp only [low, BitVec.getMsbD_eq_getLsbD, bit.isLt, decide_true, Bool.true_and,
      BitVec.getLsbD_ofNat, lower]
    congr 1
    simp only [Fin.val_rev, Fin.val_succ]
    omega
  have address := (selector stream width bounded).addressLabelAt_bitVec low state addressBits
  have top : (streamBit stream).get state = value.val.testBit width := by
    simpa only [Enable.digitBit, Fin.cases_zero, Fin.val_rev, Fin.val_zero,
      Nat.sub_zero, Nat.add_sub_cancel] using reads 0
  have actual := congrArg (RuntimeTable.index ((streamBit stream).get state)) address
  exact actual.trans (index_of_parts width ((streamBit stream).get state) low.toFin value top rfl)

/-- The actual complete row is exactly the selected source digit, with zero retained. -/
lemma sourceFedRaw_selectedRow {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
    (index : WindowIndex) (source : SourceRegister.Index) (state : Raw) :
    Tables.selectedRow index.stream index.lowerWidth index.lowerWidth_bound
        (sourceFedRaw parameters index source state) =
      (parameters.sourcePartition index source).1 :=
  selectedRow_of_digit _ _ _ _ _ (sourceFedRaw_digit parameters index source state)

/-- Original unsigned radix digit, without any reduction modulo the subgroup order. -/
lemma sourceFedRaw_selectedRow_val {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
    (index : WindowIndex) (source : SourceRegister.Index) (state : Raw) :
    (Tables.selectedRow index.stream index.lowerWidth index.lowerWidth_bound
      (sourceFedRaw parameters index source state)).val =
      Nat.FixedWidth.Radix.digit (2 ^ 16) (sourceValue index source).val index.logical.val :=
  (congrArg Fin.val (sourceFedRaw_selectedRow parameters index source state)).trans
    (parameters.sampling_sourcePartition_digit_val index source)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
