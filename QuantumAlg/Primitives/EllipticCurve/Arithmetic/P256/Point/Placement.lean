/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Ports
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Frame
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Square.Copy
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Program
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem
import Mathlib.Data.Sum.Basic

/-!
# Complete original three-word coordinates for native P-256 arithmetic

The source, accumulator and retained multiplier are three distinct
original word ports. Exactly three original scan-pool positions supply
the arithmetic flags. The completion contains every other original
physical coordinate, including padding, history, remaining pool and
C/N/W. This certificate places actual native instructions; it does not
execute a data permutation or allocate a word.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point

noncomputable section

open QuantumAlg.EncodedBit

/-- Static original-port assignment; the retained word is separate from both changing operands. -/
structure PortAssignment where
  source : WordPort
  target : WordPort
  multiplier : WordPort
  source_target : source ≠ target
  source_multiplier : source ≠ multiplier
  target_multiplier : target ≠ multiplier

namespace Placement

private abbrev Picks := ((Fin 256 ⊕ Fin 256) ⊕ Fin 3) ⊕ Fin 256

/-- Source, accumulator and the three flags precede the retained multiplier word. -/
abbrev prefixEncoding :=
  BinaryLabelEncoding.prod ModularAddition.Controlled.selectorEncoding
    (BinaryLabelEncoding.finIdentity 256)

private def groupedPicks (wordWidth flags : Nat) :
    Fin ((wordWidth + wordWidth + flags) + wordWidth) ≃
      ((Fin wordWidth ⊕ Fin wordWidth) ⊕ Fin flags) ⊕ Fin wordWidth :=
  (finSumFinEquiv (m := wordWidth + wordWidth + flags) (n := wordWidth)).symm.trans
    (Equiv.sumCongr
      ((finSumFinEquiv (m := wordWidth + wordWidth) (n := flags)).symm.trans
        (Equiv.sumCongr (finSumFinEquiv (m := wordWidth) (n := wordWidth)).symm
          (Equiv.refl (Fin flags)))) (Equiv.refl (Fin wordWidth)))

private lemma groupedPicks_source (wordWidth flags : Nat) (index : Fin wordWidth) :
    groupedPicks wordWidth flags
        (Fin.castAdd wordWidth (Fin.castAdd flags (Fin.castAdd wordWidth index))) =
      Sum.inl (Sum.inl (Sum.inl index)) := by
  simp only [groupedPicks, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl]

private lemma groupedPicks_target (wordWidth flags : Nat) (index : Fin wordWidth) :
    groupedPicks wordWidth flags
        (Fin.castAdd wordWidth (Fin.castAdd flags (Fin.natAdd wordWidth index))) =
      Sum.inl (Sum.inl (Sum.inr index)) := by
  simp only [groupedPicks, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inl]

private lemma groupedPicks_flag (wordWidth flags : Nat) (index : Fin flags) :
    groupedPicks wordWidth flags
        (Fin.castAdd wordWidth (Fin.natAdd (wordWidth + wordWidth) index)) =
      Sum.inl (Sum.inr index) := by
  simp only [groupedPicks, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.refl_apply]

private lemma groupedPicks_multiplier (wordWidth flags : Nat) (index : Fin wordWidth) :
    groupedPicks wordWidth flags (Fin.natAdd (wordWidth + wordWidth + flags) index) =
      Sum.inr index := by
  simp only [groupedPicks, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]

private def prefixPicks : Fin prefixEncoding.width ≃ Picks := groupedPicks 256 3

private def pickPosition (ports : PortAssignment) : Picks → Fin Frame.encoding.width :=
  Sum.elim
    (Sum.elim
      (Sum.elim (fun index => (ports.source.bit index.rev).wire)
        (fun index => (ports.target.bit index.rev).wire))
      (fun flag => (arithmeticFlag flag).wire))
    (fun index => (ports.multiplier.bit index.rev).wire)

private lemma word_reverse_injective (port : WordPort) :
    Function.Injective (fun index : Fin 256 => (port.bit index.rev).wire) := by
  intro left right same
  exact Fin.rev_inj.mp (WordPort.bit_index_injective port same)

private lemma pickPosition_injective (ports : PortAssignment) :
    Function.Injective (pickPosition ports) := by
  have words := (word_reverse_injective ports.source).sumElim
    (word_reverse_injective ports.target)
    (fun first second => WordPort.bit_ports_disjoint ports.source ports.target
      ports.source_target first.rev second.rev)
  have flags := words.sumElim arithmeticFlag_injective (by
    intro selected flag
    cases selected with
    | inl index => exact word_flag_disjoint ports.source index.rev flag
    | inr index => exact word_flag_disjoint ports.target index.rev flag)
  exact flags.sumElim (word_reverse_injective ports.multiplier) (by
    intro selected index
    rcases selected with (first | second) | flag
    · exact WordPort.bit_ports_disjoint ports.source ports.multiplier
        ports.source_multiplier first.rev index.rev
    · exact WordPort.bit_ports_disjoint ports.target ports.multiplier
        ports.target_multiplier second.rev index.rev
    · exact (word_flag_disjoint ports.multiplier index.rev flag).symm)

/-- Select only existing original word and pool coordinates in their exact arithmetic roles. -/
def subsystem (ports : PortAssignment) : WireSubsystem prefixEncoding Frame.encoding where
  wires :=
    { toFun := fun index => pickPosition ports (prefixPicks index)
      inj' := (pickPosition_injective ports).comp prefixPicks.injective }

private def complementIndex {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (selected : WireSubsystem source target) (bit : selected.Complement) :
    Fin selected.complementWidth := Fintype.equivFin selected.Complement bit

private lemma completed_complementIndex {Source Target : Type}
    {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
    (selected : WireSubsystem source target) (bit : selected.Complement) :
    selected.completedWires (Fin.natAdd source.width (complementIndex selected bit)) = bit.val := by
  exact (selected.completedWires_complement (complementIndex selected bit)).trans
    (congrArg Subtype.val ((Fintype.equivFin selected.Complement).symm_apply_apply bit))

-- Retain the finite complement cardinality as a symbolic metadata quantity.
-- It is determined below from the complete wire equivalence, without enumerating its positions.
attribute [local irreducible] WireSubsystem.complementWidth

/-- Exactly the existing physical complement, with no valid-state restriction. -/
abbrev Rest (ports : PortAssignment) := Fin (2 ^ (subsystem ports).complementWidth)

def restEncoding (ports : PortAssignment) : BinaryLabelEncoding (Rest ports) :=
  .finIdentity (subsystem ports).complementWidth

private lemma wire_widths {first second : Nat} (wires : Fin first ≃ Fin second) :
    first = second := by
  simpa only [Fintype.card_fin] using Fintype.card_congr wires

lemma complement_width (ports : PortAssignment) : (subsystem ports).complementWidth = 68 := by
  have sizes := wire_widths (subsystem ports).completedWires
  change 771 + (subsystem ports).complementWidth = Frame.encoding.width at sizes
  rw [Frame.encoding_width] at sizes
  omega

/-- The third original word and every actual unselected bit form the retained caller component. -/
abbrev savedEncoding (ports : PortAssignment) :=
  Accumulate.Square.savedEncoding (restEncoding ports)

abbrev arithmeticEncoding (ports : PortAssignment) := Horner.operandEncoding (savedEncoding ports)

section

attribute [local irreducible] width

private lemma selector_total :
    Function.Surjective ModularAddition.Controlled.selectorEncoding.encode :=
  Frame.product_total _ _ ModularAddition.encoding_onto
    (Frame.product_total _ _ Frame.bool_total Frame.bool_total)

private lemma arithmetic_total (ports : PortAssignment) :
    Function.Surjective (arithmeticEncoding ports).encode :=
  Frame.product_total _ _ selector_total
    (Frame.product_total _ _ (fun label => ⟨label, rfl⟩) (fun label => ⟨label, rfl⟩))

end

private def completeWires (ports : PortAssignment) :
    Fin (arithmeticEncoding ports).width ≃ Fin Frame.encoding.width :=
  (finCongr (Nat.add_assoc 515 256 (subsystem ports).complementWidth).symm).trans
    (subsystem ports).completedWires

/-- Semantic grouping and native physical locations are derived from the same complete wire map. -/
def layout (ports : PortAssignment) : FullPlacement (arithmeticEncoding ports) Frame.encoding :=
  FullPlacement.ofWires _ _ (arithmetic_total ports) Frame.encoding_surjective (completeWires ports)

private lemma completeWires_apply (ports : PortAssignment)
    (wire : Fin (arithmeticEncoding ports).width)
    (completed : Fin (subsystem ports).paddedEncoding.width) (same : wire.val = completed.val) :
    completeWires ports wire = (subsystem ports).completedWires completed := by
  have indices : (finCongr (Nat.add_assoc 515 256 (subsystem ports).complementWidth).symm) wire =
      completed := Fin.ext same
  exact congrArg (subsystem ports).completedWires indices

private lemma prefixPicks_source (index : Fin 256) :
    prefixPicks (Fin.castAdd 256 (Fin.castAdd 3 (Fin.castAdd 256 index))) =
      Sum.inl (Sum.inl (Sum.inl index)) := groupedPicks_source 256 3 index

private lemma prefixPicks_target (index : Fin 256) :
    prefixPicks (Fin.castAdd 256 (Fin.castAdd 3 (Fin.natAdd 256 index))) =
      Sum.inl (Sum.inl (Sum.inr index)) := groupedPicks_target 256 3 index

private lemma prefixPicks_flag (index : Fin 3) :
    prefixPicks (Fin.castAdd 256 (Fin.natAdd 512 index)) =
      Sum.inl (Sum.inr index) := groupedPicks_flag 256 3 index

private lemma prefixPicks_multiplier (index : Fin 256) :
    prefixPicks (Fin.natAdd 515 index) = Sum.inr index := groupedPicks_multiplier 256 3 index

private lemma completeWires_source (ports : PortAssignment) (index : Fin 256) :
    completeWires ports (Horner.operandSourceBit (savedEncoding ports) index).wire =
      (ports.source.bit index).wire := by
  refine (completeWires_apply ports _
    (Fin.castAdd (subsystem ports).complementWidth
      (Fin.castAdd 256 (Fin.castAdd 3 (Fin.castAdd 256 index.rev)))) ?_).trans ?_
  · change 256 - 1 - index.val = index.rev.val
    rw [Fin.val_rev]
    omega
  · rw [WireSubsystem.completedWires_source]
    change pickPosition ports (prefixPicks _) = _
    rw [prefixPicks_source]
    simp only [pickPosition, Sum.elim_inl, Fin.rev_rev]

/-- The full grouping reads the actual original quantum source word without a value promise. -/
lemma source_bit_get (ports : PortAssignment) (index : Fin 256) (state : Frame.Raw) :
    (Horner.operandSourceBit (savedEncoding ports) index).get ((layout ports).grouping state) =
      (ports.source.value state).val.testBit index.val :=
  (FullPlacement.ofWires_read _ _ (arithmetic_total ports) Frame.encoding_surjective
    (completeWires ports) (Horner.operandSourceBit (savedEncoding ports) index)
    (ports.source.bit index) (completeWires_source ports index) state).trans
      (WordPort.bit_get ports.source index state)

lemma grouping_source (ports : PortAssignment) (state : Frame.Raw) :
    ((layout ports).grouping state).1.1.1.1 = ports.source.value state := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  exact (Horner.operandSourceBit_get (savedEncoding ports) index _).symm.trans
    (source_bit_get ports index state)

/-- The actual original accumulator bit on the complete arithmetic frame. -/
def targetBit (ports : PortAssignment) (index : Fin 256) :
    EncodedBit (arithmeticEncoding ports) :=
  BinaryLabelEncoding.prodLeftBit ModularAddition.Controlled.selectorEncoding (savedEncoding ports)
    (BinaryLabelEncoding.prodLeftBit ModularAddition.encoding
      ModularAddition.Controlled.flagEncoding (ModularAddition.targetBit index))

private lemma completeWires_target (ports : PortAssignment) (index : Fin 256) :
    completeWires ports (targetBit ports index).wire = (ports.target.bit index).wire := by
  refine (completeWires_apply ports _
    (Fin.castAdd (subsystem ports).complementWidth
      (Fin.castAdd 256 (Fin.castAdd 3 (Fin.natAdd 256 index.rev)))) ?_).trans ?_
  · change 256 + (256 - 1 - index.val) = 256 + index.rev.val
    rw [Fin.val_rev]
    omega
  · rw [WireSubsystem.completedWires_source]
    change pickPosition ports (prefixPicks _) = _
    rw [prefixPicks_target]
    simp only [pickPosition, Sum.elim_inl, Sum.elim_inr, Fin.rev_rev]

lemma target_bit_get (ports : PortAssignment) (index : Fin 256) (state : Frame.Raw) :
    (targetBit ports index).get ((layout ports).grouping state) =
      (ports.target.value state).val.testBit index.val :=
  (FullPlacement.ofWires_read _ _ (arithmetic_total ports) Frame.encoding_surjective
    (completeWires ports) (targetBit ports index) (ports.target.bit index)
    (completeWires_target ports index) state).trans (WordPort.bit_get ports.target index state)

lemma grouping_target (ports : PortAssignment) (state : Frame.Raw) :
    ((layout ports).grouping state).1.1.1.2 = ports.target.value state := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have actual := target_bit_get ports index state
  change (MAU.Addition.TTK.rightBit width index).get
    ((layout ports).grouping state).1.1.1 = _ at actual
  exact (MAU.Addition.TTK.ttkRightBit_get width index _).symm.trans actual

/-- The original third word is retained as the actual quantum multiplier. -/
def multiplierBit (ports : PortAssignment) (index : Fin 256) :
    EncodedBit (arithmeticEncoding ports) :=
  Horner.operandSavedBit (savedEncoding ports)
    ((Accumulate.Square.multiplier (restEncoding ports)).bits index)

private lemma completeWires_multiplier (ports : PortAssignment) (index : Fin 256) :
    completeWires ports (multiplierBit ports index).wire =
      (ports.multiplier.bit index).wire := by
  refine (completeWires_apply ports _
    (Fin.castAdd (subsystem ports).complementWidth (Fin.natAdd 515 index.rev)) ?_).trans ?_
  · change 515 + (256 - 1 - index.val) = 515 + index.rev.val
    rw [Fin.val_rev]
    omega
  · exact ((subsystem ports).completedWires_source (Fin.natAdd 515 index.rev)).trans (by
      change pickPosition ports (prefixPicks _) = _
      rw [prefixPicks_multiplier]
      simp only [pickPosition, Sum.elim_inr, Fin.rev_rev])

lemma multiplier_bit_get (ports : PortAssignment) (index : Fin 256) (state : Frame.Raw) :
    (multiplierBit ports index).get ((layout ports).grouping state) =
      (ports.multiplier.value state).val.testBit index.val :=
  (FullPlacement.ofWires_read _ _ (arithmetic_total ports) Frame.encoding_surjective
    (completeWires ports) (multiplierBit ports index) (ports.multiplier.bit index)
    (completeWires_multiplier ports index) state).trans
      (WordPort.bit_get ports.multiplier index state)

lemma grouping_multiplier (ports : PortAssignment) (state : Frame.Raw) :
    ((layout ports).grouping state).2.1 = ports.multiplier.value state := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  exact ((Accumulate.Square.multiplier (restEncoding ports)).reads
    ((layout ports).grouping state).2 index).symm.trans (multiplier_bit_get ports index state)

def reductionPort (ports : PortAssignment) : EncodedBit (arithmeticEncoding ports) :=
  BinaryLabelEncoding.prodLeftBit ModularAddition.Controlled.selectorEncoding (savedEncoding ports)
    (BinaryLabelEncoding.prodLeftBit ModularAddition.encoding
      ModularAddition.Controlled.flagEncoding ModularAddition.reductionBit)

def loweringPort (ports : PortAssignment) : EncodedBit (arithmeticEncoding ports) :=
  BinaryLabelEncoding.prodLeftBit ModularAddition.Controlled.selectorEncoding (savedEncoding ports)
    ModularAddition.Controlled.controlWorkBit

def arithmeticFlagPort (ports : PortAssignment) (index : Fin 3) :
    EncodedBit (arithmeticEncoding ports) :=
  if index.val = 0 then reductionPort ports
  else if index.val = 1 then Horner.operandLatchBit (savedEncoding ports) else loweringPort ports

private lemma arithmeticFlagPort_wire (ports : PortAssignment) (index : Fin 3) :
    (arithmeticFlagPort ports index).wire.val = 512 + index.val := by
  fin_cases index <;> rfl

private lemma completeWires_flag (ports : PortAssignment) (index : Fin 3) :
    completeWires ports (arithmeticFlagPort ports index).wire = (arithmeticFlag index).wire := by
  have sourceWire : (arithmeticFlagPort ports index).wire =
      (⟨512 + index.val, by
        change 512 + index.val < 515 + (256 + (subsystem ports).complementWidth)
        have within := index.isLt
        omega⟩ : Fin (arithmeticEncoding ports).width) :=
    Fin.ext (arithmeticFlagPort_wire ports index)
  rw [sourceWire]
  change (subsystem ports).completedWires
    (Fin.castAdd (subsystem ports).complementWidth (Fin.castAdd 256 (Fin.natAdd 512 index))) = _
  rw [WireSubsystem.completedWires_source]
  change pickPosition ports (prefixPicks _) = _
  rw [prefixPicks_flag]
  rfl

lemma arithmeticFlagPort_get (ports : PortAssignment) (index : Fin 3) (state : Frame.Raw) :
    (arithmeticFlagPort ports index).get ((layout ports).grouping state) =
      (arithmeticFlag index).get state :=
  FullPlacement.ofWires_read _ _ (arithmetic_total ports) Frame.encoding_surjective
    (completeWires ports) (arithmeticFlagPort ports index) (arithmeticFlag index)
    (completeWires_flag ports index) state

/-- The real caller's clean pool supplies exactly the three arithmetic flags and no extra bits. -/
lemma grouping_flags_clean (ports : PortAssignment) (state : Frame.Raw)
    (clean : Frame.CleanPool state) :
    ((layout ports).grouping state).1.1.2 = false ∧
      ((layout ports).grouping state).1.2.1 = false ∧
        ((layout ports).grouping state).1.2.2 = false := by
  have flags := Frame.arithmetic_flags_clean state clean
  exact ⟨(arithmeticFlagPort_get ports ⟨0, by decide⟩ state).trans flags.1,
    (arithmeticFlagPort_get ports ⟨1, by decide⟩ state).trans flags.2.1,
    (arithmeticFlagPort_get ports ⟨2, by decide⟩ state).trans flags.2.2⟩

private lemma word_before_suffix (port : WordPort) (index : Fin 256) :
    (port.bit index).wire.val < 836 := by
  rw [WordPort.bit_wire]
  have within := index.isLt
  cases port <;> simp only [WordPort.physicalIndex] <;> omega

private lemma flag_before_suffix (index : Fin 3) :
    (arithmeticFlag index).wire.val < 836 := by
  rw [arithmeticFlag_wire]
  unfold arithmeticFlagIndex
  split_ifs <;> omega

private lemma subsystem_before_suffix (ports : PortAssignment)
    (index : Fin prefixEncoding.width) : ((subsystem ports).wires index).val < 836 := by
  change (pickPosition ports (prefixPicks index)).val < 836
  rcases prefixPicks index with ((source | target) | flag) | multiplier
  · exact word_before_suffix ports.source source.rev
  · exact word_before_suffix ports.target target.rev
  · exact flag_before_suffix flag
  · exact word_before_suffix ports.multiplier multiplier.rev

/-- Every original point suffix wire is outside all selected arithmetic word and pool ports. -/
lemma suffix_outside (ports : PortAssignment) (bit : EncodedBit Frame.encoding)
    (afterOriginal : 836 ≤ bit.wire.val) : bit.wire ∉ Set.range (subsystem ports).wires := by
  rintro ⟨index, same⟩
  have within := subsystem_before_suffix ports index
  have positions := congrArg Fin.val same
  omega

/-- A retained coordinate denotes precisely its original existing physical complement position. -/
def restBit (ports : PortAssignment) (bit : EncodedBit Frame.encoding)
    (outside : bit.wire ∉ Set.range (subsystem ports).wires) :
    EncodedBit (restEncoding ports) :=
  BinaryLabelEncoding.finIdentityBit (subsystem ports).complementWidth
    (complementIndex (subsystem ports) ⟨bit.wire, outside⟩)

private lemma completeWires_rest (ports : PortAssignment) (bit : EncodedBit Frame.encoding)
    (outside : bit.wire ∉ Set.range (subsystem ports).wires) :
    completeWires ports
      (Horner.operandSavedBit (savedEncoding ports)
        (Accumulate.Square.outerBit (restEncoding ports) (restBit ports bit outside))).wire =
      bit.wire := by
  refine (completeWires_apply ports _
    (Fin.natAdd prefixEncoding.width
      (complementIndex (subsystem ports) ⟨bit.wire, outside⟩)) ?_).trans
        (completed_complementIndex (subsystem ports) ⟨bit.wire, outside⟩)
  change 515 + (256 + (complementIndex (subsystem ports) ⟨bit.wire, outside⟩).val) =
    771 + (complementIndex (subsystem ports) ⟨bit.wire, outside⟩).val
  omega

lemma restBit_get (ports : PortAssignment) (bit : EncodedBit Frame.encoding)
    (outside : bit.wire ∉ Set.range (subsystem ports).wires) (state : Frame.Raw) :
    (restBit ports bit outside).get ((layout ports).grouping state).2.2 = bit.get state :=
  FullPlacement.ofWires_read _ _ (arithmetic_total ports) Frame.encoding_surjective
    (completeWires ports)
    (Horner.operandSavedBit (savedEncoding ports)
      (Accumulate.Square.outerBit (restEncoding ports) (restBit ports bit outside)))
    bit (completeWires_rest ports bit outside) state

def savedPointControl (ports : PortAssignment) : EncodedBit (restEncoding ports) :=
  restBit ports Frame.pointControlBit
    (suffix_outside ports Frame.pointControlBit (Frame.pointControlBit_wire.ge))

def savedNormal (ports : PortAssignment) : EncodedBit (restEncoding ports) :=
  restBit ports Frame.normalBit
    (suffix_outside ports Frame.normalBit (by rw [Frame.normalBit_wire]; decide))

def savedFusionWork (ports : PortAssignment) : EncodedBit (restEncoding ports) :=
  restBit ports Frame.workBit
    (suffix_outside ports Frame.workBit (by rw [Frame.workBit_wire]; decide))

lemma savedPointControl_get (ports : PortAssignment) (state : Frame.Raw) :
    (savedPointControl ports).get ((layout ports).grouping state).2.2 = state.2.1 :=
  (restBit_get ports Frame.pointControlBit _ state).trans (Frame.pointControlBit_get state)

lemma savedNormal_get (ports : PortAssignment) (state : Frame.Raw) :
    (savedNormal ports).get ((layout ports).grouping state).2.2 = state.2.2.1 :=
  (restBit_get ports Frame.normalBit _ state).trans (Frame.normalBit_get state)

lemma savedFusionWork_get (ports : PortAssignment) (state : Frame.Raw) :
    (savedFusionWork ports).get ((layout ports).grouping state).2.2 = state.2.2.2 :=
  (restBit_get ports Frame.workBit _ state).trans (Frame.workBit_get state)

/-- The physical original frame contains exactly all 839 placed arithmetic and saved systems. -/
lemma arithmeticEncoding_width (ports : PortAssignment) :
    (arithmeticEncoding ports).width = 839 := by
  change 515 + (256 + (subsystem ports).complementWidth) = 839
  rw [complement_width]

end Placement

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point
