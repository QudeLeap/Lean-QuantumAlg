/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Rotation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Frame
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Program

/-!
# Native per-index gates of a streamed TTK template

The source and target remain the original Work2 and Work1 systems. Every
gate is placed at its literal little-endian arithmetic index. Stage masks
are static template choices; the actual quantum window boundary is supplied
by the streamed selector. The ascending inverse-pair for stage four becomes
the original descending CNOT-before-Toffoli block under a real unitary
dagger [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

variable {width : Nat}

/-- Six source stages, retaining the two opposite traversals of the xor chain. -/
inductive Stage where
  | preXor
  | descendingXor
  | carry
  | descendingUncompute
  | ascendingXor
  | finalXor

private def littleIndex (width : Nat) (index : Fin (width + 3)) : Fin (width + 3) :=
  ⟨width + 3 - 1 - index.val, by have := index.isLt; omega⟩

/-- Work2 is the original arithmetic addend; Work1 is its original target. -/
def wordBit (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    EncodedBit (encoding width) := ArithmeticRotation.bit width first (littleIndex width index)

private lemma wordBit_value (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (wordBit width first index).wire.val =
      (if first then 0 else width + 3) + (width + 3 - 1 - index.val) :=
  ArithmeticRotation.bit_value width first _

private lemma wordBit_below (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (wordBit width first index).wire.val < 2 * (width + 3) := by
  rw [wordBit_value]
  have := index.isLt
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

private lemma word_ne (width : Nat) (left right : Fin (width + 3)) :
    (wordBit width true left).wire ≠ (wordBit width false right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [wordBit_value, wordBit_value] at values
  have := left.isLt
  have := right.isLt
  simp only [Bool.false_eq_true, if_false, if_true] at values
  omega

private lemma word_distinct (width : Nat) (first : Bool)
    (left right : Fin (width + 3)) (different : left ≠ right) :
    (wordBit width first left).wire ≠ (wordBit width first right).wire := by
  intro same
  apply different
  apply Fin.ext
  have values := congrArg Fin.val same
  rw [wordBit_value, wordBit_value] at values
  have := left.isLt
  have := right.isLt
  omega

private def below (cutoff : Nat) : GateSpec (encoding width) → Prop
  | .x target => target.wire.val < cutoff
  | .cnot control target _ => control.wire.val < cutoff ∧ target.wire.val < cutoff
  | .toffoli first second target _ _ _ =>
      first.wire.val < cutoff ∧ second.wire.val < cutoff ∧ target.wire.val < cutoff

private abbrev Native (width : Nat) :=
  {gate : GateSpec (encoding width) // below (2 * (width + 3)) gate}

private def sumGate (width : Nat) (index : Fin (width + 3)) : Native width :=
  ⟨.cnot (wordBit width false index) (wordBit width true index)
    (word_ne width index index).symm,
      wordBit_below width false index, wordBit_below width true index⟩

private def previous (width : Nat) (index : Fin (width + 3)) : Fin (width + 3) :=
  ⟨index.val - 1, by have := index.isLt; omega⟩

private lemma previous_ne (width : Nat) (index : Fin (width + 3)) (positive : 0 < index.val) :
    previous width index ≠ index := by
  intro same
  have values := congrArg Fin.val same
  change index.val - 1 = index.val at values
  omega

private def chainGate (width : Nat) (index : Fin (width + 3))
    (positive : 0 < index.val) : Native width :=
  ⟨.cnot (wordBit width false (previous width index)) (wordBit width false index)
    (word_distinct width false _ _ (previous_ne width index positive)),
      wordBit_below width false _, wordBit_below width false index⟩

private def carryGate (width : Nat) (index : Fin (width + 3))
    (positive : 0 < index.val) : Native width :=
  ⟨.toffoli (wordBit width true (previous width index))
      (wordBit width false (previous width index)) (wordBit width false index)
      (word_ne width _ _) (word_ne width _ _)
      (word_distinct width false _ _ (previous_ne width index positive)),
    wordBit_below width true _, wordBit_below width false _, wordBit_below width false index⟩

private def nativeWords (width : Nat) (stage : Stage) (index : Nat) : List (Native width) :=
  if within : index < width + 3 then
    let current : Fin (width + 3) := ⟨index, within⟩
    match stage with
    | .preXor => if 0 < index then [sumGate width current] else []
    | .descendingXor | .ascendingXor =>
        if internal : 2 ≤ index then
          [chainGate width current (by change 0 < index; omega)] else []
    | .carry => if positive : 0 < index then [carryGate width current positive] else []
    | .descendingUncompute => if positive : 0 < index then
        [carryGate width current positive, sumGate width current] else []
    | .finalXor => [sumGate width current]
  else []

/-- Literal source-native gate word for one public template index. -/
def source (width : Nat) (stage : Stage) (index : Nat) : List (GateSpec (encoding width)) :=
  (nativeWords width stage index).map Subtype.val

private lemma source_below (width : Nat) (stage : Stage) (index : Nat)
    (gate : GateSpec (encoding width)) (present : gate ∈ source width stage index) :
    below (2 * (width + 3)) gate := by
  obtain ⟨value, _, same⟩ := List.mem_map.mp present
  exact same ▸ value.property

private lemma wire_ne_of_below {cutoff : Nat} (first second : EncodedBit (encoding width))
    (firstBelow : first.wire.val < cutoff) (secondAbove : cutoff ≤ second.wire.val) :
    first.wire ≠ second.wire := by
  intro same
  have values := congrArg Fin.val same
  omega

private lemma below_disjoint {cutoff : Nat} (gate : GateSpec (encoding width))
    (supported : below cutoff gate) (observed : EncodedBit (encoding width))
    (outside : cutoff ≤ observed.wire.val) : GateSpec.bitDisjoint observed gate := by
  cases gate with
  | x target => exact wire_ne_of_below _ _ supported outside
  | cnot control target _ =>
      exact ⟨wire_ne_of_below _ _ supported.1 outside,
        wire_ne_of_below _ _ supported.2 outside⟩
  | toffoli first second target _ _ _ =>
      exact ⟨wire_ne_of_below _ _ supported.1 outside,
        wire_ne_of_below _ _ supported.2.1 outside,
        wire_ne_of_below _ _ supported.2.2 outside⟩

/-- The existing arbitrary Iter wire supplies restored dirty work for the moving active bit. -/
def payload (width : Nat) (stage : Stage) (index : Nat) :
    StreamedSelector.ControlledPayload (encoding width) where
  active := conjunctionBit width
  work := sourceBit width (SharedEEA.iterationBit width)
  source := source width stage index
  activeDisjoint := by
    intro gate present
    apply below_disjoint gate (source_below width stage index gate present)
    rw [conjunctionBit_wire, SharedEEA.encoding_width]
    omega
  workDisjoint := by
    intro gate present
    apply below_disjoint gate (source_below width stage index gate present)
    rw [sourceBit_wire, SharedEEA.iterationBit_wire]
    omega
  activeWork := (source_conjunction_ne width (SharedEEA.iterationBit width)).symm

private lemma stack_above (width : Nat) (index : Fin (ScanMetadata.addressWidth width + 1)) :
    2 * (width + 3) ≤ ((SelectionFrame.frame width).stack index).wire.val := by
  change 2 * (width + 3) ≤ (SelectionFrame.stack width index).wire.val
  unfold SelectionFrame.stack
  split
  · change 2 * (width + 3) ≤ (sourceBit width (SharedEEA.controlBit width)).wire.val
    rw [sourceBit_wire, SharedEEA.controlBit_wire]
    omega
  · rw [prefixBit_wire, SharedEEA.encoding_width]
    omega

/-- The complete template protects the actual address, Ctrl and every live prefix bit. -/
def family (width : Nat) (stage : Stage) :
    StreamedSelector.PayloadFamily (SelectionFrame.frame width) where
  payload label := payload width stage label.val
  activeAddress := by
    intro label index
    exact (address_conjunction_ne width index).symm
  activeStack := by
    intro label index
    change (conjunctionBit width).wire ≠ (SelectionFrame.stack width index).wire
    unfold SelectionFrame.stack
    split
    · exact (source_conjunction_ne width (SharedEEA.controlBit width)).symm
    · exact (prefix_conjunction_ne width _).symm
  sourceAddress := by
    intro label index gate present
    apply below_disjoint gate (source_below width stage label.val gate present)
    change 2 * (width + 3) ≤ (addressBit width index).wire.val
    rw [addressBit_wire, SharedEEA.encoding_width]
    omega
  sourceStack := by
    intro label index gate present
    exact below_disjoint gate (source_below width stage label.val gate present) _
      (stack_above width index)

/-- Only actual original work-word indices retain native template callbacks. -/
def tree (width : Nat) : WindowLookup.SelectorTrie (ScanMetadata.addressWidth width) :=
  WindowLookup.SelectorTrie.prune (ScanMetadata.addressWidth width)
    (fun label => decide (label.val < width + 3))

/-- Actual forward native traversal; descending source stages use its real unitary dagger. -/
def program (width : Nat) (stage : Stage) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (family width stage).program (QubitLayout.canonical _) .empty (tree width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
