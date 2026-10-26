/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout.Readout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Frame
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import Mathlib.Tactic.FinCases

/-!
# Complete original source retention through an actual selected modular-addition row

The active selector is retained as a control. Every borrowed dirty source
bit is restored by the full row, and the unused original source bit is
retained by its actual outside-wire law. These cases cover the complete
source word, including arbitrary joint source/reference amplitudes
[G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every original source readout is restored by the selected row's full physical frame law. -/
lemma reductionFrame_source_get (layout : Layout encoding width) (selector : Fin width)
    (initial current : Data)
    (invariant : (layout.reductionLayout selector).FrameInvariant initial current)
    (observed : Fin width) :
    (layout.source observed).get current = (layout.source observed).get initial := by
  by_cases selected : observed = selector
  · subst observed
    exact invariant.active 1
  · by_cases borrowed : ∃ index, dirtySourceIndex selector index = observed
    · obtain ⟨index, same⟩ := borrowed
      rw [← same]
      exact invariant.dirty index
    · have outside : ∀ port, ((layout.reductionLayout selector).bit port).wire ≠
          (layout.source observed).wire := by
        intro port
        rcases port with active | target | dirty | helper | flag
        · fin_cases active
          · change layout.control.wire ≠ (layout.source observed).wire
            exact layout.wire_ne (by intro impossible; cases impossible)
          · change (layout.source selector).wire ≠ (layout.source observed).wire
            apply layout.wire_ne
            intro same
            exact selected (Sum.inl.inj (Sum.inr.inj same)).symm
        · change (layout.target target).wire ≠ (layout.source observed).wire
          exact layout.wire_ne (by intro impossible; cases impossible)
        · change (layout.source (dirtySourceIndex selector dirty)).wire ≠
            (layout.source observed).wire
          apply layout.wire_ne
          intro same
          exact borrowed ⟨dirty, Sum.inl.inj (Sum.inr.inj same)⟩
        · change (layout.clean helper).wire ≠ (layout.source observed).wire
          exact layout.wire_ne (by intro impossible; cases impossible)
        · cases flag
          change layout.flag.wire ≠ (layout.source observed).wire
          exact layout.wire_ne (by intro impossible; cases impossible)
      have actual := invariant.outside (layout.source observed).wire outside
      exact ((layout.source observed).get_eq current).symm.trans
        (actual.trans ((layout.source observed).get_eq initial))

/-- The original complete source word is retained jointly by the actual selected modular row. -/
lemma reductionFrame_sourceWord (layout : Layout encoding width) (selector : Fin width)
    (initial current : Data)
    (invariant : (layout.reductionLayout selector).FrameInvariant initial current) :
    layout.sourceWord current = layout.sourceWord initial := by
  unfold sourceWord
  congr 1
  funext observed
  exact reductionFrame_source_get layout selector initial current invariant observed

/-- The original global multiplication control is retained by the selected row's actual frame. -/
lemma reductionFrame_control (layout : Layout encoding width) (selector : Fin width)
    (initial current : Data)
    (invariant : (layout.reductionLayout selector).FrameInvariant initial current) :
    layout.control.get current = layout.control.get initial :=
  invariant.active 0

/-- Each original modular-row address belongs to the same original multiplication frame. -/
lemma reductionLayout_bit_in_frame (layout : Layout encoding width) (selector : Fin width)
    (port : Addition.Gidney.Measured.Reduction.Port width) :
    ∃ original : Port width, (layout.reductionLayout selector).bit port = layout.bit original := by
  rcases port with active | target | dirty | helper | flag
  · fin_cases active
    · exact ⟨.inl (), rfl⟩
    · exact ⟨.inr (.inl selector), rfl⟩
  · exact ⟨.inr (.inr (.inl target)), rfl⟩
  · exact ⟨.inr (.inl (dirtySourceIndex selector dirty)), rfl⟩
  · exact ⟨.inr (.inr (.inr (.inl helper))), rfl⟩
  · exact ⟨.inr (.inr (.inr (.inr flag))), rfl⟩

/-- Every encoded wire outside the multiplication frame is retained by the actual selected row. -/
lemma reductionFrame_outside (layout : Layout encoding width) (selector : Fin width)
    (initial current : Data)
    (invariant : (layout.reductionLayout selector).FrameInvariant initial current)
    (observed : Fin encoding.width) (outside : ∀ port, (layout.bit port).wire ≠ observed) :
    (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val =
      (encoding.encode initial).val.testBit (WireAddress.bitIndex observed).val := by
  apply invariant.outside observed
  intro port
  obtain ⟨original, same⟩ := reductionLayout_bit_in_frame layout selector port
  rw [same]
  exact outside original

/-- The original complete multiplication frame outside its target and reduction flag. -/
structure FrameInvariant (layout : Layout encoding width) (initial current : Data) : Prop where
  clean : ∀ helper, (layout.clean helper).get current = false
  control : layout.control.get current = layout.control.get initial
  source : layout.sourceWord current = layout.sourceWord initial
  outside : ∀ observed : Fin encoding.width,
    (∀ port, (layout.bit port).wire ≠ observed) →
    (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val =
      (encoding.encode initial).val.testBit (WireAddress.bitIndex observed).val

/-- Clean original helpers initialize the frame without restricting the source or other wires. -/
lemma multiplication_frame_initial (layout : Layout encoding width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial initial where
  clean := clean
  control := rfl
  source := rfl
  outside := fun _ _ => rfl

/-- Two actual chronological frame restorations retain the same original source and wires. -/
lemma multiplication_frame_trans {layout : Layout encoding width} {initial middle final : Data}
    (first : layout.FrameInvariant initial middle)
    (second : layout.FrameInvariant middle final) : layout.FrameInvariant initial final where
  clean := second.clean
  control := second.control.trans first.control
  source := second.source.trans first.source
  outside := fun observed outside =>
    (second.outside observed outside).trans (first.outside observed outside)

/-- The complete actual selected measured row restores the complete multiplication frame. -/
lemma modularRow_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (selector : Fin width) (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial
      (Addition.Gidney.Measured.Instruction.wordLabel
        ((layout.reductionLayout selector).modularWord wide modulus constant) initial) := by
  have actual := Addition.Gidney.Measured.Reduction.Layout.modularWord_frame
    (layout.reductionLayout selector) wide modulus constant initial clean
  exact {
    clean := actual.clean
    control := reductionFrame_control layout selector _ _ actual
    source := reductionFrame_sourceWord layout selector _ _ actual
    outside := reductionFrame_outside layout selector _ _ actual }

/-- Every literal prefix restores all original source bits, both helpers and all outside wires. -/
lemma accumulatePrefixWord_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) (count : Nat)
    (bounded : count ≤ width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial
      (Addition.Gidney.Measured.Instruction.wordLabel
        (layout.accumulatePrefixWord wide modulus constants count bounded) initial) := by
  induction count with
  | zero => exact multiplication_frame_initial layout initial clean
  | succ count ih =>
      rw [accumulatePrefixWord, Addition.Gidney.Measured.Instruction.wordLabel_append]
      have earlier := ih (by omega)
      exact multiplication_frame_trans earlier
        (modularRow_frame layout wide ⟨count, by omega⟩ modulus _ _ earlier.clean)

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
