/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Gates
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates.Equations
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag.Gates
import all QuantumAlg.Primitives.MAU.Addition.TTK.Overflow

/-!
# The original signed TTK window with its existing overflow output

The declared operand subsystem extends by the original arbitrary Sign
bit. Every operand and output retains its actual physical position;
the complete complement includes the address and shared pool. The
native top gates agree with the original TTK overflow instructions
[TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTop

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma subsystem_sign_ne (width length : Nat) (fits : length ≤ width + 3)
    (index : Fin (Addition.TTK.encoding length).width) :
    (ArithmeticWindow.placement width length fits).subsystem.wires index ≠
      (sign width).wire := by
  refine Fin.addCases (fun left => ?_) (fun right => ?_) index
  · change (wordPairSubsystem _ _ _ _ _).wires (Fin.castAdd length left) ≠ _
    rw [wordPairSubsystem_left]
    exact word_sign_ne width false _
  · change (wordPairSubsystem _ _ _ _ _).wires (Fin.natAdd length right) ≠ _
    rw [wordPairSubsystem_right]
    exact word_sign_ne width true _

private lemma overflow_onto (length : Nat) :
    Function.Surjective (Addition.TTK.overflowEncoding length).encode :=
  Scanned.product_total _ _ (ArithmeticWindow.source_onto length) Scanned.bool_total

/-- The same actual ordered operand words beside the existing arbitrary Sign output. -/
def placement (width length : Nat) (fits : length ≤ width + 3) :
    WireSubsystem (Addition.TTK.overflowEncoding length) (Scanned.encoding width) :=
  (ArithmeticWindow.placement width length fits).subsystem.withFlag (sign width)
    (subsystem_sign_ne width length fits)

/-- The lifted original operand lens has exactly its previous physical placement. -/
lemma placed_operand (width length : Nat) (fits : length ≤ width + 3)
    (bit : EncodedBit (Addition.TTK.encoding length)) :
    (placement width length fits).placeBit (overflow_onto length)
      (Scanned.encoding_surjective width) (Addition.TTK.withOverflowBit bit) =
      (ArithmeticWindow.placement width length fits).subsystem.placeBit
        (ArithmeticWindow.source_onto length) (Scanned.encoding_surjective width) bit :=
  WireSubsystem.withFlag_place_source _ (sign width) (subsystem_sign_ne width length fits)
    (ArithmeticWindow.source_onto length) (overflow_onto length)
    (Scanned.encoding_surjective width) bit

/-- The original source output flag is the same actual arbitrary Sign bit. -/
lemma placed_sign (width length : Nat) (fits : length ≤ width + 3) :
    (placement width length fits).placeBit (overflow_onto length)
      (Scanned.encoding_surjective width) (Addition.TTK.overflowBit length) = sign width :=
  WireSubsystem.withFlag_place_flag _ (sign width) (subsystem_sign_ne width length fits)
    (overflow_onto length) (Scanned.encoding_surjective width)

/-- Relocate each literal signed source instruction to the original complete physical frame. -/
def mapGate (width length : Nat) (fits : length ≤ width + 3)
    (gate : GateSpec (Addition.TTK.overflowEncoding length)) :
    GateSpec (Scanned.encoding width) :=
  (placement width length fits).placeGate (overflow_onto length)
    (Scanned.encoding_surjective width) gate

/-- Lifting an operand primitive to Sign and then placing it keeps its original native gate. -/
lemma map_lifted (width length : Nat) (fits : length ≤ width + 3)
    (gate : GateSpec (Addition.TTK.encoding length)) :
    mapGate width length fits (Addition.TTK.withOverflowGate gate) =
      ArithmeticWindow.mapGate width length fits gate := by
  have lifted : Addition.TTK.withOverflowGate gate = WireSubsystem.withFlagGate gate := by
    cases gate <;> rfl
  rw [lifted]
  exact WireSubsystem.withFlag_placeGate _ (sign width) (subsystem_sign_ne width length fits)
    (ArithmeticWindow.source_onto length) (overflow_onto length)
    (Scanned.encoding_surjective width) gate

/-- The selected pre-overflow CNOT is the literal source instruction at its top index. -/
lemma map_preGate (width last : Nat) (fits : last + 1 ≤ width + 3) :
    mapGate width (last + 1) fits (Addition.TTK.overflowPreGate last) =
      preGate width ⟨last, by omega⟩ := by
  rw [mapGate, Addition.TTK.overflowPreGate, WireSubsystem.placeGate_cnot]
  congr 1
  · exact (placed_operand width (last + 1) fits _).trans
      (ArithmeticWindow.placed_leftBit width (last + 1) fits ⟨last, by omega⟩)
  · exact placed_sign width (last + 1) fits

/-- The selected carry Toffoli has the source's same ordered controls and original Sign output. -/
lemma map_carryGate (width last : Nat) (fits : last + 1 ≤ width + 3) :
    mapGate width (last + 1) fits (Addition.TTK.overflowCarryGate last) =
      carryGate width ⟨last, by omega⟩ := by
  rw [mapGate, Addition.TTK.overflowCarryGate, WireSubsystem.placeGate_toffoli]
  congr 1
  · exact (placed_operand width (last + 1) fits _).trans
      (ArithmeticWindow.placed_rightBit width (last + 1) fits ⟨last, by omega⟩)
  · exact (placed_operand width (last + 1) fits _).trans
      (ArithmeticWindow.placed_leftBit width (last + 1) fits ⟨last, by omega⟩)
  · exact placed_sign width (last + 1) fits

/-- The independent signed addition acts on the selected words and leaves the full complement. -/
def windowStep (width length : Nat) (fits : length ≤ width + 3) (state : Data width) :
    Data width :=
  ((placement width length fits).full (overflow_onto length)
    (Scanned.encoding_surjective width)).step
      (fun pair => (Addition.TTK.overflowOutput pair.1, pair.2)) state

/-- The exact original native overflow word has the complete signed arithmetic action. -/
lemma mapped_overflow_step (width length : Nat) (fits : length ≤ width + 3)
    (state : Data width) :
    GateSpec.stepList ((Addition.TTK.overflowGates length).map (mapGate width length fits))
      state = windowStep width length fits state := by
  have actual := (placement width length fits).placeGates_step (overflow_onto length)
    (Scanned.encoding_surjective width) (Addition.TTK.overflowGates length) state
  simp only [Addition.TTK.ttkOverflow_step] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTop
