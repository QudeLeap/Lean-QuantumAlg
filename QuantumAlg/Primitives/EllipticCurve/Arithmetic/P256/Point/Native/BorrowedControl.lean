/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native

/-!
# Actual arithmetic controlled by the existing pool address system at 560

The three arithmetic flags remain 559/569/579. This fourth existing pool
position belongs to the complete retained complement, so it may store the
whole-digit enable during arithmetic. Full-pool EEA and QROM callers must
separately restore it to zero. No wire is allocated or treated as free work.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

namespace BorrowedControl

noncomputable section

open QuantumAlg.EncodedBit

/-- The original second scan-address system, physically distinct from the arithmetic flags. -/
def flag : EncodedBit Frame.encoding :=
  Frame.scanBit (MAU.Inversion.SharedEEA.Scanned.addressBit 256 ⟨1, by decide⟩)

lemma flag_wire : flag.wire.val = 560 := by
  rw [flag, Frame.scanBit_wire, MAU.Inversion.SharedEEA.Scanned.addressBit_wire]
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

private lemma word_ne (port : WordPort) (index : Fin 256) :
    (port.bit index).wire.val ≠ 560 := by
  rw [WordPort.bit_wire]
  have within := index.isLt
  cases port <;> simp only [WordPort.physicalIndex] <;> omega

private lemma arithmeticFlag_ne (index : Fin 3) : (arithmeticFlag index).wire.val ≠ 560 := by
  rw [arithmeticFlag_wire]
  unfold arithmeticFlagIndex
  split_ifs <;> omega

/-- F560 is part of the actual complete complement for every valid original port assignment. -/
lemma outside (ports : PortAssignment) :
    flag.wire ∉ Set.range (Placement.subsystem ports).wires := by
  rintro ⟨index, same⟩
  have positions := congrArg Fin.val same
  rw [flag_wire] at positions
  change (Placement.pickPosition ports (Placement.prefixPicks index)).val = 560 at positions
  generalize Placement.prefixPicks index = selected at positions
  rcases selected with ((source | target) | arithmetic) | multiplier
  · exact word_ne ports.source source.rev positions
  · exact word_ne ports.target target.rev positions
  · exact arithmeticFlag_ne arithmetic positions
  · exact word_ne ports.multiplier multiplier.rev positions

/-- Read that same original physical system from the retained arithmetic complement. -/
def controlBit (ports : PortAssignment) : EncodedBit (Placement.restEncoding ports) :=
  Placement.restBit ports flag (outside ports)

lemma controlBit_get (ports : PortAssignment) (state : Frame.Raw) :
    (controlBit ports).get ((Placement.layout ports).grouping state).2.2 = flag.get state :=
  Placement.restBit_get ports flag (outside ports) state

def outerBit (ports : PortAssignment) : EncodedBit (Placement.savedEncoding ports) :=
  Accumulate.Square.outerBit (Placement.restEncoding ports) (controlBit ports)

private lemma outer_source_ne (ports : PortAssignment) (index : Fin width) :
    (Horner.operandSavedBit (Placement.savedEncoding ports) (outerBit ports)).wire ≠
      (Horner.operandSourceBit (Placement.savedEncoding ports) index).wire :=
  GateSpec.prodRightBit_wire_ne_prodLeftBit_wire ModularAddition.Controlled.selectorEncoding
    (Placement.savedEncoding ports) (outerBit ports)
    (BinaryLabelEncoding.prodLeftBit ModularAddition.encoding
      ModularAddition.Controlled.flagEncoding (ModularAddition.addendBit index))

lemma outer_multiplier_ne (ports : PortAssignment) (choice : Multiplier) (index : Fin width) :
    (Horner.operandSavedBit (Placement.savedEncoding ports) (outerBit ports)).wire ≠
      (Horner.operandMultiplierBit (Placement.savedEncoding ports)
        ((quantumMultiplier ports choice).ports index)).wire := by
  cases choice with
  | source => exact outer_source_ne ports index
  | retained =>
      exact Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports) index

/-- Actual original clean-target Horner tree with the supplied existing F560 control. -/
def cleanProgram (ports : PortAssignment) (choice : Multiplier) : Circuit :=
  (Placement.layout ports).place
    (Horner.cleanProgram (Placement.savedEncoding ports) (quantumMultiplier ports choice)
      (outerBit ports) (outer_multiplier_ne ports choice))

/-- Actual arbitrary-accumulator MAC with the original F560 control. -/
def macProgram (ports : PortAssignment) : Circuit :=
  (Placement.layout ports).place
    (Accumulate.program (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding ports) (controlBit ports)))

def inverseMacProgram (ports : PortAssignment) : Circuit :=
  (Placement.layout ports).place
    (Accumulate.Inverse.program (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding ports) (controlBit ports)))

/-- Both original Y-to-A copy words and the complete inverse square MAC remain actual programs. -/
def subtractSquareProgram : Circuit :=
  (Placement.layout squarePorts).place
    (Accumulate.Square.program (Placement.restEncoding squarePorts) (controlBit squarePorts))

end

end BorrowedControl

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
