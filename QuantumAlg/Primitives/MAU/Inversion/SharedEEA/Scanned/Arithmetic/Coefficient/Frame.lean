/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.WireBit
import all QuantumAlg.Components.Encoded.BitGates.BitEquality
import all QuantumAlg.Util.Permutation.PrefixReflection

/-!
# Static coefficient placement of the same native arithmetic templates

Original remainder little-endian Work2/Work1 positions map directly to
coefficient little-endian Work1/Work2 positions. Every metadata, phase,
address and prefix position stays fixed. This is the declared wire map
of the emitted native gates, with no executed word reversal or swap
[LYL+26, sec_EEA/sub_regshare.tex:17,20,263-264,291-294].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientFrame

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma operands_fit (width : Nat) : 2 * (width + 3) ≤ (encoding width).width := by
  rw [Scanned.encoding_width]
  omega

/-- A public static bijection of complete physical positions, retaining all non-operand systems. -/
def wires (width : Nat) : Equiv.Perm (Fin (encoding width).width) :=
  Permutation.prefixReflection (encoding width).width (2 * (width + 3)) (operands_fit width)

/-- The same original little-endian source and target bits occupy their coefficient positions. -/
lemma wires_wordBit (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    wires width (ArithmeticTemplate.wordBit width first index).wire =
      (ArithmeticRotation.bit width (!first) index).wire := by
  apply Fin.ext
  rw [wires, Permutation.prefixReflection_value,
    if_pos (ArithmeticTemplate.wordBit_below width first index),
    ArithmeticTemplate.wordBit_value, ArithmeticRotation.bit_value]
  have within := index.isLt
  cases first <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] <;> omega

/-- Every original metadata, phase, address and workspace coordinate stays exactly where it was. -/
lemma wires_retained (width : Nat) (index : Fin (encoding width).width)
    (outside : 2 * (width + 3) ≤ index.val) : wires width index = index :=
  Permutation.prefixReflection_outside _ _ _ index outside

/-- Complete semantic grouping and actual native gate placement come from the same physical map. -/
def placement (width : Nat) : FullPlacement (encoding width) (encoding width) :=
  FullPlacement.ofWires (encoding width) (encoding width)
    (Scanned.encoding_surjective width) (Scanned.encoding_surjective width) (wires width)

/-- Every literal template operand lens is the original coefficient operand lens on that wire. -/
lemma placed_wordBit (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (placement width).placeBit (ArithmeticTemplate.wordBit width first index) =
      ArithmeticRotation.bit width (!first) index := by
  apply EncodedBit.eq_of_wire_eq
  exact (FullPlacement.ofWires_placeBit_wire (encoding width) (encoding width)
    (Scanned.encoding_surjective width) (Scanned.encoding_surjective width)
    (wires width) (ArithmeticTemplate.wordBit width first index)).trans
    (wires_wordBit width first index)

/-- Placing any actual native template retains its complete original ordered event trace. -/
lemma place_eventTrace (width : Nat) (body : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum) :
    ((placement width).place body).eventTrace = body.eventTrace :=
  (placement width).place_eventTrace body

/-- The same actual dependency construction retains its quantum duration under static placement. -/
lemma place_quantumTime (width : Nat) (body : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum) :
    ((placement width).place body).evaluatedEventDepth Resource.Event.quantumDuration =
      body.evaluatedEventDepth Resource.Event.quantumDuration :=
  (placement width).place_evaluatedEventDepth body _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientFrame
