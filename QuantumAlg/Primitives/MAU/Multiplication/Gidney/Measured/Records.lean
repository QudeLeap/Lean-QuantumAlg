/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Records
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Coherent
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Append

/-!
# Actual multiplier outcome cardinality and common scalar from both chronological MACs

The intervening actual native exchange contributes no physical measurement
outcome. The forward and explicit inverse words keep their distinct
chronological outcomes even when they overwrite the same record cells
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum}

/-- Exactly the binary vents selected by both actual static source-order MAC banks. -/
def multiplicationVents (modulus : BitVec width) (coefficient inverseCoefficient : Nat) : Nat :=
  accumulatePrefixVents (forwardConstant modulus coefficient) width le_rfl +
    accumulatePrefixVents (inverseConstant modulus inverseCoefficient) width le_rfl

/-- The actual multiplier common scalar is exactly the inverse-square-root power of its vents. -/
lemma multiplication_commonAlpha_eq_power (modulus : BitVec width)
    (coefficient inverseCoefficient : Nat) :
    accumulatePrefixAlpha (forwardConstant modulus coefficient) width le_rfl *
        accumulatePrefixAlpha (inverseConstant modulus inverseCoefficient) width le_rfl =
      NormalizedVector.invSqrt2 ^ multiplicationVents modulus coefficient inverseCoefficient := by
  rw [accumulatePrefixAlpha_eq_power, accumulatePrefixAlpha_eq_power, multiplicationVents, pow_add]

private lemma actualOutcomes_card_append (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (first second : List (Instruction encoding (width - 2))) :
    Fintype.card (WordOutcomes physical sameWires (first ++ second)) =
      Fintype.card (WordOutcomes physical sameWires first) *
        Fintype.card (WordOutcomes physical sameWires second) := by
  rw [← Fintype.card_congr (appendOutcomesEquiv physical sameWires first second), Fintype.card_prod]

private lemma actualOutcomes_card_native (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (gates : List (EncodedBit.GateSpec encoding)) :
    Fintype.card (WordOutcomes (records := width - 2) physical sameWires [.native gates]) = 1 := by
  change Fintype.card (Unit × Unit) = 1
  simp only [Fintype.card_prod, Fintype.card_unit, Nat.mul_one]

/-- All actual multiplier outcome words have exactly one binary factor per actual emitted vent. -/
lemma multiplicationWord_outcomes_card (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    Fintype.card (WordOutcomes physical sameWires
      (layout.multiplicationWord wide modulus coefficient inverseCoefficient)) =
        2 ^ multiplicationVents modulus coefficient inverseCoefficient := by
  rw [multiplicationWord, actualOutcomes_card_append, actualOutcomes_card_append,
    actualOutcomes_card_native, Nat.mul_one]
  change Fintype.card (WordOutcomes physical sameWires
      (layout.accumulatePrefixWord wide modulus (forwardConstant modulus coefficient)
        width le_rfl)) *
    Fintype.card (WordOutcomes physical sameWires
      (layout.accumulatePrefixWord wide modulus (inverseConstant modulus inverseCoefficient)
        width le_rfl)) = _
  rw [accumulatePrefixWord_outcomes_card, accumulatePrefixWord_outcomes_card,
    multiplicationVents, pow_add]

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
