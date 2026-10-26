/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Coherent
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Records.Finite
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Append
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record

/-!
# Exact chronological outcome count and common scalar of the actual MAC

Every nonzero static row executes its own two vent passes. Zero rows emit
literal identity. Reusing the same physical record cells keeps distinct
chronological outcomes and their full actual path [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum}

/-- Actual binary vent multiplicity selected solely by the emitted static constant bank. -/
def accumulatePrefixVents (constants : Fin width → BitVec width) :
    (count : Nat) → count ≤ width → Nat
  | 0, _ => 0
  | count + 1, bounded =>
      accumulatePrefixVents constants count (by omega) +
        if constants ⟨count, by omega⟩ = 0 then 0 else 2 * (width - 2)

/-- The scalar of every actual prefix record is the inverse-square-root power of its vents. -/
lemma accumulatePrefixAlpha_eq_power (constants : Fin width → BitVec width)
    (count : Nat) (bounded : count ≤ width) :
    accumulatePrefixAlpha constants count bounded =
      NormalizedVector.invSqrt2 ^ accumulatePrefixVents constants count bounded := by
  induction count with
  | zero => exact (pow_zero _).symm
  | succ count ih =>
      rw [accumulatePrefixAlpha, accumulatePrefixVents, ih (by omega), pow_add]
      split <;> simp only [pow_zero]

/-- The actual retained physical outcome family has one binary factor per actual vent. -/
lemma accumulatePrefixWord_outcomes_card (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) (count : Nat)
    (bounded : count ≤ width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    Fintype.card (WordOutcomes physical sameWires
      (layout.accumulatePrefixWord wide modulus constants count bounded)) =
        2 ^ accumulatePrefixVents constants count bounded := by
  induction count with
  | zero => exact Fintype.card_unit
  | succ count ih =>
      rw [accumulatePrefixWord,
        ← Fintype.card_congr (appendOutcomesEquiv physical sameWires _ _), Fintype.card_prod,
        ih (by omega),
        Addition.Gidney.Measured.Reduction.Layout.modularWord_outcomes_card_if,
        accumulatePrefixVents, pow_add]
      split <;> simp only [pow_zero]

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
