/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Records
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record

/-!
# Exact actual reduction outcome cardinality including zero-offset identity

The literal zero-offset branch emits no measurement. Every other static
offset retains both chronological binary vent passes on the same original
record cells [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Execution Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum}

/-- The actual outcome family has exactly the size selected by the literal source branch. -/
lemma modularWord_outcomes_card_if (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    Fintype.card (WordOutcomes physical sameWires (layout.modularWord wide modulus constant)) =
      if constant = 0 then 1 else 2 ^ (2 * (width - 2)) := by
  by_cases zero : constant = 0
  · rw [modularWord, if_pos zero, if_pos zero]
    change Fintype.card Unit = 1
    exact Fintype.card_unit
  · rw [if_neg zero]
    exact modularWord_outcomes_card layout wide modulus constant zero physical sameWires

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
