/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail.Records
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Records
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Availability
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Availability.Words

/-!
# Exact actual physical record family of the two measured modular additions

The original finite record bank is used twice, in the same physical order.
The chronological outcome family retains both actual measurements even
though the second pass overwrites those same cells. Native comparisons
and the middle toggle contribute no outcomes [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Execution Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum}

/-- The exact two chronological physical vent passes reuse every original record-bank index. -/
lemma modularWord_ventIndices (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (nonzero : constant ≠ 0) :
    ventIndices (layout.modularWord wide modulus constant) =
      List.ofFn (fun record : Fin (width - 2) => record) ++
        List.ofFn (fun record : Fin (width - 2) => record) := by
  rw [modularWord, if_neg nonzero]
  simp only [ventIndices_append, ventIndices, List.nil_append, List.append_nil,
    Measured.Layout.adderWord_ventIndices]

/-- The actual nonzero-offset physical outcome family has exactly one binary result per vent. -/
lemma modularWord_outcomes_card (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (nonzero : constant ≠ 0)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    Fintype.card (WordOutcomes physical sameWires (layout.modularWord wide modulus constant)) =
      2 ^ (2 * (width - 2)) := by
  rw [wordOutcomes_card, modularWord_ventIndices layout wide modulus constant nonzero,
    List.length_append, List.length_ofFn]
  congr 1
  omega

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
