/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Measurements
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Records

/-!
# Exact actual measurement multiplicity of the same clean-flag modular-addition word

Every nonzero canonical row executes both original vent passes. The same
cells are physically reused, while all chronological measurement events
remain charged. Literal zero rows emit none [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual source-selected row has zero or precisely two original vent passes. -/
lemma modularWord_measurementCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) :
    wordMeasurementCount (layout.modularWord wide modulus constant) =
      if constant = 0 then 0 else 2 * (width - 2) := by
  by_cases zero : constant = 0
  · rw [modularWord, if_pos zero, if_pos zero]
    rfl
  · rw [wordMeasurementCount_eq_ventIndices_length,
      modularWord_ventIndices layout wide modulus constant zero, if_neg zero,
      List.length_append, List.length_ofFn]
    omega

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
