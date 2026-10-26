/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Coordinates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Availability

/-!
# Actual physical measurement counts and the original chronological vent list

The trace-derived count agrees with the length of the same emitted vent
index list. Repeated writes to one physical cell remain distinct actual
measurements [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}

/-- The actual measurement multiplicity is exactly the number of original chronological vents. -/
lemma wordMeasurementCount_eq_ventIndices_length (word : List (Instruction encoding records)) :
    wordMeasurementCount word = (ventIndices word).length := by
  induction word with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction with
      | native gates =>
          simpa only [wordMeasurementCount, List.map_cons, List.sum_cons, measurementCount,
            ventIndices, Nat.zero_add] using ih
      | vent target record =>
          change 1 + wordMeasurementCount rest = (ventIndices rest).length + 1
          omega
      | phase target record =>
          simpa only [wordMeasurementCount, List.map_cons, List.sum_cons, measurementCount,
            ventIndices, Nat.zero_add] using ih

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
