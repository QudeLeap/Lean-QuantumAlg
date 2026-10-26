/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Coordinates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Coordinates

/-!
# Closed native coordinates of the actual measured clean-flag modular addition

The bounds sum both original native comparisons and both paid measured
additions. The flag toggle remains its one native Toffoli. Zero static
offset rows are literal identity [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every original modular-addition word retains both CNOT and paid one-qubit bounds. -/
lemma modularWord_coordinate_bounds (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (modulus constant : BitVec width) :
    wordCnotCount (layout.modularWord wide modulus constant) ≤ 54 * width - 90 ∧
      wordSingleQubitBound (layout.modularWord wide modulus constant) ≤ 12 * width - 16 := by
  unfold modularWord
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · have firstCompare := comparisonGates_cnot_bound layout wide large (modulus - constant)
    have lastCompare := comparisonGates_cnot_bound layout wide large constant
    have firstAdder := Addition.Gidney.Measured.Layout.adderWord_cnot_bound
      layout.adderLayout wide large constant
    have lastAdder := Addition.Gidney.Measured.Layout.adderWord_cnot_bound
      layout.adderLayout wide large (constant - modulus)
    constructor
    · simp only [wordCnotCount_append]
      change ((layout.comparisonGates wide (modulus - constant)).map cnotMultiplicity).sum +
        wordCnotCount (layout.adderLayout.adderWord wide constant) + 0 +
          wordCnotCount (layout.adderLayout.adderWord wide (constant - modulus)) +
            ((layout.comparisonGates wide constant).map cnotMultiplicity).sum ≤ _
      omega
    · have nativeSingle (gates : List (GateSpec encoding)) :
          wordSingleQubitBound (records := width - 2) [.native gates] =
            (gates.map xMultiplicity).sum := rfl
      simp only [wordSingleQubitBound_append, nativeSingle, comparisonGates_x_count,
        Addition.Gidney.Measured.Layout.adderWord_single_bound]
      change 0 + (6 * width - 8) + 0 + (6 * width - 8) + 0 ≤ _
      omega

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
