/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.PortProgram
import all QuantumAlg.Components.Encoded.BitGates.Word.Reverse
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap

/-!
# Native coordinates of the actual full output-port orientation

Every symmetric pair in the complete original word executes the existing
three-CNOT swap. This is the original physical word of width n+3, including
the padding positions; it is not a free logical relabeling.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit

private lemma swap_x_count {Data : Type} {frame : BinaryLabelEncoding Data} {width : Nat}
    (left right : Word frame width)
    (separate : ∀ index, (left.bit index).wire ≠ (right.bit index).wire) :
    ((Word.swapGates left right separate).map GateSpec.xMultiplicity).sum = 0 := by
  unfold Word.swapGates
  generalize (List.ofFn fun index : Fin width => index) = indices
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simpa only [List.flatMap_cons, List.map_append, List.sum_append, EncodedBit.swapGates,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, GateSpec.xMultiplicity_cnot,
        Nat.zero_add] using inductionHypothesis

/-- The same actual full reversal retains all three native CNOTs per physical exchanged pair. -/
lemma orientation_source_counts (width : Nat) :
    ((OutputPortProgram.orientationGates width).map GateSpec.toffoliMultiplicity).sum = 0 ∧
      ((OutputPortProgram.orientationGates width).map GateSpec.cnotMultiplicity).sum =
        3 * ((width + 3) / 2) ∧
      ((OutputPortProgram.orientationGates width).map GateSpec.xMultiplicity).sum = 0 := by
  simp only [OutputPortProgram.orientationGates, Word.reverseGates]
  exact ⟨Word.swapGates_toffoliMultiplicity_sum _ _ _,
    Word.swapGates_cnotMultiplicity_sum _ _ _, swap_x_count _ _ _⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
