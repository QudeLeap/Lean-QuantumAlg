/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Feedback.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Chronological

/-!
# Paid feedback depends only on the original earlier measured bits

Every scalar is the same product of the actual selected native phase gates.
Distinct real storage keys prove that arbitrary old future or unrelated
values are never read in place of the measured prefix [GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

/-- The original record's product of the same selected native feedback phase scalars. -/
def recordFeedbackScalar (inverse : Bool) {bits : Nat} (record : Fin bits → Fin 2)
    (position : Fin bits) : (count : Nat) → count ≤ position.val → ℂ
  | 0, _ => 1
  | count + 1, bounded =>
      Recycling.FeedbackCarrier.selectedScalar inverse (position.val - count - 1)
        (.finite (record ⟨count, by have bound := position.isLt; omega⟩)) *
          recordFeedbackScalar inverse record position count (by omega)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ChronologicalFeedbackCtx := context base noQuantum m ell width

/-- Earlier real output writes determine every paid feedback scalar without an old-Store promise. -/
lemma feedbackScalar_after_prefix (inverse : Bool) {bits : Nat}
    (selection : Fin bits → Fin (resultBits m ell)) (separate : Function.Injective selection)
    (record : Fin bits → Fin 2)
    (original : Store (ChronologicalFeedbackCtx base noQuantum m ell width))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val) :
    feedbackScalar base noQuantum m ell width inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) position count
        bounded
        (Store.writePrefix (fun index => resultCell base noQuantum m ell width (selection index))
          (fun index => .finite (record index)) original position.val
          (Nat.le_of_lt position.isLt)) =
      recordFeedbackScalar inverse record position count bounded := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [feedbackScalar, recordFeedbackScalar, induction]
      rw [Store.read_writePrefix
        (fun index => resultCell base noQuantum m ell width (selection index))
        (fun index => .finite (record index))
        ((resultCell_key_injective base noQuantum m ell width).comp separate) original position.val
        (Nat.le_of_lt position.isLt) ⟨count, by have bound := position.isLt; omega⟩
        (Nat.lt_of_succ_le bounded)]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
