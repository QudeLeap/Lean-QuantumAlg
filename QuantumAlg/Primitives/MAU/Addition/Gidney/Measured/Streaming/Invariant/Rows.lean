/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant.Step

/-!
# Original-data invariant along the actual chronological streaming prefix

The induction follows the literal increasing-index rows after the original
native offset word. It imposes only the two original clean-helper values;
every original target, control and dirty value remains arbitrary
[G25, main.tex:209-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every actual prefix before the final row satisfies the same original-data invariant. -/
lemma streamingRows_prefixInvariant (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (count : Nat) (bounded : count ≤ width - 2) :
    layout.PrefixInvariant constant initial
      (wordLabel (layout.streamingRows wide constant count (by omega))
        (stepList (layout.offsetGates constant) initial)) count := by
  revert bounded
  induction count with
  | zero =>
      intro _
      exact offsetGates_prefixInvariant layout constant initial clean
  | succ count ih =>
      intro bounded
      rw [streamingRows_label_succ]
      exact prefixInvariant_step wide count bounded (ih (by omega))

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
