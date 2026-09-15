/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Conditional refinement of complete actual native gate lists

Suppose each emitted replacement block has the complete action of its
original block when a retained predicate holds, and otherwise has the
identity action. If every original block preserves the predicate, the
same equation holds for their flattened emitted lists. The statement
compares actual native lists and their complete state actions; physical
control synthesis and the events of each replacement remain in its owner.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

/-- Conditional block refinement composes over the complete flattened native sequence. -/
theorem stepList_flatMap_if {Data Block : Type} {encoding : BinaryLabelEncoding Data}
    (predicate : Data → Prop) [DecidablePred predicate]
    (original replacement : Block → List (GateSpec encoding))
    (blockAction : ∀ block state,
      stepList (replacement block) state =
        if predicate state then stepList (original block) state else state)
    (retained : ∀ block state, predicate (stepList (original block) state) ↔ predicate state)
    (blocks : List Block) (state : Data) :
    stepList (blocks.flatMap replacement) state =
      if predicate state then stepList (blocks.flatMap original) state else state := by
  induction blocks generalizing state with
  | nil => simp [stepList]
  | cons head rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, stepList_append, stepList_append, blockAction]
      by_cases active : predicate state
      · rw [if_pos active, ih, if_pos ((retained head state).mpr active), if_pos active]
      · rw [if_neg active, ih, if_neg active, if_neg active]

end

end QuantumAlg.EncodedBit.GateSpec
