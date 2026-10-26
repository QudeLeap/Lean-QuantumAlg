/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Fork

/-!
# Exact first-one fork action with an arbitrary incoming prefix

Both real child visits are selected by the original prefix XOR their
computed parent predicate. The same full native toggle/copy schedule
restores that original prefix. Cleanliness is needed only when interpreting
the selected child as the original first-marked search branch.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The literal restored fork retains its original dirty prefix in both child-selection formulas. -/
lemma forkStep_dirty_correct (enable next : EncodedBit encoding)
    (different : next.wire ≠ enable.wire) (predicate : Data → Bool)
    (predicateFlip : ∀ state, predicate (next.flip state) = predicate state)
    (lower higher : Bool → Data → Data)
    (lowerProtects : ∀ selected, ForkAction enable next predicate (lower selected))
    (higherProtects : ∀ selected, ForkAction enable next predicate (higher selected))
    (state : Data) :
    forkStep enable next predicate lower higher state =
      higher (next.get state ^^ (enable.get state && !predicate state))
        (lower (next.get state ^^ (enable.get state && predicate state)) state) := by
  have retainedEnable : ∀ value, enable.get (next.flip value) = enable.get value :=
    get_flip_of_wire_ne next enable different
  have lowerEnable := fun selected => (lowerProtects selected).enable_get
  have lowerNext := fun selected => (lowerProtects selected).next_get
  have lowerFlip := fun selected => (lowerProtects selected).next_flip
  have lowerPredicate := fun selected => (lowerProtects selected).predicate_get
  have higherEnable := fun selected => (higherProtects selected).enable_get
  have higherNext := fun selected => (higherProtects selected).next_get
  have higherFlip := fun selected => (higherProtects selected).next_flip
  have higherPredicate := fun selected => (higherProtects selected).predicate_get
  cases old : next.get state <;> cases enabled : enable.get state <;>
    cases selected : predicate state <;>
    simp_all [forkStep, EncodedBit.predicateFlip, cnotStep, get_flip_self, flip_flip]

end

end QuantumAlg.EncodedBit.FirstOne
