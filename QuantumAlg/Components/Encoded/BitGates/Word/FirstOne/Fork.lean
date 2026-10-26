/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Predicate

/-!
# A restored prefix fork selected by a full word predicate

The actual predicate-toggle body is supplied separately by the native
word-zero circuit. This semantic composition exposes all four parent
toggle/copy operations and both child visits. It does not introduce a
primitive gate implementing a mathematical predicate for free.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- A child preserves every retained fork readout and commutes with its unused prefix flip. -/
structure ForkAction (enable next : EncodedBit encoding) (predicate : Data → Bool)
    (action : Data → Data) : Prop where
  enable_get : ∀ state, enable.get (action state) = enable.get state
  next_get : ∀ state, next.get (action state) = next.get state
  next_flip : ∀ state, action (next.flip state) = next.flip (action state)
  predicate_get : ∀ state, predicate (action state) = predicate state

/-- The same next prefix selects both real children and is then physically uncomputed. -/
def forkStep (enable next : EncodedBit encoding) (predicate : Data → Bool)
    (lower higher : Bool → Data → Data) (state : Data) : Data :=
  let toggle := predicateFlip next (fun value => enable.get value && predicate value)
  let first := toggle state
  let lowerDone := lower (next.get first) first
  let alternate := cnotStep enable next lowerDone
  let higherDone := higher (next.get alternate) alternate
  cnotStep enable next (toggle higherDone)

/-- The literal toggle/copy order restores the prefix and retains both selected child actions. -/
lemma forkStep_correct (enable next : EncodedBit encoding)
    (different : next.wire ≠ enable.wire) (predicate : Data → Bool)
    (predicateFlip : ∀ state, predicate (next.flip state) = predicate state)
    (lower higher : Bool → Data → Data)
    (lowerProtects : ∀ selected, ForkAction enable next predicate (lower selected))
    (higherProtects : ∀ selected, ForkAction enable next predicate (higher selected))
    (state : Data) (clean : next.get state = false) :
    forkStep enable next predicate lower higher state =
      higher (enable.get state && !predicate state)
        (lower (enable.get state && predicate state) state) := by
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
  cases enabled : enable.get state <;> cases selected : predicate state <;>
    simp_all [forkStep, EncodedBit.predicateFlip, cnotStep, get_flip_self, flip_flip]

end

end QuantumAlg.EncodedBit.FirstOne
