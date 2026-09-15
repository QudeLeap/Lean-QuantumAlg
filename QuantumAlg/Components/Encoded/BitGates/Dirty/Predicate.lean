/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic

/-!
# A conjunction of predicates using one restored dirty bit

Four alternating predicate-controlled flips cancel the incoming value of a
borrowed wire. This semantic identity applies to complete encoded states and
is used when lowering larger control sets to actual elementary gate lists.
The toggle cancellation principle is described in [G17, paper.tex:278-293].
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Flip one actual encoded wire when the mathematical predicate holds. -/
def predicateFlip (target : EncodedBit encoding) (predicate : Data → Bool) (state : Data) : Data :=
  if predicate state then target.flip state else state

/-- Alternate the two exact predicate actions, retaining every encoded coordinate. -/
def dirtyPredicateConjunction (work output : EncodedBit encoding)
    (first second : Data → Bool) (state : Data) : Data :=
  let toggle := predicateFlip work first
  let copy := predicateFlip output (fun value => second value && work.get value)
  copy (toggle (copy (toggle state)))

/-- Two alternating toggles remove the arbitrary work value and return the full work state. -/
theorem dirtyPredicateConjunction_eq (work output : EncodedBit encoding)
    (different : work.wire ≠ output.wire) (first second : Data → Bool)
    (firstWork : ∀ state, first (work.flip state) = first state)
    (firstOutput : ∀ state, first (output.flip state) = first state)
    (secondWork : ∀ state, second (work.flip state) = second state)
    (secondOutput : ∀ state, second (output.flip state) = second state)
    (state : Data) :
    dirtyPredicateConjunction work output first second state =
      predicateFlip output (fun value => first value && second value) state := by
  have workRead : ∀ value, work.get (output.flip value) = work.get value :=
    get_flip_of_wire_ne output work different.symm
  have commute : ∀ value, work.flip (output.flip value) = output.flip (work.flip value) :=
    flip_comm work output
  cases firstValue : first state <;> cases secondValue : second state <;>
    cases workValue : work.get state <;>
    simp [dirtyPredicateConjunction, predicateFlip, firstWork, firstOutput,
      secondWork, secondOutput, workRead, get_flip_self, commute, flip_flip,
      firstValue, secondValue, workValue]

end

end QuantumAlg.EncodedBit
