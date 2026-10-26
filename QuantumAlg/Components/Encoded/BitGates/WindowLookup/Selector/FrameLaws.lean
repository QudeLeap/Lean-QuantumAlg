/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector

/-!
# Physical prefix computation and scoped fork laws

A prefix is restored by reversible native gates. Payload correctness assumes
only the current prefix starts clean, and that the ideal payload actions do
not inspect that temporary prefix. All other data may be dirty.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The semantic action of computing one zero-address child into its prefix. -/
def zeroChildStep (enable address work : EncodedBit encoding) (state : Data) : Data :=
  if enable.get state && !address.get state then work.flip state else state

/-- Explicit conditional payload action, with the original prefix retained. -/
def conditionalAction (enable : EncodedBit encoding) (action : Data → Data) (state : Data) : Data :=
  if enable.get state then action state else state

/-- Exact semantic execution order of one native unitary selector fork. -/
def forkStep (enable address work : EncodedBit encoding) (left right : Data → Data)
    (state : Data) : Data :=
  toffoliStep enable address work
    (right (cnotStep enable work (left (zeroChildStep enable address work state))))

namespace SelectorFrame

variable {width : Nat}

/-- The actual three native instructions compute exactly the zero-address prefix. -/
lemma leftGates_step (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) (state : Data) :
    GateSpec.stepList (frame.leftGates depth present) state =
      zeroChildStep (frame.enableAt depth present) (frame.addressAt depth present)
        (frame.prefixAt depth present) state := by
  simp only [leftGates, GateSpec.stepList, GateSpec.step, id_eq]
  unfold toffoliStep
  rw [EncodedBit.get_flip_of_wire_ne _ _ (Ne.symm (frame.enable_address depth present)),
    EncodedBit.get_flip_self]
  unfold zeroChildStep
  split
  · rw [EncodedBit.flip_comm, EncodedBit.flip_flip]
  · exact EncodedBit.flip_flip _ _

/-- An ideal payload ignores the temporary prefix, even while it may inspect the enable. -/
def IndependentPrefixes (frame : SelectorFrame encoding width) (action : Data → Data) : Prop :=
  ∀ (index : Fin width) state,
    action ((frame.stack index.succ).flip state) = (frame.stack index.succ).flip (action state)

end SelectorFrame

/-- A payload protects the fork controls and the current temporary prefix. -/
structure ForkAction (enable address work : EncodedBit encoding) (action : Data → Data) : Prop where
  enable_get : ∀ state, enable.get (action state) = enable.get state
  address_get : ∀ state, address.get (action state) = address.get state
  work_get : ∀ state, work.get (action state) = work.get state
  work_flip : ∀ state, action (work.flip state) = work.flip (action state)

/-- Computing, selecting the two children and clearing gives exactly the enabled child action. -/
lemma scopedFork_correct (enable address work : EncodedBit encoding)
    (workEnable : work.wire ≠ enable.wire) (workAddress : work.wire ≠ address.wire)
    (left right : Data → Data) (leftProtects : ForkAction enable address work left)
    (rightProtects : ForkAction enable address work right) (state : Data)
    (clean : work.get state = false) :
    forkStep enable address work (conditionalAction work left)
      (conditionalAction work right) state =
      if enable.get state then
        (if address.get state then right state else left state) else state := by
  have flipEnable : ∀ value, enable.get (work.flip value) = enable.get value :=
    EncodedBit.get_flip_of_wire_ne work enable workEnable
  have flipAddress : ∀ value, address.get (work.flip value) = address.get value :=
    EncodedBit.get_flip_of_wire_ne work address workAddress
  have enableLeft := leftProtects.enable_get
  have addressLeft := leftProtects.address_get
  have workLeft := leftProtects.work_get
  have flipLeft := leftProtects.work_flip
  have enableRight := rightProtects.enable_get
  have addressRight := rightProtects.address_get
  have workRight := rightProtects.work_get
  have flipRight := rightProtects.work_flip
  cases enabled : enable.get state <;> cases selected : address.get state <;>
    simp_all [forkStep, zeroChildStep, conditionalAction, cnotStep, toffoliStep,
      EncodedBit.get_flip_self, EncodedBit.flip_flip]

end

end QuantumAlg.EncodedBit.WindowLookup
