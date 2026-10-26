/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.FrameLaws

/-!
# A selector fork that visits both children in order

Each child receives its actual computed selection bit. Its false-selection
action may still update data outside the selector frame. This supports a
streaming active flag while preserving the actual reversible prefix gates.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

/-- Both real child visits retain their order even when their false branch is nontrivial. -/
lemma streamedFork_correct {Data : Type} {encoding : BinaryLabelEncoding Data}
    (enable address work : EncodedBit encoding)
    (workEnable : work.wire ≠ enable.wire) (workAddress : work.wire ≠ address.wire)
    (left right : Bool → Data → Data)
    (leftProtects : ∀ selected, ForkAction enable address work (left selected))
    (rightProtects : ∀ selected, ForkAction enable address work (right selected))
    (state : Data) (clean : work.get state = false) :
    forkStep enable address work (fun value => left (work.get value) value)
      (fun value => right (work.get value) value) state =
      right (enable.get state && address.get state)
        (left (enable.get state && !address.get state) state) := by
  have flipEnable : ∀ value, enable.get (work.flip value) = enable.get value :=
    EncodedBit.get_flip_of_wire_ne work enable workEnable
  have flipAddress : ∀ value, address.get (work.flip value) = address.get value :=
    EncodedBit.get_flip_of_wire_ne work address workAddress
  have enableLeft := fun selected => (leftProtects selected).enable_get
  have addressLeft := fun selected => (leftProtects selected).address_get
  have workLeft := fun selected => (leftProtects selected).work_get
  have flipLeft := fun selected => (leftProtects selected).work_flip
  have enableRight := fun selected => (rightProtects selected).enable_get
  have addressRight := fun selected => (rightProtects selected).address_get
  have workRight := fun selected => (rightProtects selected).work_get
  have flipRight := fun selected => (rightProtects selected).work_flip
  cases enabled : enable.get state <;> cases selected : address.get state <;>
    simp_all [forkStep, zeroChildStep, cnotStep, toffoliStep,
      EncodedBit.get_flip_self, EncodedBit.flip_flip]

end

end QuantumAlg.EncodedBit.StreamedSelector
