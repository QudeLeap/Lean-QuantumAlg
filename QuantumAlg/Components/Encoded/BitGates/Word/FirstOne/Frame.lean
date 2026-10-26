/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Zero
import Mathlib.Data.List.Nodup

/-!
# Existing physical frame for a complete first-one encoder

The source, arbitrary target word, retained root plus clean prefix stack,
and one arbitrary restored work bit are supplied existing wires. Every
control and target separation is certified on those physical wires. A
complete static subword test allocates no additional quantum system.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Original source, arbitrary output and existing prefix/work systems of the native encoder. -/
structure Frame (encoding : BinaryLabelEncoding Data) (count outputWidth depth : Nat) where
  source : Word encoding count
  output : Word encoding outputWidth
  stack : Word encoding (depth + 1)
  work : EncodedBit encoding
  sourceDistinct : Function.Injective (fun index => (source.bit index).wire)
  outputDistinct : Function.Injective (fun index => (output.bit index).wire)
  stackDistinct : Function.Injective (fun index => (stack.bit index).wire)
  sourceOutput : ∀ sourceIndex outputIndex,
    (source.bit sourceIndex).wire ≠ (output.bit outputIndex).wire
  sourceStack : ∀ sourceIndex stackIndex,
    (source.bit sourceIndex).wire ≠ (stack.bit stackIndex).wire
  outputStack : ∀ outputIndex stackIndex,
    (output.bit outputIndex).wire ≠ (stack.bit stackIndex).wire
  sourceWork : ∀ index, (source.bit index).wire ≠ work.wire
  outputWork : ∀ index, (output.bit index).wire ≠ work.wire
  stackWork : ∀ index, (stack.bit index).wire ≠ work.wire

namespace Frame

variable {count outputWidth depth : Nat} (frame : Frame encoding count outputWidth depth)

/-- An ordered complete static source subword with unchanged physical wire identities. -/
def subword (labels : List (Fin count)) : Word encoding labels.length :=
  ⟨fun index => frame.source.bit (labels.get index)⟩

/-- The current retained root or prefix, before this node computes its child selection. -/
def enableAt (level : Nat) (present : level < depth) : EncodedBit encoding :=
  frame.stack.bit ⟨level, by omega⟩

/-- The next existing clean prefix is reused by both real children and then restored. -/
def nextAt (level : Nat) (present : level < depth) : EncodedBit encoding :=
  frame.stack.bit ⟨level + 1, by omega⟩

/-- The current retained enable and its next actual prefix have different physical wires. -/
lemma enable_next_ne (level : Nat) (present : level < depth) :
    (frame.enableAt level present).wire ≠ (frame.nextAt level present).wire := by
  intro same
  have equal := frame.stackDistinct same
  have values := congrArg (fun index : Fin (depth + 1) => index.val) equal
  change level = level + 1 at values
  omega

/-- A complete ordered subword uses the same arbitrary work and next existing prefix target. -/
def testLayout (labels : List (Fin count)) (distinct : labels.Nodup)
    (level : Nat) (present : level < depth) : Word.OneDirtyLayout (encoding := encoding)
      labels.length where
  source := frame.subword labels
  output := frame.nextAt level present
  work := frame.work
  source_injective := fun _ _ same => distinct.injective_get (frame.sourceDistinct same)
  source_output_ne := fun index => frame.sourceStack (labels.get index) ⟨level + 1, by omega⟩
  source_work_ne := fun index => frame.sourceWork (labels.get index)
  work_output_ne := Ne.symm (frame.stackWork _)

/-- The literal native full-zero test is selected by the same actual retained enable. -/
def testGates (labels : List (Fin count)) (distinct : labels.Nodup)
    (level : Nat) (present : level < depth) : List (GateSpec encoding) :=
  zeroGates (frame.testLayout labels distinct level present) (frame.enableAt level present)
    (fun index => Ne.symm (frame.sourceStack (labels.get index) ⟨level, by omega⟩))
    (frame.enable_next_ne level present) (frame.stackWork _)

/-- Every source mask, dirty-work restoration and prefix toggle belongs
to the actual native list. -/
lemma testGates_step (labels : List (Fin count)) (distinct : labels.Nodup)
    (level : Nat) (present : level < depth) (state : Data) :
    GateSpec.stepList (frame.testGates labels distinct level present) state =
      predicateFlip (frame.nextAt level present)
        (fun value => (frame.enableAt level present).get value &&
          zeroPredicate (frame.subword labels) value) state :=
  zeroGates_step _ _ _ _ _ state

/-- The complete physical zero test includes its retained enable and all negative-control masks. -/
lemma testGates_length_le (labels : List (Fin count)) (distinct : labels.Nodup)
    (level : Nat) (present : level < depth) :
    (frame.testGates labels distinct level present).length ≤ 10 * (labels.length + 1) + 1 :=
  zeroGates_length_le _ _ _ _ _

end Frame

end

end QuantumAlg.EncodedBit.FirstOne
