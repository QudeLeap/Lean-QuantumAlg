/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Frame
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import Mathlib.Data.Fintype.Card

/-!
# Existing arbitrary borrowed bank for a native first-one producer

The bank is supplied storage disjoint from every source, output and
retained prefix system. No zero promise or additional allocation is used.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- Existing physically disjoint arbitrary bank, restored by every complete native test. -/
structure BorrowedBank (bankWidth : Nat) where
  word : Word encoding bankWidth
  distinct : Function.Injective (fun index => (word.bit index).wire)
  capacity : count - 1 ≤ bankWidth
  sourceBank : ∀ source bank, (frame.source.bit source).wire ≠ (word.bit bank).wire
  outputBank : ∀ output bank, (frame.output.bit output).wire ≠ (word.bit bank).wire
  stackBank : ∀ stack bank, (frame.stack.bit stack).wire ≠ (word.bit bank).wire

namespace BorrowedBank

variable {frame} {bankWidth : Nat} (bank : frame.BorrowedBank bankWidth)

/-- Borrow the first supplied arbitrary bank bits without changing their physical identities. -/
def takeWord (size : Nat) (fits : size ≤ bankWidth) : Word encoding size :=
  ⟨fun index => bank.word.bit ⟨index.val, Nat.lt_of_lt_of_le index.isLt fits⟩⟩

/-- A real complete source subword plus its enable uses exactly one fewer borrowed chain bits. -/
def conjunctionLayout (head : Fin count) (rest : List (Fin count))
    (unique : (head :: rest).Nodup) (level : Nat) (present : level < depth) :
    Word.ZeroTestLayout (encoding := encoding) rest.length := by
  have bounded := unique.length_le_card
  simp only [List.length_cons, Fintype.card_fin] at bounded
  have fits : rest.length ≤ bankWidth := by have available := bank.capacity; omega
  let original := frame.testLayout (head :: rest) unique level present
  let controls := original.controlledPatternLayout (frame.enableAt level present)
    (fun index => Ne.symm (frame.sourceStack ((head :: rest).get index) ⟨level, by omega⟩))
    (frame.enable_next_ne level present) (frame.stackWork _)
  exact {
    source := controls.source
    output := frame.nextAt level present
    work := bank.takeWord rest.length fits
    source_source_ne := fun _ _ different same => different (controls.source_injective same)
    source_output_ne := controls.source_output_ne
    source_work_ne := by
      intro source work
      refine Fin.cases ?_ (fun original => ?_) source
      · exact bank.stackBank _ _
      · exact bank.sourceBank ((head :: rest).get original) _
    work_work_ne := by
      intro left right different same
      have equal := bank.distinct same
      have values : left.val = right.val :=
        congrArg (fun index : Fin bankWidth => index.val) equal
      exact different (Fin.ext values)
    work_output_ne := fun _ => Ne.symm (bank.stackBank _ _)
  }

end BorrowedBank

end

end QuantumAlg.EncodedBit.FirstOne.Frame
