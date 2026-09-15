/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.ZeroTest

/-!
# Native leading-bit predicates for the initial divisor length

The source initializes the divisor length from the value actually carried
by Work2 [LYL+26, sec_EEA/sub_4phase.tex:108-117]. Its three padding bits are
excluded from this read. Each prefix predicate below is an explicit list
of X, CNOT, and Toffoli gates; it xors into a selected existing divisor-length
bit and restores every other source-register coordinate. Wider predicates
borrow only actual Work1 bits, with arbitrary incoming values, using the
proved arbitrary-work refinement of [dW19, qcnotes.tex:1335-1337].

Two consecutive prefix-zero tests select exactly the first nonzero payload
bit. Their difference supplies the binary length writer without preparing
an input-dependent constant or allocating hidden work. These predicates
read the current payload, so the later initializer can compute the length
after the source's conditional folding rather than retain a stale length.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthPredicate

noncomputable section

open EncodedBit

/-- An actual payload bit of Work2, beyond its three physical padding bits. -/
def payloadBit (width : Nat) (index : Fin width) : EncodedBit (encoding width) :=
  secondWordBit width ⟨3 + index.val, by have bound := index.isLt; omega⟩

theorem payloadBit_get (width : Nat) (index : Fin width) (state : Registers width) :
    (payloadBit width index).get state = state.secondWord.getMsbD (3 + index.val) :=
  secondWordBit_get width _ state

private theorem payloadBit_wire (width : Nat) (index : Fin width) :
    (payloadBit width index).wire.val = width + 3 + (3 + index.val) :=
  secondWordBit_wire width _

private theorem payload_output_ne (width : Nat) (index : Fin width)
    (output : Fin width.size) :
    (payloadBit width index).wire ≠ (divisorLengthBit width output).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [payloadBit_wire, divisorLengthBit_wire] at values
  have bound := index.isLt
  omega

/-- A mathematical predicate of precisely the first `count` physical payload bits. -/
def zeroPrefix (width count : Nat) (within : count ≤ width) (state : Registers width) : Prop :=
  ∀ index : Fin count,
    (payloadBit width ⟨index.val, lt_of_lt_of_le index.isLt within⟩).get state = false

private instance zeroPrefixDecidable (width count : Nat) (within : count ≤ width)
    (state : Registers width) : Decidable (zeroPrefix width count within state) :=
  inferInstanceAs (Decidable (∀ index : Fin count,
    (payloadBit width ⟨index.val, lt_of_lt_of_le index.isLt within⟩).get state = false))

private theorem zeroPrefix_flip (width count : Nat) (within : count ≤ width)
    (output : Fin width.size) (state : Registers width) :
    zeroPrefix width count within ((divisorLengthBit width output).flip state) ↔
      zeroPrefix width count within state := by
  unfold zeroPrefix
  apply forall_congr'
  intro index
  rw [EncodedBit.get_flip_of_wire_ne _ _ (payload_output_ne width _ output).symm]

/-- A prefix of at least two bits borrows only existing Work1 coordinates. -/
def longLayout (width tail : Nat) (within : tail + 2 ≤ width) (output : Fin width.size) :
    Word.ZeroTestLayout (encoding := encoding width) tail where
  source := ⟨fun index => payloadBit width
    ⟨index.val, lt_of_lt_of_le index.isLt within⟩⟩
  output := divisorLengthBit width output
  work := ⟨fun index => firstWordBit width
    ⟨index.val, by have bound := index.isLt; omega⟩⟩
  source_source_ne := by
    intro left right different same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    have leftPosition := payloadBit_wire width
      ⟨left.val, lt_of_lt_of_le left.isLt within⟩
    have rightPosition := payloadBit_wire width
      ⟨right.val, lt_of_lt_of_le right.isLt within⟩
    have positions := leftPosition.symm.trans (values.trans rightPosition)
    change width + 3 + (3 + left.val) = width + 3 + (3 + right.val) at positions
    omega
  source_output_ne := fun index => payload_output_ne width _ output
  source_work_ne := by
    intro sourceIndex workIndex same
    have values := congrArg Fin.val same
    change (payloadBit width _).wire.val = (firstWordBit width _).wire.val at values
    rw [payloadBit_wire, firstWordBit_wire] at values
    have bound := workIndex.isLt
    omega
  work_work_ne := by
    intro left right different same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    change (firstWordBit width _).wire.val = (firstWordBit width _).wire.val at values
    rw [firstWordBit_wire, firstWordBit_wire] at values
    exact values
  work_output_ne := by
    intro index same
    have values := congrArg Fin.val same
    change (firstWordBit width _).wire.val = (divisorLengthBit width output).wire.val at values
    rw [firstWordBit_wire, divisorLengthBit_wire] at values
    have bound := index.isLt
    omega

/-- An empty prefix uses X, one bit uses X/CNOT, and every wider prefix uses restored dirty work. -/
def gates (width : Nat) (output : Fin width.size) :
    (count : Nat) → count ≤ width → List (GateSpec (encoding width))
  | 0, _ => [.x (divisorLengthBit width output)]
  | 1, within =>
      [.x (divisorLengthBit width output),
        .cnot (payloadBit width ⟨0, by omega⟩) (divisorLengthBit width output)
          (payload_output_ne width _ output)]
  | tail + 2, within => (longLayout width tail within output).borrowedZeroGates

/-- The literal gates act correctly on the entire register value, including arbitrary work. -/
theorem gates_step (width count : Nat) (within : count ≤ width) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (gates width output count within) state =
      if zeroPrefix width count within state then (divisorLengthBit width output).flip state
      else state := by
  classical
  cases count with
  | zero =>
      simp [gates, GateSpec.stepList, GateSpec.step, zeroPrefix]
  | succ previous =>
      cases previous with
      | zero =>
          have condition : zeroPrefix width 1 within state ↔
              (payloadBit width ⟨0, by omega⟩).get state = false := by
            constructor
            · intro zeros
              exact zeros 0
            · intro zero index
              have indexZero : index = 0 := Subsingleton.elim _ _
              subst index
              exact zero
          rw [show gates width output 1 within =
            [.x (divisorLengthBit width output),
              .cnot (payloadBit width ⟨0, by omega⟩) (divisorLengthBit width output)
                (payload_output_ne width _ output)] from rfl]
          change cnotStep (payloadBit width ⟨0, by omega⟩) (divisorLengthBit width output)
            ((divisorLengthBit width output).flip state) = _
          simp only [condition, cnotStep, EncodedBit.get_flip_of_wire_ne _ _
            (payload_output_ne width _ output).symm]
          cases selected : (payloadBit width ⟨0, by omega⟩).get state <;>
            simp [EncodedBit.flip_flip]
      | succ tail =>
          exact (longLayout width tail within output).borrowedZeroGates_step state

/-- The leading position is recognized by the zero prefix followed by a nonzero next bit. -/
def firstOne (width : Nat) (index : Fin width) (state : Registers width) : Prop :=
  zeroPrefix width index.val (Nat.le_of_lt index.isLt) state ∧
    (payloadBit width index).get state = true

private instance firstOneDecidable (width : Nat) (index : Fin width) (state : Registers width) :
    Decidable (firstOne width index state) :=
  inferInstanceAs (Decidable (zeroPrefix width index.val (Nat.le_of_lt index.isLt) state ∧
    (payloadBit width index).get state = true))

private theorem zeroPrefix_succ (width : Nat) (index : Fin width) (state : Registers width) :
    zeroPrefix width (index.val + 1) index.isLt state ↔
      zeroPrefix width index.val (Nat.le_of_lt index.isLt) state ∧
        (payloadBit width index).get state = false := by
  constructor
  · intro zeros
    constructor
    · intro previous
      exact zeros ⟨previous.val, by have bound := previous.isLt; omega⟩
    · exact zeros ⟨index.val, by omega⟩
  · rintro ⟨zeros, last⟩ selected
    by_cases final : selected.val = index.val
    · have same : (⟨selected.val, lt_of_lt_of_le selected.isLt index.isLt⟩ : Fin width) =
          index := Fin.ext final
      change (payloadBit width _).get state = false
      rw [same]
      exact last
    · exact zeros ⟨selected.val, by have bound := selected.isLt; omega⟩

/-- Two actual zero-predicate circuits select a candidate leading bit without retaining a flag. -/
def firstOneGates (width : Nat) (index : Fin width) (output : Fin width.size) :
    List (GateSpec (encoding width)) :=
  gates width output index.val (Nat.le_of_lt index.isLt) ++
    gates width output (index.val + 1) index.isLt

/-- The two literal predicate calls flip only the chosen length bit at the actual leading one. -/
theorem firstOneGates_step (width : Nat) (index : Fin width) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (firstOneGates width index output) state =
      if firstOne width index state then (divisorLengthBit width output).flip state else state := by
  classical
  rw [firstOneGates, GateSpec.stepList_append,
    gates_step width index.val (Nat.le_of_lt index.isLt) output state]
  by_cases earlier : zeroPrefix width index.val (Nat.le_of_lt index.isLt) state
  · rw [if_pos earlier, gates_step]
    have retained := EncodedBit.get_flip_of_wire_ne (divisorLengthBit width output)
      (payloadBit width index) (payload_output_ne width index output).symm state
    simp only [zeroPrefix_flip, zeroPrefix_succ, earlier, true_and, firstOne, retained]
    cases (payloadBit width index).get state <;> simp [EncodedBit.flip_flip]
  · rw [if_neg earlier, gates_step]
    simp only [zeroPrefix_succ, earlier, false_and, if_false, firstOne]

/-- The leading-bit predicate is realized by those same elementary native gates. -/
theorem firstOneGates_realizes (width : Nat) (index : Fin width) (output : Fin width.size) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (firstOneGates width index output))
      (fun state => if firstOne width index state
        then (divisorLengthBit width output).flip state else state) :=
  GateSpec.realizesList_congrStep (firstOneGates width index output)
    (firstOneGates_step width index output)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthPredicate
