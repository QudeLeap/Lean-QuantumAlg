/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Util.NumberTheory.SharedEEA.PaddingClock

/-!
# Exact native register encoding for shared EEA

The registered allocation uses two `n+3`-bit shared words, four
`Nat.size n`-bit length registers, and five individual control bits
[LYL+26, sec_EEA/sub_regshare.tex:16-26]. In particular, the separate
`Ctrl` bit is present in addition to `Phase1`, `Phase2`, `Sign`, and `Iter`.

Physical fields occur in this order: Work1, Work2, coefficient length,
quotient length, divisor length, low shift, Phase1, Phase2, Sign, Iter,
Ctrl. Every finite field value has an exact computational-basis encoding;
no valid-state promise or cardinality-only encoding discards other labels.
Widths zero and one remain valid encoding parameters. The original prime
algorithm domain establishes `n ≥ 2` separately.

The candidate terminal high-counter bits are already inside Work1 at
its local physical positions `n` and `n+1`. There is no extra high-counter
field. This owner specifies real register width and exact bit order; it
does not claim initialization, an executed EEA round, or a complete
algorithm resource formula. Every control and input-dependent history
field remains explicitly represented.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA

noncomputable section

open NumberTheory.SharedEEA

/-- All actual shared words, finite source lengths, phase/parity bits, and the separate Ctrl bit. -/
structure Registers (width : Nat) where
  firstWord : BitVec (width + 3)
  secondWord : BitVec (width + 3)
  coefficientLength : BitVec width.size
  quotientLength : BitVec width.size
  divisorLength : BitVec width.size
  shift : BitVec width.size
  flags : PhaseControl.Flags
  control : Bool
deriving DecidableEq

/-- The source fields grouped only for exact product encoding, in the declared physical order. -/
abbrev RegisterTuple (width : Nat) :=
  (BitVec (width + 3) × BitVec (width + 3)) ×
    (((BitVec width.size × BitVec width.size) × (BitVec width.size × BitVec width.size)) ×
      (((Bool × Bool) × (Bool × Bool)) × Bool))

/-- Group and ungroup every named register field without changing any physical bit. -/
def registerTupleEquiv (width : Nat) : Registers width ≃ RegisterTuple width where
  toFun state := ((state.firstWord, state.secondWord),
    (((state.coefficientLength, state.quotientLength), (state.divisorLength, state.shift)),
      (((state.flags.first, state.flags.second), (state.flags.sign, state.flags.iteration)),
        state.control)))
  invFun state :=
    { firstWord := state.1.1
      secondWord := state.1.2
      coefficientLength := state.2.1.1.1
      quotientLength := state.2.1.1.2
      divisorLength := state.2.1.2.1
      shift := state.2.1.2.2
      flags := ⟨state.2.2.1.1.1, state.2.2.1.1.2, state.2.2.1.2.1, state.2.2.1.2.2⟩
      control := state.2.2.2 }
  left_inv := by
    rintro ⟨first, second, coefficient, quotient, divisor, shift, ⟨p1, p2, sign, iter⟩, control⟩
    rfl
  right_inv := by
    rintro ⟨⟨first, second⟩, ⟨⟨⟨coefficient, quotient⟩, ⟨divisor, shift⟩⟩,
      ⟨⟨⟨p1, p2⟩, ⟨sign, iter⟩⟩, control⟩⟩⟩
    rfl

/-- Every finite word uses its actual unsigned binary label, including zero width. -/
@[implicit_reducible]
def wordEncoding (width : Nat) : BinaryLabelEncoding (BitVec width) :=
  BinaryLabelEncoding.ofEquiv BitVec.equivFin.toEquiv

@[implicit_reducible]
def wordPairEncoding (width : Nat) :
    BinaryLabelEncoding (BitVec (width + 3) × BitVec (width + 3)) :=
  BinaryLabelEncoding.prod (wordEncoding (width + 3)) (wordEncoding (width + 3))

@[implicit_reducible]
def lengthPairEncoding (width : Nat) :
    BinaryLabelEncoding (BitVec width.size × BitVec width.size) :=
  BinaryLabelEncoding.prod (wordEncoding width.size) (wordEncoding width.size)

@[implicit_reducible]
def lengthEncoding (width : Nat) : BinaryLabelEncoding
    ((BitVec width.size × BitVec width.size) × (BitVec width.size × BitVec width.size)) :=
  BinaryLabelEncoding.prod (lengthPairEncoding width) (lengthPairEncoding width)

@[implicit_reducible]
def flagPairEncoding : BinaryLabelEncoding (Bool × Bool) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool

@[implicit_reducible]
def flagEncoding : BinaryLabelEncoding ((Bool × Bool) × (Bool × Bool)) :=
  BinaryLabelEncoding.prod flagPairEncoding flagPairEncoding

@[implicit_reducible]
def controlEncoding : BinaryLabelEncoding (((Bool × Bool) × (Bool × Bool)) × Bool) :=
  BinaryLabelEncoding.prod flagEncoding BinaryLabelEncoding.bool

@[implicit_reducible]
def tailEncoding (width : Nat) : BinaryLabelEncoding
    (((BitVec width.size × BitVec width.size) × (BitVec width.size × BitVec width.size)) ×
      (((Bool × Bool) × (Bool × Bool)) × Bool)) :=
  BinaryLabelEncoding.prod (lengthEncoding width) controlEncoding

@[implicit_reducible]
def tupleEncoding (width : Nat) : BinaryLabelEncoding (RegisterTuple width) :=
  BinaryLabelEncoding.prod (wordPairEncoding width) (tailEncoding width)

/-- Exact binary encoding of all declared source fields; no field is hidden or allocated here. -/
@[implicit_reducible]
def encoding (width : Nat) : BinaryLabelEncoding (Registers width) :=
  (tupleEncoding width).relabel (registerTupleEquiv width)

/-- The width counts exactly the present two words, four length fields, and five control wires. -/
theorem encoding_width (width : Nat) :
    (encoding width).width = 2 * (width + 3) + 4 * width.size + 5 := by
  change ((width + 3) + (width + 3)) +
    (((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + (1 + 1) + 1)) = _
  omega

private theorem prod_surjective {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (leftTotal : Function.Surjective left.encode) (rightTotal : Function.Surjective right.encode) :
    Function.Surjective (BinaryLabelEncoding.prod left right).encode := by
  intro label
  obtain ⟨⟨leftLabel, rightLabel⟩, rfl⟩ :=
    (prodEquiv (m := left.width) (n := right.width)).surjective label
  obtain ⟨leftValue, rfl⟩ := leftTotal leftLabel
  obtain ⟨rightValue, rfl⟩ := rightTotal rightLabel
  exact ⟨(leftValue, rightValue), rfl⟩

private theorem bool_surjective : Function.Surjective BinaryLabelEncoding.bool.encode := by
  intro label
  obtain ⟨value, rfl⟩ := finTwoEquiv.symm.surjective label
  refine ⟨value, ?_⟩
  cases value <;> rfl

private theorem word_surjective (width : Nat) : Function.Surjective (wordEncoding width).encode :=
  BitVec.equivFin.toEquiv.surjective

/-- Every binary tuple label decodes to every declared finite register field. -/
theorem tupleEncoding_surjective (width : Nat) :
    Function.Surjective (tupleEncoding width).encode :=
  prod_surjective _ _
    (prod_surjective _ _ (word_surjective _) (word_surjective _))
    (prod_surjective _ _
      (prod_surjective _ _
        (prod_surjective _ _ (word_surjective _) (word_surjective _))
        (prod_surjective _ _ (word_surjective _) (word_surjective _)))
      (prod_surjective _ _
        (prod_surjective _ _
          (prod_surjective _ _ bool_surjective bool_surjective)
          (prod_surjective _ _ bool_surjective bool_surjective)) bool_surjective))

/-- The native encoding covers every computational-basis label, not just admissible EEA states. -/
theorem encoding_surjective (width : Nat) : Function.Surjective (encoding width).encode := by
  intro label
  obtain ⟨tuple, encoded⟩ := tupleEncoding_surjective width label
  refine ⟨(registerTupleEquiv width).symm tuple, ?_⟩
  change (tupleEncoding width).encode
    (registerTupleEquiv width ((registerTupleEquiv width).symm tuple)) = label
  rw [Equiv.apply_symm_apply]
  exact encoded

/-- Read exactly the previously proved finite terminal-frame coordinates from the full registers. -/
def Registers.frame {width : Nat} (state : Registers width) :
    TerminalTail.Frame (width + 3) width.size :=
  ⟨state.firstWord, state.secondWord, state.shift, state.flags⟩

/-- Replace only the existing frame fields while preserving all remaining declared registers. -/
def Registers.withFrame {width : Nat} (state : Registers width)
    (frame : TerminalTail.Frame (width + 3) width.size) : Registers width :=
  { state with
    firstWord := frame.firstWord
    secondWord := frame.secondWord
    shift := frame.shift
    flags := frame.flags }

theorem registers_frame_withFrame {width : Nat} (state : Registers width)
    (frame : TerminalTail.Frame (width + 3) width.size) :
    (state.withFrame frame).frame = frame := by
  cases frame
  rfl

theorem registers_withFrame_frame {width : Nat} (state : Registers width) :
    state.withFrame state.frame = state := by
  cases state
  rfl

/-- The frame projection never consumes the actual coefficient/quotient/divisor lengths or Ctrl. -/
theorem registers_withFrame_retained {width : Nat} (state : Registers width)
    (frame : TerminalTail.Frame (width + 3) width.size) :
    (state.withFrame frame).coefficientLength = state.coefficientLength ∧
      (state.withFrame frame).quotientLength = state.quotientLength ∧
      (state.withFrame frame).divisorLength = state.divisorLength ∧
      (state.withFrame frame).control = state.control := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA
