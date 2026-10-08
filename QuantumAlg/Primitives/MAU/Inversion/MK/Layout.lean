/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule.ZeroTestValue
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.NumberTheory.Binary.GCD.FixedRound

/-!
# Fixed-round inversion layout

This focused leaf is part of the exact fixed-round binary-GCD inversion
realization.  It is exported only through the canonical `MAU.Inversion.MK`
aggregate.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-- Canonical binary label encoding for a raw word label. -/
@[implicit_reducible]
def wordEncoding (width : Nat) : BinaryLabelEncoding (Word width) :=
  BinaryLabelEncoding.finIdentity width

/-- In-range bit formula for width-preserving addition of local finite words.
The carry is stated in `left,right` order to match the VBE carry recurrence. -/
theorem word_add_testBit_eq_xor3
    (width : Nat) (left right : Word width) (bit : Fin width) :
    (right + left).val.testBit bit.val =
      ((right.val.testBit bit.val ^^ left.val.testBit bit.val) ^^
        Nat.BinaryArithmetic.natAddCarry
          left.val right.val bit.val) := by
  rw [Fin.val_add]
  rw [Nat.testBit_mod_two_pow]
  simp only [Fin.is_lt, decide_true, Bool.true_and, Bool.bne_assoc]
  rw [Nat.BinaryArithmetic.testBit_add_eq_xor3]
  rw [Nat.BinaryArithmetic.natAddCarry_comm
    right.val left.val bit.val]
  simp

/-- Registers of one fixed-round Montgomery--Kaliski compute workspace.  The
field order mirrors the public RNSL17 circuit lines: `u`, `v`, comparison
ancilla, `s`, `r`, two scratch ancillas, the stored `m_i` history family,
active/counter flag `f`, and counter `k` [RNSL17, ECDLP.tex:425-475].  The
counter width is a parameter here; the source uses an `O(log n)` counter, while
the later concrete resource theorem must select the exact finite width it
implements [RNSL17, ECDLP.tex:430-442]. -/
structure Registers (n counterWidth : Nat) where
  /-- `u` binary-GCD register. -/
  u : Word n
  /-- `v` binary-GCD register. -/
  v : Word n
  /-- Comparison/subtraction ancilla used to dispatch odd branches. -/
  compare : Bool
  /-- `s` coefficient register, represented with `n+1` bits. -/
  sCoeff : Word (n + 1)
  /-- `r` coefficient register, represented with `n+1` bits. -/
  rCoeff : Word (n + 1)
  /-- First scratch ancilla from the round circuit. -/
  scratchA : Bool
  /-- Second scratch ancilla from the round circuit. -/
  scratchB : Bool
  /-- Packed family of the `2n` stored per-round branch-history bits `m_i`. -/
  history : Word (2 * n)
  /-- Active/counter flag `f`. -/
  active : Bool
  /-- Padding/termination counter `k`. -/
  counter : Word counterWidth
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprRegisters.repr

/-- Product view used by the register encoding. -/
abbrev RegisterTuple (n counterWidth : Nat) :=
  Word n ×
    (Word n ×
      (Bool ×
        (Word (n + 1) ×
          (Word (n + 1) ×
            (Bool ×
              (Bool ×
                (Word (2 * n) ×
                  (Bool × Word counterWidth))))))))

/-- Equivalence between named Montgomery--Kaliski registers and the packed
product field order. -/
def registerTupleEquiv (n counterWidth : Nat) :
    Registers n counterWidth ≃ RegisterTuple n counterWidth where
  toFun := fun r =>
    (r.u, (r.v, (r.compare, (r.sCoeff, (r.rCoeff, (r.scratchA,
      (r.scratchB, (r.history, (r.active, r.counter)))))))))
  invFun := fun x =>
    { u := x.1
      v := x.2.1
      compare := x.2.2.1
      sCoeff := x.2.2.2.1
      rCoeff := x.2.2.2.2.1
      scratchA := x.2.2.2.2.2.1
      scratchB := x.2.2.2.2.2.2.1
      history := x.2.2.2.2.2.2.2.1
      active := x.2.2.2.2.2.2.2.2.1
      counter := x.2.2.2.2.2.2.2.2.2 }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro x
    rcases x with ⟨u, rest⟩
    rcases rest with ⟨v, rest⟩
    rcases rest with ⟨compare, rest⟩
    rcases rest with ⟨sCoeff, rest⟩
    rcases rest with ⟨rCoeff, rest⟩
    rcases rest with ⟨scratchA, rest⟩
    rcases rest with ⟨scratchB, rest⟩
    rcases rest with ⟨history, rest⟩
    rcases rest with ⟨active, counter⟩
    rfl

/-- Product-field encoding for the finite Montgomery--Kaliski workspace. -/
@[implicit_reducible]
def registerTupleEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegisterTuple n counterWidth) :=
  BinaryLabelEncoding.prod (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n)
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        (BinaryLabelEncoding.prod (wordEncoding (n + 1))
          (BinaryLabelEncoding.prod (wordEncoding (n + 1))
            (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
              (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
                (BinaryLabelEncoding.prod (wordEncoding (2 * n))
                  (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
                    (wordEncoding counterWidth)))))))))

/-- Faithful finite binary encoding of the Montgomery--Kaliski compute
workspace. -/
@[implicit_reducible]
def registerEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (Registers n counterWidth) :=
  (registerTupleEncoding n counterWidth).relabel
    (registerTupleEquiv n counterWidth)

@[simp] theorem wordEncoding_width (width : Nat) :
    (wordEncoding width).width = width :=
  rfl

@[simp] theorem registerTupleEncoding_width (n counterWidth : Nat) :
    (registerTupleEncoding n counterWidth).width =
      n + (n + (1 + ((n + 1) + ((n + 1) + (1 + (1 +
        ((2 * n) + (1 + counterWidth)))))))) :=
  rfl

@[simp] theorem registerEncoding_width (n counterWidth : Nat) :
    (registerEncoding n counterWidth).width =
      n + (n + (1 + ((n + 1) + ((n + 1) + (1 + (1 +
        ((2 * n) + (1 + counterWidth)))))))) :=
  rfl

/-! ## Comparison work layout -/

/-- Extra clean work bits for the gate-level word comparator.  The RNSL17 odd
branches need a comparison between `u` and `v`; this work register records the
finite borrow/carry chain workspace separately from the main
Montgomery--Kaliski registers so the comparator slices and the later
full-workspace integration can share one explicit layout
[RNSL17, ECDLP.tex:399-421,468-475]. -/
structure ComparisonWork (n : Nat) where
  /-- Packed comparator borrow/carry work bits. -/
  carry : Word n
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprComparisonWork.repr

/-- Product view of the comparison work register. -/
abbrev ComparisonWorkTuple (n : Nat) := Word n

/-- Equivalence between named comparison work and its packed word. -/
def comparisonWorkEquiv (n : Nat) :
    ComparisonWork n ≃ ComparisonWorkTuple n where
  toFun := fun work => work.carry
  invFun := fun carry => { carry := carry }
  left_inv := by
    intro work
    cases work
    rfl
  right_inv := by
    intro carry
    rfl

/-- Faithful finite binary encoding of the comparison work bits. -/
@[implicit_reducible]
def comparisonWorkEncoding (n : Nat) :
    BinaryLabelEncoding (ComparisonWork n) :=
  (wordEncoding n).relabel (comparisonWorkEquiv n)

@[simp] theorem comparisonWorkEncoding_width (n : Nat) :
    (comparisonWorkEncoding n).width = n :=
  rfl

/-- Clean all-zero comparison work register. -/
def cleanComparisonWork (n : Nat) : ComparisonWork n where
  carry := 0

/-- Bit lens for one comparison borrow/carry work bit. -/
def comparisonCarryBit (n : Nat) (bit : Fin n) :
    EncodedBit (comparisonWorkEncoding n) :=
  (BinaryLabelEncoding.finIdentityBit n bit).relabel
    (comparisonWorkEquiv n)

/-- Little-endian value-bit lens for one comparison borrow/carry work bit. -/
def comparisonCarryValueBit (n : Nat) (bit : Fin n) :
    EncodedBit (comparisonWorkEncoding n) :=
  comparisonCarryBit n (WireAddress.littleEndianWire bit)

/-- Word lens for the packed comparison borrow/carry work register. -/
def comparisonCarryWord (n : Nat) :
    EncodedBit.Word (comparisonWorkEncoding n) n where
  bit := comparisonCarryBit n

/-- Little-endian word lens for the packed comparison borrow/carry work
register. -/
def comparisonCarryValueWord (n : Nat) :
    EncodedBit.Word (comparisonWorkEncoding n) n where
  bit := comparisonCarryValueBit n

@[simp] theorem comparisonCarryBit_clean (n : Nat) (bit : Fin n) :
    (comparisonCarryBit n bit).get (cleanComparisonWork n) = false := by
  simp [comparisonCarryBit, cleanComparisonWork, comparisonWorkEquiv,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel]

@[simp] theorem comparisonCarryValueBit_clean (n : Nat) (bit : Fin n) :
    (comparisonCarryValueBit n bit).get (cleanComparisonWork n) = false := by
  simp [comparisonCarryValueBit]

/-- Distinct little-endian value-bit indices map to distinct addressed wires. -/
theorem littleEndianWire_ne {n : Nat} {left right : Fin n}
    (h : left ≠ right) :
    WireAddress.littleEndianWire left ≠ WireAddress.littleEndianWire right := by
  intro hw
  apply h
  have hb := congrArg WireAddress.bitIndex hw
  simpa using hb

/-- Full Kaliski register state paired with the comparison-work register. -/
abbrev RegistersWithComparisonWork (n counterWidth : Nat) :=
  Registers n counterWidth × ComparisonWork n

/-- Binary encoding for Kaliski registers paired with comparison work. -/
@[implicit_reducible]
def registersWithComparisonWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithComparisonWork n counterWidth) :=
  BinaryLabelEncoding.prod (registerEncoding n counterWidth)
    (comparisonWorkEncoding n)

@[simp] theorem registersWithComparisonWorkEncoding_width
    (n counterWidth : Nat) :
    (registersWithComparisonWorkEncoding n counterWidth).width =
      (registerEncoding n counterWidth).width + n :=
  rfl

/-- Dedicated carry-work register for coefficient additions on the `n+1`-bit
Kaliski `r/s` words. -/
abbrev CoeffAdderCarryWork (n : Nat) :=
  PlainAdder.Schedule.PowerOfTwo.CarryWork (n + 1)

/-- Dedicated clean carry flag plus carry-work word for coefficient-add slices.
This work object is separate from the comparison/history scratch space. -/
abbrev CoeffAdderWork (n : Nat) :=
  Bool × CoeffAdderCarryWork n

/-- Clean coefficient-adder work: false carry-in and all-zero temporary carry
word. -/
def cleanCoeffAdderWork (n : Nat) : CoeffAdderWork n :=
  (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1))

/-- Encoding for the dedicated coefficient-adder work object. -/
@[implicit_reducible]
def coeffAdderWorkEncoding (n : Nat) :
    BinaryLabelEncoding (CoeffAdderWork n) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (n + 1))

/-- Dedicated carry-work register for the padding-counter incrementer. -/
abbrev CounterIncrementCarryWork (counterWidth : Nat) :=
  PlainAdder.Schedule.PowerOfTwo.CarryWork counterWidth

/-- Dedicated source-one word, clean carry flag, and carry-work word for the
padding-counter incrementer. -/
abbrev CounterIncrementWork (counterWidth : Nat) :=
  Word counterWidth × (Bool × CounterIncrementCarryWork counterWidth)

/-- Clean counter-increment work: source word one, false carry-in, and all-zero
temporary carry work. -/
def cleanCounterIncrementWork (counterWidth : Nat) :
    CounterIncrementWork counterWidth :=
  (1, (false, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork counterWidth))

/-- Encoding for the dedicated counter-increment work object. -/
@[implicit_reducible]
def counterIncrementWorkEncoding (counterWidth : Nat) :
    BinaryLabelEncoding (CounterIncrementWork counterWidth) :=
  BinaryLabelEncoding.prod (wordEncoding counterWidth)
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding counterWidth))

/-- Kaliski registers plus comparison work and one dedicated coefficient-adder
work object. -/
abbrev RegistersWithCoeffAdderWork (n counterWidth : Nat) :=
  RegistersWithComparisonWork n counterWidth × CoeffAdderWork n

/-- Kaliski registers plus one dedicated counter-increment work object. -/
abbrev RegistersWithCounterIncrementWork (n counterWidth : Nat) :=
  Registers n counterWidth × CounterIncrementWork counterWidth

/-- Kaliski registers plus comparison work and dedicated counter-increment work. -/
abbrev RegistersWithDetectorCounterWork (n counterWidth : Nat) :=
  RegistersWithComparisonWork n counterWidth × CounterIncrementWork counterWidth

/-- Kaliski registers plus the comparison, coefficient-adder, and padding
counter-increment work needed by one fixed-round implementation slice. -/
abbrev RegistersWithFullRoundWork (n counterWidth : Nat) :=
  RegistersWithCoeffAdderWork n counterWidth ×
    CounterIncrementWork counterWidth

/-- Full fixed-round workspace with one trailing path bit.  The extra bit is
reserved for reversible routing facts such as the original active flag; it is
not borrowed from counter, comparison, or coefficient-adder work. -/
abbrev RegistersWithFullRoundPathWork (n counterWidth : Nat) :=
  RegistersWithFullRoundWork n counterWidth × Bool

/-- Full fixed-round workspace with a trailing path bit and a separate clean
control-work bit.  The second bit is needed when the path bit controls a
gate-list that may contain Toffoli gates. -/
abbrev RegistersWithFullRoundPathControlWork (n counterWidth : Nat) :=
  RegistersWithFullRoundPathWork n counterWidth × Bool

/-- Encoding for Kaliski registers, comparison work, and dedicated
coefficient-adder work. -/
@[implicit_reducible]
def registersWithCoeffAdderWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithCoeffAdderWork n counterWidth) :=
  BinaryLabelEncoding.prod (registersWithComparisonWorkEncoding n counterWidth)
    (coeffAdderWorkEncoding n)

/-- Encoding for Kaliski registers plus dedicated counter-increment work. -/
@[implicit_reducible]
def registersWithCounterIncrementWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithCounterIncrementWork n counterWidth) :=
  BinaryLabelEncoding.prod (registerEncoding n counterWidth)
    (counterIncrementWorkEncoding counterWidth)

/-- Encoding for Kaliski registers, comparison work, and dedicated
counter-increment work. -/
@[implicit_reducible]
def registersWithDetectorCounterWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithDetectorCounterWork n counterWidth) :=
  BinaryLabelEncoding.prod (registersWithComparisonWorkEncoding n counterWidth)
    (counterIncrementWorkEncoding counterWidth)

/-- Encoding for Kaliski registers, comparison work, coefficient-adder work,
and dedicated counter-increment work in the order used by the active-round
workspace, with the counter work appended. -/
@[implicit_reducible]
def registersWithFullRoundWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithFullRoundWork n counterWidth) :=
  BinaryLabelEncoding.prod (registersWithCoeffAdderWorkEncoding n counterWidth)
    (counterIncrementWorkEncoding counterWidth)

/-- Encoding for the full fixed-round workspace with one trailing path bit. -/
@[implicit_reducible]
def registersWithFullRoundPathWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithFullRoundPathWork n counterWidth) :=
  BinaryLabelEncoding.prod (registersWithFullRoundWorkEncoding n counterWidth)
    BinaryLabelEncoding.bool

/-- Encoding for the full fixed-round workspace with path and control-work
bits. -/
@[implicit_reducible]
def registersWithFullRoundPathControlWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithFullRoundPathControlWork n counterWidth) :=
  BinaryLabelEncoding.prod
    (registersWithFullRoundPathWorkEncoding n counterWidth)
    BinaryLabelEncoding.bool

/-- Clean work object for the full fixed-round workspace. -/
def cleanFullRoundWork (n counterWidth : Nat) :
    CoeffAdderWork n × CounterIncrementWork counterWidth :=
  (cleanCoeffAdderWork n, cleanCounterIncrementWork counterWidth)

/-- Clean work object for the full fixed-round workspace plus path bit. -/
def cleanFullRoundPathWork (n counterWidth : Nat) :
    (CoeffAdderWork n × CounterIncrementWork counterWidth) × Bool :=
  (cleanFullRoundWork n counterWidth, false)

/-- Clean work object for the full fixed-round workspace plus path/control
bits. -/
def cleanFullRoundPathControlWork (n counterWidth : Nat) :
    ((CoeffAdderWork n × CounterIncrementWork counterWidth) × Bool) × Bool :=
  (cleanFullRoundPathWork n counterWidth, false)

/-- Pair a clean full-round path-work object with a Kaliski register state. -/
def withCleanFullRoundPathWork (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    RegistersWithFullRoundPathWork n counterWidth :=
  ((((x, cleanComparisonWork n), cleanCoeffAdderWork n),
      cleanCounterIncrementWork counterWidth), false)

/-- Pair a clean full-round path/control-work object with a Kaliski register
state. -/
def withCleanFullRoundPathControlWork (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    RegistersWithFullRoundPathControlWork n counterWidth :=
  (withCleanFullRoundPathWork n counterWidth x, false)

/-- Lift a full-round workspace step over the trailing path bit, preserving
that bit. -/
def liftFullRoundWorkStepToPathWork
    (n counterWidth : Nat)
    (step :
      RegistersWithFullRoundWork n counterWidth ->
        RegistersWithFullRoundWork n counterWidth) :
    RegistersWithFullRoundPathWork n counterWidth ->
      RegistersWithFullRoundPathWork n counterWidth :=
  fun x => (step x.1, x.2)

/-- Lift an actual full-round workspace circuit over the trailing path bit. -/
def liftFullRoundWorkProgramToPathWork
    (n counterWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundWorkEncoding n counterWidth).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundPathWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix BinaryLabelEncoding.bool.width program

/-- Actual-circuit realization is preserved when adding the path bit. -/
theorem liftFullRoundWorkProgramToPathWork_realizes
    (n counterWidth : Nat)
    {step : RegistersWithFullRoundWork n counterWidth ->
      RegistersWithFullRoundWork n counterWidth}
    {program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundWorkEncoding n counterWidth).width).toQuantum}
    (h : UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding n counterWidth) program step) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathWorkEncoding n counterWidth)
      (liftFullRoundWorkProgramToPathWork n counterWidth program)
      (liftFullRoundWorkStepToPathWork n counterWidth step) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := BinaryLabelEncoding.bool) h

/-- Lift a path-work step over the trailing control-work bit, preserving that
bit. -/
def liftFullRoundPathWorkStepToControlWork
    (n counterWidth : Nat)
    (step :
      RegistersWithFullRoundPathWork n counterWidth ->
        RegistersWithFullRoundPathWork n counterWidth) :
    RegistersWithFullRoundPathControlWork n counterWidth ->
      RegistersWithFullRoundPathControlWork n counterWidth :=
  fun x => (step x.1, x.2)

/-- Lift an actual path-work circuit over the trailing control-work bit. -/
def liftFullRoundPathWorkProgramToControlWork
    (n counterWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundPathWorkEncoding n counterWidth).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundPathControlWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix BinaryLabelEncoding.bool.width program

/-- Actual-circuit realization is preserved when adding control work. -/
theorem liftFullRoundPathWorkProgramToControlWork_realizes
    (n counterWidth : Nat)
    {step : RegistersWithFullRoundPathWork n counterWidth ->
      RegistersWithFullRoundPathWork n counterWidth}
    {program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundPathWorkEncoding n counterWidth).width).toQuantum}
    (h : UnitaryCircuit.Realizes
      (registersWithFullRoundPathWorkEncoding n counterWidth) program step) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding n counterWidth)
      (liftFullRoundPathWorkProgramToControlWork n counterWidth program)
      (liftFullRoundPathWorkStepToControlWork n counterWidth step) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := BinaryLabelEncoding.bool) h

/-- Lift a full-round workspace step over path and control-work bits. -/
def liftFullRoundWorkStepToPathControlWork
    (n counterWidth : Nat)
    (step :
      RegistersWithFullRoundWork n counterWidth ->
        RegistersWithFullRoundWork n counterWidth) :
    RegistersWithFullRoundPathControlWork n counterWidth ->
      RegistersWithFullRoundPathControlWork n counterWidth :=
  liftFullRoundPathWorkStepToControlWork n counterWidth
    (liftFullRoundWorkStepToPathWork n counterWidth step)

/-- Lift an actual full-round circuit over path and control-work bits. -/
def liftFullRoundWorkProgramToPathControlWork
    (n counterWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundWorkEncoding n counterWidth).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundPathControlWorkEncoding n counterWidth).width).toQuantum :=
  liftFullRoundPathWorkProgramToControlWork n counterWidth
    (liftFullRoundWorkProgramToPathWork n counterWidth program)

/-- Actual-circuit realization is preserved across both appended work bits. -/
theorem liftFullRoundWorkProgramToPathControlWork_realizes
    (n counterWidth : Nat)
    {step : RegistersWithFullRoundWork n counterWidth ->
      RegistersWithFullRoundWork n counterWidth}
    {program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundWorkEncoding n counterWidth).width).toQuantum}
    (h : UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding n counterWidth) program step) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding n counterWidth)
      (liftFullRoundWorkProgramToPathControlWork n counterWidth program)
      (liftFullRoundWorkStepToPathControlWork n counterWidth step) :=
  liftFullRoundPathWorkProgramToControlWork_realizes n counterWidth
    (liftFullRoundWorkProgramToPathWork_realizes n counterWidth h)

/-- Reassociate the full fixed-round workspace so detector/counter programs can
act on their native `(registers + comparison + counter)` layout while
preserving the coefficient-adder work. -/
def fullRoundWorkDetectorEquiv (n counterWidth : Nat) :
    RegistersWithFullRoundWork n counterWidth ≃
      RegistersWithDetectorCounterWork n counterWidth × CoeffAdderWork n where
  toFun := fun x => ((x.1.1, x.2), x.1.2)
  invFun := fun x => ((x.1.1, x.2), x.1.2)
  left_inv := by
    intro x
    rcases x with ⟨⟨regs, coeffWork⟩, counterWork⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨regs, counterWork⟩, coeffWork⟩
    rfl

/-- Lift a Kaliski register bit over the trailing comparison-work register. -/
def liftRegisterBitToComparisonWork
    (n counterWidth : Nat)
    (bit : EncodedBit (registerEncoding n counterWidth)) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit (registerEncoding n counterWidth)
    (comparisonWorkEncoding n) bit

/-- Lift a comparison-work bit over the leading Kaliski registers. -/
def liftComparisonWorkBit
    (n counterWidth : Nat)
    (bit : EncodedBit (comparisonWorkEncoding n)) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (registerEncoding n counterWidth)
    (comparisonWorkEncoding n) bit

/-- Lifted comparison-work carry/borrow bit. -/
def liftedComparisonCarryBit
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftComparisonWorkBit n counterWidth (comparisonCarryValueBit n bit)

/-- Lift a register-plus-comparison bit over the dedicated coefficient-adder
work object. -/
def liftComparisonStateBitToCoeffAdderWork
    (n counterWidth : Nat)
    (bit : EncodedBit (registersWithComparisonWorkEncoding n counterWidth)) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (registersWithComparisonWorkEncoding n counterWidth)
    (coeffAdderWorkEncoding n) bit

/-- Lift a coefficient-adder work bit over the leading register-plus-comparison
state. -/
def liftCoeffAdderWorkBit
    (n counterWidth : Nat)
    (bit : EncodedBit (coeffAdderWorkEncoding n)) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit
    (registersWithComparisonWorkEncoding n counterWidth)
    (coeffAdderWorkEncoding n) bit

/-- Lift a Kaliski register bit over the dedicated counter-increment work
object. -/
def liftRegisterBitToCounterIncrementWork
    (n counterWidth : Nat)
    (bit : EncodedBit (registerEncoding n counterWidth)) :
    EncodedBit (registersWithCounterIncrementWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit (registerEncoding n counterWidth)
    (counterIncrementWorkEncoding counterWidth) bit

/-- Lift a counter-increment work bit over the leading Kaliski registers. -/
def liftCounterIncrementWorkBit
    (n counterWidth : Nat)
    (bit : EncodedBit (counterIncrementWorkEncoding counterWidth)) :
    EncodedBit (registersWithCounterIncrementWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (registerEncoding n counterWidth)
    (counterIncrementWorkEncoding counterWidth) bit

/-- Lift a register-plus-comparison bit over the trailing counter-increment work
object. -/
def liftComparisonStateBitToDetectorCounterWork
    (n counterWidth : Nat)
    (bit : EncodedBit (registersWithComparisonWorkEncoding n counterWidth)) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (registersWithComparisonWorkEncoding n counterWidth)
    (counterIncrementWorkEncoding counterWidth) bit

/-- Lift a counter-increment work bit over the leading register-plus-comparison
state. -/
def liftCounterIncrementWorkBitToDetectorCounterWork
    (n counterWidth : Nat)
    (bit : EncodedBit (counterIncrementWorkEncoding counterWidth)) :
    EncodedBit (registersWithDetectorCounterWorkEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit
    (registersWithComparisonWorkEncoding n counterWidth)
    (counterIncrementWorkEncoding counterWidth) bit

/-- Lift a register-plus-comparison-plus-coefficient-work bit over the trailing
counter-increment work object in the full fixed-round workspace. -/
def liftCoeffAdderStateBitToFullRoundWork
    (tail counterWidth : Nat)
    (bit :
      EncodedBit
        (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)) :
    EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth) bit

/-- Lift a counter-increment work bit over the leading coefficient-work state
in the full fixed-round workspace. -/
def liftCounterIncrementWorkBitToFullRoundWork
    (tail counterWidth : Nat)
    (bit : EncodedBit (counterIncrementWorkEncoding counterWidth)) :
    EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodRightBit
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth) bit

/-- Lift a full-round-work bit over the trailing path bit. -/
def liftFullRoundWorkBitToPathWork
    (tail counterWidth : Nat)
    (bit :
      EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :
    EncodedBit
      (registersWithFullRoundPathWorkEncoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (registersWithFullRoundWorkEncoding tail.succ counterWidth)
    BinaryLabelEncoding.bool bit

/-- Trailing path bit for the extended full-round workspace. -/
def fullRoundPathWorkPathBit (tail counterWidth : Nat) :
    EncodedBit
      (registersWithFullRoundPathWorkEncoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodRightBit
    (registersWithFullRoundWorkEncoding tail.succ counterWidth)
    BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit

/-- Lift a path-work bit over the trailing control-work bit. -/
def liftFullRoundPathWorkBitToControlWork
    (tail counterWidth : Nat)
    (bit :
      EncodedBit
        (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)) :
    EncodedBit
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
    BinaryLabelEncoding.bool bit

/-- Lift a full-round-work bit over the trailing path and control-work bits. -/
def liftFullRoundWorkBitToPathControlWork
    (tail counterWidth : Nat)
    (bit :
      EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :
    EncodedBit
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth) :=
  liftFullRoundPathWorkBitToControlWork tail counterWidth
    (liftFullRoundWorkBitToPathWork tail counterWidth bit)

/-- Path bit in the path/control-work layout. -/
def fullRoundPathControlWorkPathBit (tail counterWidth : Nat) :
    EncodedBit
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth) :=
  liftFullRoundPathWorkBitToControlWork tail counterWidth
    (fullRoundPathWorkPathBit tail counterWidth)

/-- Clean control-work bit in the path/control-work layout. -/
def fullRoundPathControlWorkControlWorkBit (tail counterWidth : Nat) :
    EncodedBit
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodRightBit
    (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
    BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit

/-- An encoded bit lifted from the left side of a product is wire-disjoint from
an encoded bit lifted from the right side. -/
theorem prodLeftBit_prodRightBit_wire_ne
    {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right)
    (leftBit : EncodedBit left) (rightBit : EncodedBit right) :
    (BinaryLabelEncoding.prodLeftBit left right leftBit).wire ≠
      (BinaryLabelEncoding.prodRightBit left right rightBit).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  have hlt : leftBit.wire.val < left.width := leftBit.wire.isLt
  simp [BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- Lifting a gate to the left side of a product makes it disjoint from any
right-side bit. -/
theorem gateSpecProdLeft_bitDisjoint_prodRightBit
    {Left Right : Type} {left : BinaryLabelEncoding Left}
    (right : BinaryLabelEncoding Right)
    (observed : EncodedBit right)
    (gate : EncodedBit.GateSpec left) :
    EncodedBit.GateSpec.bitDisjoint
      (BinaryLabelEncoding.prodRightBit left right observed)
      (EncodedBit.GateSpec.prodLeft right gate) := by
  cases gate with
  | x target =>
      exact prodLeftBit_prodRightBit_wire_ne left right target observed
  | cnot control target hct =>
      exact
        ⟨prodLeftBit_prodRightBit_wire_ne left right control observed,
          prodLeftBit_prodRightBit_wire_ne left right target observed⟩
  | toffoli controlA controlB target hab ha hb =>
      exact
        ⟨prodLeftBit_prodRightBit_wire_ne left right controlA observed,
          prodLeftBit_prodRightBit_wire_ne left right controlB observed,
          prodLeftBit_prodRightBit_wire_ne left right target observed⟩

/-- Left-product lifting preserves disjointness facts. -/
theorem gateSpecProdLeft_bitDisjoint_prodLeftBit
    {Left Right : Type} {left : BinaryLabelEncoding Left}
    (right : BinaryLabelEncoding Right)
    (observed : EncodedBit left)
    (gate : EncodedBit.GateSpec left)
    (h :
      EncodedBit.GateSpec.bitDisjoint observed gate) :
    EncodedBit.GateSpec.bitDisjoint
      (BinaryLabelEncoding.prodLeftBit left right observed)
      (EncodedBit.GateSpec.prodLeft right gate) := by
  cases gate with
  | x target =>
      exact EncodedBit.GateSpec.prodLeftWire_ne right h
  | cnot control target hct =>
      exact
        ⟨EncodedBit.GateSpec.prodLeftWire_ne right h.1,
          EncodedBit.GateSpec.prodLeftWire_ne right h.2⟩
  | toffoli controlA controlB target hab ha hb =>
      exact
        ⟨EncodedBit.GateSpec.prodLeftWire_ne right h.1,
          EncodedBit.GateSpec.prodLeftWire_ne right h.2.1,
          EncodedBit.GateSpec.prodLeftWire_ne right h.2.2⟩

/-- Source-one work word bit for the padding-counter incrementer. -/
def counterIncrementSourceBit (counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (counterIncrementWorkEncoding counterWidth) :=
  BinaryLabelEncoding.prodLeftBit (wordEncoding counterWidth)
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding counterWidth))
    (BinaryLabelEncoding.finIdentityBit counterWidth
      (WireAddress.littleEndianWire bit))

/-- Carry-in flag for the padding-counter incrementer. -/
def counterIncrementCarryInBit (counterWidth : Nat) :
    EncodedBit (counterIncrementWorkEncoding counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding counterWidth)
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding counterWidth))
    (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding counterWidth)
      BinaryLabelEncoding.boolBit)

/-- Temporary carry-work bit for the padding-counter incrementer. -/
def counterIncrementCarryWorkBit
    (counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (counterIncrementWorkEncoding counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding counterWidth)
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding counterWidth))
    (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding counterWidth)
      (BinaryLabelEncoding.finIdentityBit (counterWidth - 1) bit))

/-- Full-round source-one work bit for the padding-counter incrementer. -/
def fullRoundWorkCounterSourceBit
    (tail counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth) :=
  liftCounterIncrementWorkBitToFullRoundWork tail counterWidth
    (counterIncrementSourceBit counterWidth bit)

/-- Full-round carry-in flag for the padding-counter incrementer. -/
def fullRoundWorkCounterCarryInBit (tail counterWidth : Nat) :
    EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth) :=
  liftCounterIncrementWorkBitToFullRoundWork tail counterWidth
    (counterIncrementCarryInBit counterWidth)

/-- Full-round temporary carry-work bit for the padding-counter incrementer. -/
def fullRoundWorkCounterCarryWorkBit
    (tail counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth) :=
  liftCounterIncrementWorkBitToFullRoundWork tail counterWidth
    (counterIncrementCarryWorkBit counterWidth bit)

/-- Lifted source-one work word bit for the padding-counter incrementer. -/
def liftedCounterIncrementSourceBit
    (n counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (registersWithCounterIncrementWorkEncoding n counterWidth) :=
  liftCounterIncrementWorkBit n counterWidth
    (counterIncrementSourceBit counterWidth bit)

/-- Lifted carry-in flag for the padding-counter incrementer. -/
def liftedCounterIncrementCarryInBit (n counterWidth : Nat) :
    EncodedBit (registersWithCounterIncrementWorkEncoding n counterWidth) :=
  liftCounterIncrementWorkBit n counterWidth
    (counterIncrementCarryInBit counterWidth)

/-- Lifted temporary carry-work bit for the padding-counter incrementer. -/
def liftedCounterIncrementCarryWorkBit
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (registersWithCounterIncrementWorkEncoding n counterWidth) :=
  liftCounterIncrementWorkBit n counterWidth
    (counterIncrementCarryWorkBit counterWidth bit)

/-- Lifted source-one work word for the padding-counter incrementer. -/
def liftedCounterIncrementSourceWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCounterIncrementWorkEncoding n counterWidth)
      counterWidth where
  bit := liftedCounterIncrementSourceBit n counterWidth

/-- Lifted temporary carry-work word for the padding-counter incrementer. -/
def liftedCounterIncrementCarryWorkWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCounterIncrementWorkEncoding n counterWidth)
      (counterWidth - 1) where
  bit := liftedCounterIncrementCarryWorkBit n counterWidth

/-- Carry-in flag for the dedicated coefficient-adder work object. -/
def coeffAdderCarryInWorkBit (n : Nat) :
    EncodedBit (coeffAdderWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
    (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (n + 1))
    BinaryLabelEncoding.boolBit

/-- Temporary carry-work bit for the dedicated coefficient-adder work object. -/
def coeffAdderCarryWorkBit
    (n : Nat) (bit : Fin ((n + 1) - 1)) :
    EncodedBit (coeffAdderWorkEncoding n) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (n + 1))
    (BinaryLabelEncoding.finIdentityBit ((n + 1) - 1) bit)

/-- Lifted carry-in flag for the coefficient-adder layout. -/
def liftedCoeffAdderCarryInBit (n counterWidth : Nat) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftCoeffAdderWorkBit n counterWidth (coeffAdderCarryInWorkBit n)

/-- Lifted temporary carry-work bit for the coefficient-adder layout. -/
def liftedCoeffAdderCarryWorkBit
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1)) :
    EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth) :=
  liftCoeffAdderWorkBit n counterWidth (coeffAdderCarryWorkBit n bit)

/-- Lifted temporary carry-work word for the coefficient-adder layout. -/
def liftedCoeffAdderCarryWorkWord (n counterWidth : Nat) :
    EncodedBit.Word
      (registersWithCoeffAdderWorkEncoding n counterWidth) ((n + 1) - 1) where
  bit := liftedCoeffAdderCarryWorkBit n counterWidth

/-! ## Field lenses for future base-gate programs -/

namespace RegisterBits

/-- Encoding of the active flag and padding counter suffix. -/
@[implicit_reducible]
def activeCounterEncoding (counterWidth : Nat) :
    BinaryLabelEncoding (Bool × Word counterWidth) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool (wordEncoding counterWidth)

/-- Encoding suffix after the `scratchB` bit. -/
def tailAfterScratchB (n counterWidth : Nat) :
    BinaryLabelEncoding (Word (2 * n) × (Bool × Word counterWidth)) :=
  BinaryLabelEncoding.prod (wordEncoding (2 * n))
    (activeCounterEncoding counterWidth)

/-- Encoding suffix after the `scratchA` bit. -/
def tailAfterScratchA (n counterWidth : Nat) :
    BinaryLabelEncoding
      (Bool × (Word (2 * n) × (Bool × Word counterWidth))) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (tailAfterScratchB n counterWidth)

/-- Encoding suffix after the `r` coefficient word. -/
def tailAfterR (n counterWidth : Nat) :
    BinaryLabelEncoding
      (Bool × (Bool × (Word (2 * n) × (Bool × Word counterWidth)))) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (tailAfterScratchA n counterWidth)

/-- Encoding suffix after the `s` coefficient word. -/
def tailAfterS (n counterWidth : Nat) :
    BinaryLabelEncoding
      (Word (n + 1) ×
        (Bool × (Bool × (Word (2 * n) × (Bool × Word counterWidth))))) :=
  BinaryLabelEncoding.prod (wordEncoding (n + 1)) (tailAfterR n counterWidth)

/-- Encoding suffix after the comparison bit. -/
def tailAfterCompare (n counterWidth : Nat) :
    BinaryLabelEncoding
      (Word (n + 1) ×
        (Word (n + 1) ×
          (Bool × (Bool × (Word (2 * n) × (Bool × Word counterWidth)))))) :=
  BinaryLabelEncoding.prod (wordEncoding (n + 1))
    (tailAfterS n counterWidth)

/-- Encoding suffix after the `v` word. -/
def tailAfterV (n counterWidth : Nat) :
    BinaryLabelEncoding
      (Bool ×
        (Word (n + 1) ×
          (Word (n + 1) ×
            (Bool ×
              (Bool × (Word (2 * n) × (Bool × Word counterWidth))))))) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (tailAfterCompare n counterWidth)

/-- Encoding suffix after the `u` word. -/
def tailAfterU (n counterWidth : Nat) :
    BinaryLabelEncoding
      (Word n ×
        (Bool ×
          (Word (n + 1) ×
            (Word (n + 1) ×
              (Bool ×
                (Bool × (Word (2 * n) × (Bool × Word counterWidth)))))))) :=
  BinaryLabelEncoding.prod (wordEncoding n) (tailAfterV n counterWidth)

/-- Tuple-layout bit lens for the `u` register. -/
def tupleUBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.finIdentityBit n bit)

/-- Tuple-layout bit lens for the `v` register. -/
def tupleVBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodLeftBit (wordEncoding n)
      (tailAfterV n counterWidth) (BinaryLabelEncoding.finIdentityBit n bit))

/-- Tuple-layout bit lens for the comparison ancilla. -/
def tupleCompareBit (n counterWidth : Nat) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth) BinaryLabelEncoding.boolBit))

/-- Tuple-layout bit lens for the `s` coefficient word. -/
def tupleSCoeffBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth)
        (BinaryLabelEncoding.prodLeftBit (wordEncoding (n + 1))
          (tailAfterS n counterWidth)
          (BinaryLabelEncoding.finIdentityBit (n + 1) bit))))

/-- Tuple-layout bit lens for the `r` coefficient word. -/
def tupleRCoeffBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth)
        (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
          (tailAfterS n counterWidth)
          (BinaryLabelEncoding.prodLeftBit (wordEncoding (n + 1))
            (tailAfterR n counterWidth)
            (BinaryLabelEncoding.finIdentityBit (n + 1) bit)))))

/-- Tuple-layout bit lens for the first scratch ancilla. -/
def tupleScratchABit (n counterWidth : Nat) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth)
        (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
          (tailAfterS n counterWidth)
          (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
            (tailAfterR n counterWidth)
            (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
              (tailAfterScratchA n counterWidth)
              BinaryLabelEncoding.boolBit)))))

/-- Tuple-layout bit lens for the second scratch ancilla. -/
def tupleScratchBBit (n counterWidth : Nat) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth)
        (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
          (tailAfterS n counterWidth)
          (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
            (tailAfterR n counterWidth)
            (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
              (tailAfterScratchA n counterWidth)
              (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
                (tailAfterScratchB n counterWidth)
                BinaryLabelEncoding.boolBit))))))

/-- Tuple-layout bit lens for the packed branch-history word. -/
def tupleHistoryBit (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth)
        (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
          (tailAfterS n counterWidth)
          (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
            (tailAfterR n counterWidth)
            (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
              (tailAfterScratchA n counterWidth)
              (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
                (tailAfterScratchB n counterWidth)
                (BinaryLabelEncoding.prodLeftBit (wordEncoding (2 * n))
                  (activeCounterEncoding counterWidth)
                  (BinaryLabelEncoding.finIdentityBit (2 * n) bit))))))))

/-- Tuple-layout bit lens for the active flag. -/
def tupleActiveBit (n counterWidth : Nat) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth)
        (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
          (tailAfterS n counterWidth)
          (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
            (tailAfterR n counterWidth)
            (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
              (tailAfterScratchA n counterWidth)
              (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
                (tailAfterScratchB n counterWidth)
                (BinaryLabelEncoding.prodRightBit (wordEncoding (2 * n))
                  (activeCounterEncoding counterWidth)
                  (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
                    (wordEncoding counterWidth)
                    BinaryLabelEncoding.boolBit))))))))

/-- Tuple-layout bit lens for the padding counter. -/
def tupleCounterBit (n counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n) (tailAfterU n counterWidth)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      (tailAfterV n counterWidth)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        (tailAfterCompare n counterWidth)
        (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
          (tailAfterS n counterWidth)
          (BinaryLabelEncoding.prodRightBit (wordEncoding (n + 1))
            (tailAfterR n counterWidth)
            (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
              (tailAfterScratchA n counterWidth)
              (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
                (tailAfterScratchB n counterWidth)
                (BinaryLabelEncoding.prodRightBit (wordEncoding (2 * n))
                  (activeCounterEncoding counterWidth)
                  (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
                    (wordEncoding counterWidth)
                    (BinaryLabelEncoding.finIdentityBit counterWidth bit)))))))))

/-- Register-layout bit lens for the `u` register. -/
def uBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleUBit n counterWidth bit).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the `v` register. -/
def vBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleVBit n counterWidth bit).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the comparison ancilla. -/
def compareBit (n counterWidth : Nat) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleCompareBit n counterWidth).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the `s` coefficient word. -/
def sCoeffBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleSCoeffBit n counterWidth bit).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the `r` coefficient word. -/
def rCoeffBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleRCoeffBit n counterWidth bit).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the first scratch ancilla. -/
def scratchABit (n counterWidth : Nat) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleScratchABit n counterWidth).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the second scratch ancilla. -/
def scratchBBit (n counterWidth : Nat) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleScratchBBit n counterWidth).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the packed branch-history word. -/
def historyBit (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleHistoryBit n counterWidth bit).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the active flag. -/
def activeBit (n counterWidth : Nat) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleActiveBit n counterWidth).relabel (registerTupleEquiv n counterWidth)

/-- Register-layout bit lens for the padding counter. -/
def counterBit (n counterWidth : Nat) (bit : Fin counterWidth) :
    EncodedBit (registerEncoding n counterWidth) :=
  (tupleCounterBit n counterWidth bit).relabel
    (registerTupleEquiv n counterWidth)

/-- Little-endian value-bit lens for the `u` register. -/
def uValueBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registerEncoding n counterWidth) :=
  uBit n counterWidth (WireAddress.littleEndianWire bit)

/-- Little-endian value-bit lens for the `v` register. -/
def vValueBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registerEncoding n counterWidth) :=
  vBit n counterWidth (WireAddress.littleEndianWire bit)

/-- Little-endian value-bit lens for the `s` coefficient register. -/
def sCoeffValueBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (registerEncoding n counterWidth) :=
  sCoeffBit n counterWidth (WireAddress.littleEndianWire bit)

/-- Little-endian value-bit lens for the `r` coefficient register. -/
def rCoeffValueBit (n counterWidth : Nat) (bit : Fin (n + 1)) :
    EncodedBit (registerEncoding n counterWidth) :=
  rCoeffBit n counterWidth (WireAddress.littleEndianWire bit)

/-- Word lens for the `u` register in the packed compute workspace. -/
def uWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) n where
  bit := uBit n counterWidth

/-- Word lens for the `v` register in the packed compute workspace. -/
def vWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) n where
  bit := vBit n counterWidth

/-- Little-endian value-word lens for the `u` register. -/
def uValueWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) n where
  bit := uValueBit n counterWidth

/-- Little-endian value-word lens for the `v` register. -/
def vValueWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) n where
  bit := vValueBit n counterWidth

/-- Word lens for the `s` coefficient register in the packed workspace. -/
def sCoeffWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) (n + 1) where
  bit := sCoeffBit n counterWidth

/-- Word lens for the `r` coefficient register in the packed workspace. -/
def rCoeffWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) (n + 1) where
  bit := rCoeffBit n counterWidth

/-- Little-endian value-word lens for the `s` coefficient register. -/
def sCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) (n + 1) where
  bit := sCoeffValueBit n counterWidth

/-- Little-endian value-word lens for the `r` coefficient register. -/
def rCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) (n + 1) where
  bit := rCoeffValueBit n counterWidth

/-- Word lens for the packed `m_i` branch-history register family. -/
def historyWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) (2 * n) where
  bit := historyBit n counterWidth

/-- Word lens for the padding counter. -/
def counterWord (n counterWidth : Nat) :
    EncodedBit.Word (registerEncoding n counterWidth) counterWidth where
  bit := counterBit n counterWidth

@[simp] theorem uValueBit_get (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (uValueBit n counterWidth bit).get x =
      x.u.val.testBit bit.val := by
  simp [uValueBit, uBit, tupleUBit, registerTupleEquiv, wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, EncodedBit.relabel]

@[simp] theorem vValueBit_get (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (vValueBit n counterWidth bit).get x =
      x.v.val.testBit bit.val := by
  simp [vValueBit, vBit, tupleVBit, registerTupleEquiv, wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]

theorem vValueBit_get_false_of_v_zero
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (hv : x.v.val = 0) :
    (vValueBit n counterWidth bit).get x = false := by
  simp [vValueBit_get, hv]

@[simp] theorem sCoeffValueBit_get
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (sCoeffValueBit n counterWidth bit).get x =
      x.sCoeff.val.testBit bit.val := by
  simp [sCoeffValueBit, sCoeffBit, tupleSCoeffBit, registerTupleEquiv,
    wordEncoding, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel]

@[simp] theorem rCoeffValueBit_get
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (rCoeffValueBit n counterWidth bit).get x =
      x.rCoeff.val.testBit bit.val := by
  simp [rCoeffValueBit, rCoeffBit, tupleRCoeffBit, registerTupleEquiv,
    wordEncoding, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel]

theorem scratchABit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get x = x.scratchA := by
  simp [scratchABit, tupleScratchABit, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]
  rfl

theorem scratchBBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (scratchBBit n counterWidth).get x = x.scratchB := by
  simp [scratchBBit, tupleScratchBBit, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]
  rfl

theorem historyBit_get
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (historyBit n counterWidth bit).get x =
      x.history.val.testBit (WireAddress.bitIndex bit).val := by
  simp [historyBit, tupleHistoryBit, registerTupleEquiv, wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]

theorem activeBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (activeBit n counterWidth).get x = x.active := by
  simp [activeBit, tupleActiveBit, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]
  rfl

@[simp] theorem counterBit_get
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : Registers n counterWidth) :
    (counterBit n counterWidth bit).get x =
      x.counter.val.testBit (WireAddress.bitIndex bit).val := by
  simp [counterBit, tupleCounterBit, registerTupleEquiv, wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel]

@[simp] theorem compareBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (compareBit n counterWidth).get x = x.compare := by
  simp [compareBit, tupleCompareBit, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]
  rfl

/-- The active flag and each stored branch-history bit occupy distinct wires. -/
theorem active_history_wire_ne (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (activeBit n counterWidth).wire ≠ (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, historyBit, tupleActiveBit, tupleHistoryBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The active flag and each padding-counter bit occupy distinct wires. -/
theorem active_counter_wire_ne (n counterWidth : Nat)
    (bit : Fin counterWidth) :
    (activeBit n counterWidth).wire ≠
      (counterBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, counterBit, tupleActiveBit, tupleCounterBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- A `u` word bit and each padding-counter bit occupy distinct wires. -/
theorem u_counter_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (counterIndex : Fin counterWidth) :
    (uBit n counterWidth uIndex).wire ≠
      (counterBit n counterWidth counterIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, counterBit, tupleUBit, tupleCounterBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- A `v` word bit and each padding-counter bit occupy distinct wires. -/
theorem v_counter_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (counterIndex : Fin counterWidth) :
    (vBit n counterWidth vIndex).wire ≠
      (counterBit n counterWidth counterIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [vBit, counterBit, tupleVBit, tupleCounterBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The comparison ancilla and each padding-counter bit occupy distinct wires. -/
theorem compare_counter_wire_ne
    (n counterWidth : Nat) (bit : Fin counterWidth) :
    (compareBit n counterWidth).wire ≠
      (counterBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [compareBit, counterBit, tupleCompareBit, tupleCounterBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- An `s` coefficient bit and each padding-counter bit occupy distinct wires. -/
theorem sCoeff_counter_wire_ne
    (n counterWidth : Nat) (sIndex : Fin (n + 1))
    (counterIndex : Fin counterWidth) :
    (sCoeffBit n counterWidth sIndex).wire ≠
      (counterBit n counterWidth counterIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [sCoeffBit, counterBit, tupleSCoeffBit, tupleCounterBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- An `r` coefficient bit and each padding-counter bit occupy distinct wires. -/
theorem rCoeff_counter_wire_ne
    (n counterWidth : Nat) (rIndex : Fin (n + 1))
    (counterIndex : Fin counterWidth) :
    (rCoeffBit n counterWidth rIndex).wire ≠
      (counterBit n counterWidth counterIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [rCoeffBit, counterBit, tupleRCoeffBit, tupleCounterBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The first scratch bit and each padding-counter bit occupy distinct wires. -/
theorem scratchA_counter_wire_ne
    (n counterWidth : Nat) (bit : Fin counterWidth) :
    (scratchABit n counterWidth).wire ≠
      (counterBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [scratchABit, counterBit, tupleScratchABit, tupleCounterBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The second scratch bit and each padding-counter bit occupy distinct wires. -/
theorem scratchB_counter_wire_ne
    (n counterWidth : Nat) (bit : Fin counterWidth) :
    (scratchBBit n counterWidth).wire ≠
      (counterBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [scratchBBit, counterBit, tupleScratchBBit, tupleCounterBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- Each stored branch-history bit and each padding-counter bit occupy distinct
wires. -/
theorem history_counter_wire_ne
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (counterIndex : Fin counterWidth) :
    (historyBit n counterWidth historyIndex).wire ≠
      (counterBit n counterWidth counterIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [historyBit, counterBit, tupleHistoryBit, tupleCounterBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The active flag and the second scratch bit occupy distinct wires. -/
theorem active_scratchB_wire_ne (n counterWidth : Nat) :
    (activeBit n counterWidth).wire ≠ (scratchBBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, scratchBBit, tupleActiveBit, tupleScratchBBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.bool_width,
    BinaryLabelEncoding.boolBit]
  omega

/-- The active flag and the first scratch bit occupy distinct wires. -/
theorem active_scratchA_wire_ne (n counterWidth : Nat) :
    (activeBit n counterWidth).wire ≠ (scratchABit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, scratchABit, tupleActiveBit, tupleScratchABit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.bool_width,
    BinaryLabelEncoding.boolBit]
  omega

/-- The active flag and comparison ancilla occupy distinct wires. -/
theorem active_compare_wire_ne (n counterWidth : Nat) :
    (activeBit n counterWidth).wire ≠ (compareBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, compareBit, tupleActiveBit, tupleCompareBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.bool_width,
    BinaryLabelEncoding.boolBit]
  omega

/-- The active flag and a `u` word bit occupy distinct wires. -/
theorem active_u_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (activeBit n counterWidth).wire ≠
      (uBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, uBit, tupleActiveBit, tupleUBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The active flag and a `v` word bit occupy distinct wires. -/
theorem active_v_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (activeBit n counterWidth).wire ≠
      (vBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, vBit, tupleActiveBit, tupleVBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The active flag and an `s` coefficient bit occupy distinct wires. -/
theorem active_sCoeff_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (activeBit n counterWidth).wire ≠
      (sCoeffBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, sCoeffBit, tupleActiveBit, tupleSCoeffBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- The active flag and an `r` coefficient bit occupy distinct wires. -/
theorem active_rCoeff_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (activeBit n counterWidth).wire ≠
      (rCoeffBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [activeBit, rCoeffBit, tupleActiveBit, tupleRCoeffBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- A `u` word bit and the comparison ancilla occupy distinct wires. -/
theorem u_compare_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (uBit n counterWidth bit).wire ≠
      (compareBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, compareBit, tupleUBit, tupleCompareBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- A `v` word bit and the comparison ancilla occupy distinct wires. -/
theorem v_compare_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (vBit n counterWidth bit).wire ≠
      (compareBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [vBit, compareBit, tupleVBit, tupleCompareBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- The comparison ancilla and an `s` coefficient bit occupy distinct wires. -/
theorem compare_sCoeff_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (compareBit n counterWidth).wire ≠
      (sCoeffBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [compareBit, sCoeffBit, tupleCompareBit, tupleSCoeffBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- The comparison ancilla and an `r` coefficient bit occupy distinct wires. -/
theorem compare_rCoeff_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (compareBit n counterWidth).wire ≠
      (rCoeffBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [compareBit, rCoeffBit, tupleCompareBit, tupleRCoeffBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- The comparison ancilla and each stored branch-history bit occupy distinct
wires. -/
theorem compare_history_wire_ne
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (compareBit n counterWidth).wire ≠
      (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [compareBit, historyBit, tupleCompareBit, tupleHistoryBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- A `u` word bit and each stored branch-history bit occupy distinct wires. -/
theorem u_history_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (bit : Fin (2 * n)) :
    (uBit n counterWidth uIndex).wire ≠
      (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, historyBit, tupleUBit, tupleHistoryBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- A `u` word bit and a `v` word bit occupy distinct wires. -/
theorem u_v_wire_ne
    (n counterWidth : Nat) (uBitIndex vBitIndex : Fin n) :
    (uBit n counterWidth uBitIndex).wire ≠
      (vBit n counterWidth vBitIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, vBit, tupleUBit, tupleVBit, tailAfterU, tailAfterV,
    tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- A `u` word bit and an `s` coefficient bit occupy distinct wires. -/
theorem u_sCoeff_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (sIndex : Fin (n + 1)) :
    (uBit n counterWidth uIndex).wire ≠
      (sCoeffBit n counterWidth sIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, sCoeffBit, tupleUBit, tupleSCoeffBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding,
    EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, BinaryLabelEncoding.prod_width,
    BinaryLabelEncoding.finIdentity_width, BinaryLabelEncoding.bool_width]
  omega

/-- A `u` word bit and an `r` coefficient bit occupy distinct wires. -/
theorem u_rCoeff_wire_ne
    (n counterWidth : Nat) (uIndex : Fin n) (rIndex : Fin (n + 1)) :
    (uBit n counterWidth uIndex).wire ≠
      (rCoeffBit n counterWidth rIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, rCoeffBit, tupleUBit, tupleRCoeffBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding,
    EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, BinaryLabelEncoding.prod_width,
    BinaryLabelEncoding.finIdentity_width, BinaryLabelEncoding.bool_width]
  omega

/-- A `v` word bit and an `s` coefficient bit occupy distinct wires. -/
theorem v_sCoeff_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (sIndex : Fin (n + 1)) :
    (vBit n counterWidth vIndex).wire ≠
      (sCoeffBit n counterWidth sIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [vBit, sCoeffBit, tupleVBit, tupleSCoeffBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding,
    EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, BinaryLabelEncoding.prod_width,
    BinaryLabelEncoding.finIdentity_width, BinaryLabelEncoding.bool_width]
  omega

/-- A `v` word bit and an `r` coefficient bit occupy distinct wires. -/
theorem v_rCoeff_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (rIndex : Fin (n + 1)) :
    (vBit n counterWidth vIndex).wire ≠
      (rCoeffBit n counterWidth rIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [vBit, rCoeffBit, tupleVBit, tupleRCoeffBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding,
    EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, BinaryLabelEncoding.prod_width,
    BinaryLabelEncoding.finIdentity_width, BinaryLabelEncoding.bool_width]
  omega

/-- An `s` coefficient bit and an `r` coefficient bit occupy distinct wires. -/
theorem sCoeff_rCoeff_wire_ne
    (n counterWidth : Nat) (sIndex rIndex : Fin (n + 1)) :
    (sCoeffBit n counterWidth sIndex).wire ≠
      (rCoeffBit n counterWidth rIndex).wire := by
  apply Fin.ne_of_val_ne
  simp only [sCoeffBit, rCoeffBit, tupleSCoeffBit, tupleRCoeffBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- A `u` word bit and the first scratch bit occupy distinct wires. -/
theorem u_scratchA_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (uBit n counterWidth bit).wire ≠
      (scratchABit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, scratchABit, tupleUBit, tupleScratchABit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- A `u` word bit and the second scratch bit occupy distinct wires. -/
theorem u_scratchB_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (uBit n counterWidth bit).wire ≠
      (scratchBBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [uBit, scratchBBit, tupleUBit, tupleScratchBBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- A `v` word bit and each stored branch-history bit occupy distinct wires. -/
theorem v_history_wire_ne
    (n counterWidth : Nat) (vIndex : Fin n) (bit : Fin (2 * n)) :
    (vBit n counterWidth vIndex).wire ≠
      (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [vBit, historyBit, tupleVBit, tupleHistoryBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- An `s` coefficient bit and each stored branch-history bit occupy distinct
wires. -/
theorem sCoeff_history_wire_ne
    (n counterWidth : Nat) (sIndex : Fin (n + 1))
    (bit : Fin (2 * n)) :
    (sCoeffBit n counterWidth sIndex).wire ≠
      (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [sCoeffBit, historyBit, tupleSCoeffBit, tupleHistoryBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- An `r` coefficient bit and each stored branch-history bit occupy distinct
wires. -/
theorem rCoeff_history_wire_ne
    (n counterWidth : Nat) (rIndex : Fin (n + 1))
    (bit : Fin (2 * n)) :
    (rCoeffBit n counterWidth rIndex).wire ≠
      (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [rCoeffBit, historyBit, tupleRCoeffBit, tupleHistoryBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

/-- A `v` word bit and the first scratch bit occupy distinct wires. -/
theorem v_scratchA_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (vBit n counterWidth bit).wire ≠
      (scratchABit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [vBit, scratchABit, tupleVBit, tupleScratchABit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- An `s` coefficient bit and the first scratch bit occupy distinct wires. -/
theorem sCoeff_scratchA_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (sCoeffBit n counterWidth bit).wire ≠
      (scratchABit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [sCoeffBit, scratchABit, tupleSCoeffBit, tupleScratchABit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- An `r` coefficient bit and the first scratch bit occupy distinct wires. -/
theorem rCoeff_scratchA_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (rCoeffBit n counterWidth bit).wire ≠
      (scratchABit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [rCoeffBit, scratchABit, tupleRCoeffBit, tupleScratchABit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- A `v` word bit and the second scratch bit occupy distinct wires. -/
theorem v_scratchB_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (vBit n counterWidth bit).wire ≠
      (scratchBBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [vBit, scratchBBit, tupleVBit, tupleScratchBBit, tailAfterU,
    tailAfterV, tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- An `s` coefficient bit and the second scratch bit occupy distinct wires. -/
theorem sCoeff_scratchB_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (sCoeffBit n counterWidth bit).wire ≠
      (scratchBBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [sCoeffBit, scratchBBit, tupleSCoeffBit, tupleScratchBBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- An `r` coefficient bit and the second scratch bit occupy distinct wires. -/
theorem rCoeff_scratchB_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (rCoeffBit n counterWidth bit).wire ≠
      (scratchBBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [rCoeffBit, scratchBBit, tupleRCoeffBit, tupleScratchBBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- The comparison ancilla and the first scratch bit occupy distinct wires. -/
theorem compare_scratchA_wire_ne (n counterWidth : Nat) :
    (compareBit n counterWidth).wire ≠
      (scratchABit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [compareBit, scratchABit, tupleCompareBit, tupleScratchABit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.bool_width,
    BinaryLabelEncoding.boolBit]
  omega

/-- The comparison ancilla and the second scratch bit occupy distinct wires. -/
theorem compare_scratchB_wire_ne (n counterWidth : Nat) :
    (compareBit n counterWidth).wire ≠
      (scratchBBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [compareBit, scratchBBit, tupleCompareBit, tupleScratchBBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.bool_width,
    BinaryLabelEncoding.boolBit]
  omega

/-- The two scratch bits occupy distinct wires. -/
theorem scratchA_scratchB_wire_ne (n counterWidth : Nat) :
    (scratchABit n counterWidth).wire ≠
      (scratchBBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp only [scratchABit, scratchBBit, tupleScratchABit, tupleScratchBBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.bool_width,
    BinaryLabelEncoding.boolBit]
  omega

/-- The first scratch bit and each stored branch-history bit occupy distinct
wires. -/
theorem scratchA_history_wire_ne
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (scratchABit n counterWidth).wire ≠
      (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [scratchABit, historyBit, tupleScratchABit, tupleHistoryBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- The second scratch bit and each stored branch-history bit occupy distinct
wires. -/
theorem scratchB_history_wire_ne
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (scratchBBit n counterWidth).wire ≠
      (historyBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp only [scratchBBit, historyBit, tupleScratchBBit, tupleHistoryBit,
    tailAfterU, tailAfterV, tailAfterCompare, tailAfterS, tailAfterR,
    tailAfterScratchA, tailAfterScratchB, activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit]
  omega

/-- Distinct stored branch-history slots occupy distinct wires. -/
theorem history_history_wire_ne
    (n counterWidth : Nat) {target observed : Fin (2 * n)}
    (hne : target ≠ observed) :
    (historyBit n counterWidth target).wire ≠
      (historyBit n counterWidth observed).wire := by
  have hval : target.val ≠ observed.val := by
    intro hval
    exact hne (Fin.ext hval)
  apply Fin.ne_of_val_ne
  simp only [historyBit, tupleHistoryBit, tailAfterU, tailAfterV,
    tailAfterCompare, tailAfterS, tailAfterR, tailAfterScratchA,
    tailAfterScratchB, activeCounterEncoding, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width]
  omega

end RegisterBits

/-- Lifted comparison ancilla used by the comparator schedule. -/
def liftedCompareBit (n counterWidth : Nat) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftRegisterBitToComparisonWork n counterWidth
    (RegisterBits.compareBit n counterWidth)

/-- Lifted first scratch bit used as an independent clean initial-borrow
ancilla for comparison selectors. -/
def liftedScratchABit (n counterWidth : Nat) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftRegisterBitToComparisonWork n counterWidth
    (RegisterBits.scratchABit n counterWidth)

/-- Lifted second scratch bit used by branch-history write slices. -/
def liftedScratchBBit (n counterWidth : Nat) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftRegisterBitToComparisonWork n counterWidth
    (RegisterBits.scratchBBit n counterWidth)

/-- Lifted active flag over comparison work. -/
def liftedActiveBit (n counterWidth : Nat) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftRegisterBitToComparisonWork n counterWidth
    (RegisterBits.activeBit n counterWidth)

/-- Lifted branch-history bit over comparison work. -/
def liftedHistoryBit (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit (registersWithComparisonWorkEncoding n counterWidth) :=
  liftRegisterBitToComparisonWork n counterWidth
    (RegisterBits.historyBit n counterWidth bit)

/-- Any lifted Kaliski-register bit and lifted comparison-work bit occupy
distinct wires in the product encoding. -/
theorem liftRegisterBit_liftComparisonWorkBit_wire_ne
    (n counterWidth : Nat)
    (registerBit : EncodedBit (registerEncoding n counterWidth))
    (workBit : EncodedBit (comparisonWorkEncoding n)) :
    (liftRegisterBitToComparisonWork n counterWidth registerBit).wire ≠
      (liftComparisonWorkBit n counterWidth workBit).wire := by
  intro h
  have hval := congrArg Fin.val h
  have hleft := registerBit.wire.isLt
  simp [liftRegisterBitToComparisonWork, liftComparisonWorkBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire] at hval hleft
  omega

/-- The lifted comparison ancilla and a lifted comparison-work carry bit occupy
distinct wires. -/
theorem liftedCompare_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (liftedCompareBit n counterWidth).wire ≠
      (liftedComparisonCarryBit n counterWidth bit).wire :=
  liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
    (RegisterBits.compareBit n counterWidth) (comparisonCarryValueBit n bit)

/-- The lifted scratchA initial-borrow ancilla and each lifted comparison-work
carry bit occupy distinct wires. -/
theorem liftedScratchA_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (liftedScratchABit n counterWidth).wire ≠
      (liftedComparisonCarryBit n counterWidth bit).wire :=
  liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
    (RegisterBits.scratchABit n counterWidth) (comparisonCarryValueBit n bit)

/-- Lifting two distinct Kaliski-register bits over comparison work preserves
wire distinctness. -/
theorem liftRegisterBit_liftRegisterBit_wire_ne
    (n counterWidth : Nat)
    (left right : EncodedBit (registerEncoding n counterWidth))
    (h : left.wire ≠ right.wire) :
    (liftRegisterBitToComparisonWork n counterWidth left).wire ≠
      (liftRegisterBitToComparisonWork n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodLeftWire] using hval

/-- Lifting two distinct comparison-work bits preserves wire distinctness. -/
theorem liftComparisonWorkBit_liftComparisonWorkBit_wire_ne
    (n counterWidth : Nat)
    (left right : EncodedBit (comparisonWorkEncoding n))
    (h : left.wire ≠ right.wire) :
    (liftComparisonWorkBit n counterWidth left).wire ≠
      (liftComparisonWorkBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  have hwidth := (registerEncoding n counterWidth).width
  simp [liftComparisonWorkBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- Lifting two distinct register-plus-comparison bits over coefficient-adder
work preserves wire distinctness. -/
theorem liftComparisonStateBit_liftComparisonStateBit_wire_ne
    (n counterWidth : Nat)
    (left right :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (h : left.wire ≠ right.wire) :
    (liftComparisonStateBitToCoeffAdderWork n counterWidth left).wire ≠
      (liftComparisonStateBitToCoeffAdderWork n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [liftComparisonStateBitToCoeffAdderWork,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire]
    using hval

/-- Any lifted register-plus-comparison bit and lifted coefficient-adder work
bit occupy distinct wires. -/
theorem liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
    (n counterWidth : Nat)
    (stateBit :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (workBit : EncodedBit (coeffAdderWorkEncoding n)) :
    (liftComparisonStateBitToCoeffAdderWork n counterWidth stateBit).wire ≠
      (liftCoeffAdderWorkBit n counterWidth workBit).wire := by
  intro h
  have hval := congrArg Fin.val h
  have hleft := stateBit.wire.isLt
  simp [liftComparisonStateBitToCoeffAdderWork, liftCoeffAdderWorkBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire] at hval hleft
  omega

/-- Lifting two distinct coefficient-adder work bits over the
register-plus-comparison state preserves wire distinctness. -/
theorem liftCoeffAdderWorkBit_liftCoeffAdderWorkBit_wire_ne
    (n counterWidth : Nat)
    (left right : EncodedBit (coeffAdderWorkEncoding n))
    (h : left.wire ≠ right.wire) :
    (liftCoeffAdderWorkBit n counterWidth left).wire ≠
      (liftCoeffAdderWorkBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  have hwidth := (registersWithComparisonWorkEncoding n counterWidth).width
  simp [liftCoeffAdderWorkBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- Lifting two distinct register-plus-comparison bits over counter-increment
work preserves wire distinctness. -/
theorem liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
    (n counterWidth : Nat)
    (left right :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (h : left.wire ≠ right.wire) :
    (liftComparisonStateBitToDetectorCounterWork n counterWidth left).wire ≠
      (liftComparisonStateBitToDetectorCounterWork n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [liftComparisonStateBitToDetectorCounterWork,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire]
    using hval

/-- Any lifted register-plus-comparison bit and lifted counter-increment work bit
occupy distinct wires. -/
theorem liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
    (n counterWidth : Nat)
    (stateBit :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (workBit : EncodedBit (counterIncrementWorkEncoding counterWidth)) :
    (liftComparisonStateBitToDetectorCounterWork n counterWidth stateBit).wire ≠
      (liftCounterIncrementWorkBitToDetectorCounterWork n counterWidth
        workBit).wire := by
  intro h
  have hval := congrArg Fin.val h
  have hleft := stateBit.wire.isLt
  simp [liftComparisonStateBitToDetectorCounterWork,
    liftCounterIncrementWorkBitToDetectorCounterWork,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire]
    at hval hleft
  omega

/-- Lifting two distinct counter-increment work bits over the
register-plus-comparison state preserves wire distinctness. -/
theorem liftDetectorCounterWorkBit_liftDetectorCounterWorkBit_wire_ne
    (n counterWidth : Nat)
    (left right : EncodedBit (counterIncrementWorkEncoding counterWidth))
    (h : left.wire ≠ right.wire) :
    (liftCounterIncrementWorkBitToDetectorCounterWork n counterWidth
        left).wire ≠
      (liftCounterIncrementWorkBitToDetectorCounterWork n counterWidth
        right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  have hwidth := (registersWithComparisonWorkEncoding n counterWidth).width
  simp [liftCounterIncrementWorkBitToDetectorCounterWork,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- Any lifted Kaliski-register bit and lifted counter-increment work bit
occupy distinct wires. -/
theorem liftRegisterBit_liftCounterIncrementWorkBit_wire_ne
    (n counterWidth : Nat)
    (registerBit : EncodedBit (registerEncoding n counterWidth))
    (workBit : EncodedBit (counterIncrementWorkEncoding counterWidth)) :
    (liftRegisterBitToCounterIncrementWork n counterWidth registerBit).wire ≠
      (liftCounterIncrementWorkBit n counterWidth workBit).wire := by
  intro h
  have hval := congrArg Fin.val h
  have hleft := registerBit.wire.isLt
  simp [liftRegisterBitToCounterIncrementWork,
    liftCounterIncrementWorkBit, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hval hleft
  omega

/-- Lifting two distinct Kaliski-register bits over counter-increment work
preserves wire distinctness. -/
theorem liftRegisterBit_counterIncrement_liftRegisterBit_wire_ne
    (n counterWidth : Nat)
    (left right : EncodedBit (registerEncoding n counterWidth))
    (h : left.wire ≠ right.wire) :
    (liftRegisterBitToCounterIncrementWork n counterWidth left).wire ≠
      (liftRegisterBitToCounterIncrementWork n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [liftRegisterBitToCounterIncrementWork,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire]
    using hval

/-- Lifting two distinct counter-increment work bits over the Kaliski registers
preserves wire distinctness. -/
theorem liftCounterIncrementWorkBit_liftCounterIncrementWorkBit_wire_ne
    (n counterWidth : Nat)
    (left right : EncodedBit (counterIncrementWorkEncoding counterWidth))
    (h : left.wire ≠ right.wire) :
    (liftCounterIncrementWorkBit n counterWidth left).wire ≠
      (liftCounterIncrementWorkBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  have hwidth := (registerEncoding n counterWidth).width
  simp [liftCounterIncrementWorkBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- The dedicated coefficient-adder carry-in flag is distinct from every
temporary carry-work bit. -/
theorem coeffAdderCarryIn_carryWork_wire_ne
    (n : Nat) (bit : Fin ((n + 1) - 1)) :
    (coeffAdderCarryInWorkBit n).wire ≠
      (coeffAdderCarryWorkBit n bit).wire := by
  apply Fin.ne_of_val_ne
  simp [coeffAdderCarryInWorkBit, coeffAdderCarryWorkBit,
    coeffAdderWorkEncoding, PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.bool_width,
    BinaryLabelEncoding.boolBit, BinaryLabelEncoding.finIdentityBit]
  omega

/-- Distinct dedicated coefficient-adder carry-work bits occupy distinct
wires. -/
theorem coeffAdderCarryWork_carryWork_wire_ne
    (n : Nat) (left right : Fin ((n + 1) - 1)) (h : left ≠ right) :
    (coeffAdderCarryWorkBit n left).wire ≠
      (coeffAdderCarryWorkBit n right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [coeffAdderCarryWorkBit, coeffAdderWorkEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
    using hval

/-- Distinct counter-increment source bits occupy distinct wires. -/
theorem counterIncrementSource_source_wire_ne
    (counterWidth : Nat) (left right : Fin counterWidth) (h : left ≠ right) :
    (counterIncrementSourceBit counterWidth left).wire ≠
      (counterIncrementSourceBit counterWidth right).wire := by
  intro hw
  exact (littleEndianWire_ne h) (by
    apply Fin.ext
    have hval := congrArg Fin.val hw
    simpa [counterIncrementSourceBit, wordEncoding,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire,
      BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
      using hval)

/-- Each counter-increment source bit is distinct from the carry-in flag. -/
theorem counterIncrementSource_carryIn_wire_ne
    (counterWidth : Nat) (bit : Fin counterWidth) :
    (counterIncrementSourceBit counterWidth bit).wire ≠
      (counterIncrementCarryInBit counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp [counterIncrementSourceBit, counterIncrementCarryInBit,
    counterIncrementWorkEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
  omega

/-- Each counter-increment source bit is distinct from every temporary
carry-work bit. -/
theorem counterIncrementSource_carryWork_wire_ne
    (counterWidth : Nat) (sourceBit : Fin counterWidth)
    (workBit : Fin (counterWidth - 1)) :
    (counterIncrementSourceBit counterWidth sourceBit).wire ≠
      (counterIncrementCarryWorkBit counterWidth workBit).wire := by
  apply Fin.ne_of_val_ne
  simp [counterIncrementSourceBit, counterIncrementCarryWorkBit,
    counterIncrementWorkEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit]
  omega

/-- The counter-increment carry-in flag is distinct from every temporary
carry-work bit. -/
theorem counterIncrementCarryIn_carryWork_wire_ne
    (counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    (counterIncrementCarryInBit counterWidth).wire ≠
      (counterIncrementCarryWorkBit counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp [counterIncrementCarryInBit, counterIncrementCarryWorkBit,
    counterIncrementWorkEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.finIdentity_width,
    BinaryLabelEncoding.bool_width, BinaryLabelEncoding.boolBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]

/-- Distinct counter-increment carry-work bits occupy distinct wires. -/
theorem counterIncrementCarryWork_carryWork_wire_ne
    (counterWidth : Nat) (left right : Fin (counterWidth - 1))
    (h : left ≠ right) :
    (counterIncrementCarryWorkBit counterWidth left).wire ≠
      (counterIncrementCarryWorkBit counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [counterIncrementCarryWorkBit, counterIncrementWorkEncoding,
    wordEncoding, PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
    using hval

/-- Full-round lifted coefficient-work-state bits and lifted counter-increment
work bits occupy distinct wires. -/
theorem liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
    (tail counterWidth : Nat)
    (stateBit :
      EncodedBit
        (registersWithCoeffAdderWorkEncoding tail.succ counterWidth))
    (workBit : EncodedBit (counterIncrementWorkEncoding counterWidth)) :
    (liftCoeffAdderStateBitToFullRoundWork
        tail counterWidth stateBit).wire ≠
      (liftCounterIncrementWorkBitToFullRoundWork
        tail counterWidth workBit).wire := by
  intro h
  have hval := congrArg Fin.val h
  have hleft := stateBit.wire.isLt
  simp [liftCoeffAdderStateBitToFullRoundWork,
    liftCounterIncrementWorkBitToFullRoundWork,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire]
    at hval hleft
  omega

/-- Lifting two distinct counter-increment work bits over the full-round
coefficient-work state preserves wire distinctness. -/
theorem liftCounterIncrementWorkBitToFullRoundWork_wire_ne
    (tail counterWidth : Nat)
    (left right : EncodedBit (counterIncrementWorkEncoding counterWidth))
    (h : left.wire ≠ right.wire) :
    (liftCounterIncrementWorkBitToFullRoundWork tail counterWidth left).wire ≠
      (liftCounterIncrementWorkBitToFullRoundWork
        tail counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simp [liftCounterIncrementWorkBitToFullRoundWork,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- The full-round counter carry-in latch bit is distinct from every
counter-increment source bit. -/
theorem fullRoundWorkCounterCarryIn_counterSource_wire_ne
    (tail counterWidth : Nat) (bit : Fin counterWidth) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).wire ≠
      (fullRoundWorkCounterSourceBit tail counterWidth bit).wire :=
  liftCounterIncrementWorkBitToFullRoundWork_wire_ne
    tail counterWidth
    (counterIncrementCarryInBit counterWidth)
    (counterIncrementSourceBit counterWidth bit)
    (Ne.symm (counterIncrementSource_carryIn_wire_ne counterWidth bit))

/-- The full-round counter carry-in latch bit is distinct from every
counter-increment carry-work bit. -/
theorem fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
    (tail counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).wire ≠
      (fullRoundWorkCounterCarryWorkBit tail counterWidth bit).wire :=
  liftCounterIncrementWorkBitToFullRoundWork_wire_ne
    tail counterWidth
    (counterIncrementCarryInBit counterWidth)
    (counterIncrementCarryWorkBit counterWidth bit)
    (counterIncrementCarryIn_carryWork_wire_ne counterWidth bit)

/-- A full-round counter-increment work bit is disjoint from any gate lifted
from the coefficient-work state into the left side of the full-round product. -/
theorem fullRoundWorkCounterBit_prodLeftGate_bitDisjoint
    (tail counterWidth : Nat)
    (observed : EncodedBit (counterIncrementWorkEncoding counterWidth))
    (gate :
      EncodedBit.GateSpec
        (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)) :
    EncodedBit.GateSpec.bitDisjoint
      (liftCounterIncrementWorkBitToFullRoundWork tail counterWidth observed)
      (EncodedBit.GateSpec.prodLeft
        (counterIncrementWorkEncoding counterWidth) gate) := by
  cases gate with
  | x target =>
      exact
        liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
          tail counterWidth target observed
  | cnot control target hct =>
      exact
        ⟨liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth control observed,
          liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth target observed⟩
  | toffoli controlA controlB target hab ha hb =>
      exact
        ⟨liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth controlA observed,
          liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth controlB observed,
          liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth target observed⟩

/-- Distinct `u` bits occupy distinct wires in the Kaliski register encoding. -/
theorem u_u_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    (RegisterBits.uBit n counterWidth left).wire ≠
      (RegisterBits.uBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [RegisterBits.uBit, RegisterBits.tupleUBit, RegisterBits.tailAfterU,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
    using hval

/-- Distinct `v` bits occupy distinct wires in the Kaliski register encoding. -/
theorem v_v_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    (RegisterBits.vBit n counterWidth left).wire ≠
      (RegisterBits.vBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [RegisterBits.vBit, RegisterBits.tupleVBit, RegisterBits.tailAfterU,
    RegisterBits.tailAfterV, registerEncoding, registerTupleEncoding,
    wordEncoding, EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit] using hval

/-- Distinct `s` coefficient bits occupy distinct wires in the Kaliski register
encoding. -/
theorem sCoeff_sCoeff_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    (RegisterBits.sCoeffBit n counterWidth left).wire ≠
      (RegisterBits.sCoeffBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [RegisterBits.sCoeffBit, RegisterBits.tupleSCoeffBit,
    RegisterBits.tailAfterU, RegisterBits.tailAfterV,
    RegisterBits.tailAfterCompare, RegisterBits.tailAfterS, registerEncoding,
    registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
    using hval

/-- Distinct `r` coefficient bits occupy distinct wires in the Kaliski register
encoding. -/
theorem rCoeff_rCoeff_wire_ne
    (n counterWidth : Nat) (left right : Fin (n + 1)) (h : left ≠ right) :
    (RegisterBits.rCoeffBit n counterWidth left).wire ≠
      (RegisterBits.rCoeffBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [RegisterBits.rCoeffBit, RegisterBits.tupleRCoeffBit,
    RegisterBits.tailAfterU, RegisterBits.tailAfterV,
    RegisterBits.tailAfterCompare, RegisterBits.tailAfterS,
    RegisterBits.tailAfterR, registerEncoding, registerTupleEncoding,
    wordEncoding, EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit] using hval

/-- Distinct padding-counter bits occupy distinct wires in the Kaliski register
encoding. -/
theorem counter_counter_wire_ne
    (n counterWidth : Nat) (left right : Fin counterWidth) (h : left ≠ right) :
    (RegisterBits.counterBit n counterWidth left).wire ≠
      (RegisterBits.counterBit n counterWidth right).wire := by
  intro hw
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [RegisterBits.counterBit, RegisterBits.tupleCounterBit,
    RegisterBits.tailAfterU, RegisterBits.tailAfterV,
    RegisterBits.tailAfterCompare, RegisterBits.tailAfterS,
    RegisterBits.tailAfterR, RegisterBits.tailAfterScratchA,
    RegisterBits.tailAfterScratchB, RegisterBits.activeCounterEncoding,
    registerEncoding, registerTupleEncoding, wordEncoding, EncodedBit.relabel,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]
    using hval

/-- Distinct little-endian padding-counter value bits occupy distinct wires. -/
theorem counterValue_counterValue_wire_ne
    (n counterWidth : Nat) (left right : Fin counterWidth) (h : left ≠ right) :
    (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire left)).wire ≠
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire right)).wire := by
  exact counter_counter_wire_ne n counterWidth
    (WireAddress.littleEndianWire left)
    (WireAddress.littleEndianWire right)
    (littleEndianWire_ne h)

/-! ## Compact shared carrier -/

namespace Compact

/-- Reusable clean workspace shared by mutually exclusive inversion stages.

The VBE work object is the sole linear-width deviation from the RNSL17
carrier.  The logarithmic word and two bits are reused by round routing and
the counter-controlled correction rather than duplicated for each stage
[RNSL17, ECDLP.tex:269,399-479,656-691]. -/
structure SharedWork (n counterWidth : Nat) where
  /-- One clean VBE carry-in plus the carry chain for `n + 1`-bit coefficients. -/
  coefficientAdder : CoeffAdderWork n
  /-- Logarithmic correction/control word; one bit shorter than the `2n` counter. -/
  correctionCounter : Word (counterWidth - 1)
  /-- Shared route/path bit. -/
  path : Bool
  /-- Shared clean bit for decomposing controlled native gates. -/
  control : Bool
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprSharedWork.repr

/-- Product view used by the shared-work encoding. -/
abbrev SharedWorkTuple (n counterWidth : Nat) :=
  CoeffAdderWork n ×
    (Word (counterWidth - 1) × (Bool × Bool))

/-- Fieldwise equivalence for the reusable shared workspace. -/
def sharedWorkTupleEquiv (n counterWidth : Nat) :
    SharedWork n counterWidth ≃ SharedWorkTuple n counterWidth where
  toFun := fun work =>
    (work.coefficientAdder,
      (work.correctionCounter, (work.path, work.control)))
  invFun := fun work =>
    { coefficientAdder := work.1
      correctionCounter := work.2.1
      path := work.2.2.1
      control := work.2.2.2 }
  left_inv := by
    intro work
    cases work
    rfl
  right_inv := by
    intro work
    rcases work with ⟨coefficientAdder, correctionCounter, path, control⟩
    rfl

/-- Packed encoding of the reusable inversion workspace. -/
@[implicit_reducible]
def sharedWorkTupleEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (SharedWorkTuple n counterWidth) :=
  BinaryLabelEncoding.prod (coeffAdderWorkEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool))

/-- Faithful encoding of the reusable inversion workspace. -/
@[implicit_reducible]
def sharedWorkEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (SharedWork n counterWidth) :=
  (sharedWorkTupleEncoding n counterWidth).relabel
    (sharedWorkTupleEquiv n counterWidth)

/-- Distinguished clean value of the reusable inversion workspace. -/
def cleanSharedWork (n counterWidth : Nat) : SharedWork n counterWidth where
  coefficientAdder := cleanCoeffAdderWork n
  correctionCounter := 0
  path := false
  control := false

/-- Compact compute/correct/copy carrier.

The input lives in the core `v` register during the forward fold and is
restored by the physical inverse after the result has been copied to `target`.
Thus no separate preserved-input word is appended.  The carrier has only the
one `2n` history family already present in `MK.Registers`; comparison,
counter-increment, and correction stages must borrow `shared`. -/
structure Registers (n counterWidth : Nat) where
/-- Montgomery--Kaliski data, including the sole `2n` history word
[RNSL17, ECDLP.tex:445-446,468]. -/
  core : MK.Registers n counterWidth
  /-- Workspace reused by comparison, addition, routing, and correction. -/
  shared : SharedWork n counterWidth
  /-- Public word into which the corrected inverse is xor-copied. -/
  target : Word n
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprRegisters.repr

/-- Product view used by the compact carrier encoding. -/
abbrev RegisterTuple (n counterWidth : Nat) :=
  MK.Registers n counterWidth ×
    (SharedWork n counterWidth × Word n)

/-- Fieldwise equivalence for the compact inversion carrier. -/
def registerTupleEquiv (n counterWidth : Nat) :
    Registers n counterWidth ≃ RegisterTuple n counterWidth where
  toFun := fun registers =>
    (registers.core, (registers.shared, registers.target))
  invFun := fun registers =>
    { core := registers.1
      shared := registers.2.1
      target := registers.2.2 }
  left_inv := by
    intro registers
    cases registers
    rfl
  right_inv := by
    intro registers
    rcases registers with ⟨core, shared, target⟩
    rfl

/-- Packed product encoding before restoring field names. -/
@[implicit_reducible]
def registerTupleEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegisterTuple n counterWidth) :=
  BinaryLabelEncoding.prod (registerEncoding n counterWidth)
    (BinaryLabelEncoding.prod (sharedWorkEncoding n counterWidth)
      (wordEncoding n))

/-- Exact physical encoding of the compact inversion carrier. -/
@[implicit_reducible]
def encoding (n counterWidth : Nat) :
    BinaryLabelEncoding (Registers n counterWidth) :=
  (registerTupleEncoding n counterWidth).relabel
    (registerTupleEquiv n counterWidth)

/-! ### Addressed compact-carrier fields -/

/-- One core-register bit before restoring the compact field names. -/
def rawCoreBit (n counterWidth : Nat)
    (bit : EncodedBit (registerEncoding n counterWidth)) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit (registerEncoding n counterWidth)
    (BinaryLabelEncoding.prod (sharedWorkEncoding n counterWidth)
      (wordEncoding n)) bit

/-- One core-register bit in the compact carrier. -/
def liftCoreBit (n counterWidth : Nat)
    (bit : EncodedBit (registerEncoding n counterWidth)) :
    EncodedBit (encoding n counterWidth) :=
  (rawCoreBit n counterWidth bit).relabel
    (registerTupleEquiv n counterWidth)

/-- One shared-work bit before restoring the compact field names. -/
def rawSharedBit (n counterWidth : Nat)
    (bit : EncodedBit (sharedWorkEncoding n counterWidth)) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (registerEncoding n counterWidth)
    (BinaryLabelEncoding.prod (sharedWorkEncoding n counterWidth)
      (wordEncoding n))
    (BinaryLabelEncoding.prodLeftBit (sharedWorkEncoding n counterWidth)
      (wordEncoding n) bit)

/-- One shared-work bit in the compact carrier. -/
def liftSharedBit (n counterWidth : Nat)
    (bit : EncodedBit (sharedWorkEncoding n counterWidth)) :
    EncodedBit (encoding n counterWidth) :=
  (rawSharedBit n counterWidth bit).relabel
    (registerTupleEquiv n counterWidth)

/-- One public target-word bit before restoring compact field names. -/
def rawTargetBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (registerTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (registerEncoding n counterWidth)
    (BinaryLabelEncoding.prod (sharedWorkEncoding n counterWidth)
      (wordEncoding n))
    (BinaryLabelEncoding.prodRightBit (sharedWorkEncoding n counterWidth)
      (wordEncoding n) (BinaryLabelEncoding.finIdentityBit n bit))

/-- One public target-word bit in the complete compact carrier. -/
def targetBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (encoding n counterWidth) :=
  (rawTargetBit n counterWidth bit).relabel
    (registerTupleEquiv n counterWidth)

/-- Little-endian target value-bit lens. -/
def targetValueBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (encoding n counterWidth) :=
  targetBit n counterWidth (WireAddress.littleEndianWire bit)

/-- Little-endian target word lens. -/
def targetValueWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) n where
  bit := targetValueBit n counterWidth

@[simp] theorem liftCoreBit_get (n counterWidth : Nat)
    (bit : EncodedBit (registerEncoding n counterWidth))
    (x : Registers n counterWidth) :
    (liftCoreBit n counterWidth bit).get x = bit.get x.core := by
  simp [liftCoreBit, rawCoreBit, registerTupleEncoding, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, EncodedBit.relabel]

@[simp] theorem liftSharedBit_get (n counterWidth : Nat)
    (bit : EncodedBit (sharedWorkEncoding n counterWidth))
    (x : Registers n counterWidth) :
    (liftSharedBit n counterWidth bit).get x = bit.get x.shared := by
  simp [liftSharedBit, rawSharedBit, registerTupleEncoding, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]

/-- The VBE coefficient-adder carry-in before restoring shared-work field
names. -/
def rawCoefficientCarryInBit (n counterWidth : Nat) :
    EncodedBit (sharedWorkTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit (coeffAdderWorkEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (n + 1))
      BinaryLabelEncoding.boolBit)

/-- The VBE coefficient-adder carry-in in the named shared workspace. -/
def sharedCoefficientCarryInBit (n counterWidth : Nat) :
    EncodedBit (sharedWorkEncoding n counterWidth) :=
  (rawCoefficientCarryInBit n counterWidth).relabel
    (sharedWorkTupleEquiv n counterWidth)

/-- The VBE coefficient-adder carry-in in the complete compact carrier. -/
def coefficientCarryInBit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  liftSharedBit n counterWidth
    (sharedCoefficientCarryInBit n counterWidth)

/-- One VBE carry-work bit before restoring the shared-work field names.
The `(n+1)`-bit coefficient adder has exactly `n` such bits, so the same word
can serve as the `n`-bit subtract-borrow workspace during comparison. -/
def rawCoefficientCarryWorkBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (sharedWorkTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit (coeffAdderWorkEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (n + 1))
      (BinaryLabelEncoding.finIdentityBit n bit))

/-- One VBE carry-work bit in the named shared workspace. -/
def sharedCoefficientCarryWorkBit
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (sharedWorkEncoding n counterWidth) :=
  (rawCoefficientCarryWorkBit n counterWidth bit).relabel
    (sharedWorkTupleEquiv n counterWidth)

/-- One VBE carry-work bit lifted into the complete compact carrier. -/
def coefficientCarryWorkBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (encoding n counterWidth) :=
  liftSharedBit n counterWidth
    (sharedCoefficientCarryWorkBit n counterWidth bit)

/-- The VBE carry bank viewed as the compact comparator borrow-work word. -/
def coefficientCarryWorkWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) n where
  bit := coefficientCarryWorkBit n counterWidth

@[simp] theorem coefficientCarryInBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get x =
      x.shared.coefficientAdder.1 := by
  simp [coefficientCarryInBit, liftSharedBit, rawSharedBit,
    sharedCoefficientCarryInBit, rawCoefficientCarryInBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, sharedWorkTupleEquiv,
    registerTupleEquiv, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel]
  rfl

@[simp] theorem coefficientCarryWorkBit_get (n counterWidth : Nat)
    (bit : Fin n) (x : Registers n counterWidth) :
    (coefficientCarryWorkBit n counterWidth bit).get x =
      (BinaryLabelEncoding.finIdentityBit n bit).get
        x.shared.coefficientAdder.2 := by
  simp [coefficientCarryWorkBit, liftSharedBit, rawSharedBit,
    sharedCoefficientCarryWorkBit, rawCoefficientCarryWorkBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, sharedWorkTupleEquiv,
    registerTupleEquiv, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel]

@[simp] theorem targetBit_get (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (targetBit n counterWidth bit).get x =
      x.target.val.testBit (WireAddress.bitIndex bit).val := by
  simp [targetBit, rawTargetBit, registerTupleEncoding, registerTupleEquiv,
    BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel]

@[simp] theorem targetValueBit_get (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (targetValueBit n counterWidth bit).get x =
      x.target.val.testBit bit.val := by
  simp [targetValueBit, targetBit_get]

/-- Flipping a public target bit leaves the compact core unchanged. -/
@[simp] theorem targetValueBit_flip_core
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    ((targetValueBit n counterWidth bit).flip x).core = x.core := by
  simp [targetValueBit, targetBit, rawTargetBit, registerTupleEncoding,
    registerTupleEquiv, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel]

/-- Flipping a public target bit leaves the reusable shared workspace
unchanged. -/
@[simp] theorem targetValueBit_flip_shared
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    ((targetValueBit n counterWidth bit).flip x).shared = x.shared := by
  simp [targetValueBit, targetBit, rawTargetBit, registerTupleEncoding,
    registerTupleEquiv, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel]

/-- One bit of the logarithmic word shared by counter correction and the
literal-one source used while the padding counter is borrowed. -/
def rawCorrectionCounterBit
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (sharedWorkTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (coeffAdderWorkEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodLeftBit (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.finIdentityBit (counterWidth - 1) bit))

/-- One correction-counter bit in the named reusable workspace. -/
def sharedCorrectionCounterBit
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (sharedWorkEncoding n counterWidth) :=
  (rawCorrectionCounterBit n counterWidth bit).relabel
    (sharedWorkTupleEquiv n counterWidth)

/-- One correction-counter bit in the complete compact carrier. -/
def correctionCounterBit
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (encoding n counterWidth) :=
  liftSharedBit n counterWidth
    (sharedCorrectionCounterBit n counterWidth bit)

/-- The shared correction-counter word. -/
def correctionCounterWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) (counterWidth - 1) where
  bit := correctionCounterBit n counterWidth

/-- The shared route/path bit before restoring named workspace fields. -/
def rawPathBit (n counterWidth : Nat) :
    EncodedBit (sharedWorkTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (coeffAdderWorkEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- The shared route/path bit in the named reusable workspace. -/
def sharedPathBit (n counterWidth : Nat) :
    EncodedBit (sharedWorkEncoding n counterWidth) :=
  (rawPathBit n counterWidth).relabel (sharedWorkTupleEquiv n counterWidth)

/-- The shared route/path bit in the complete compact carrier. -/
def pathBit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  liftSharedBit n counterWidth (sharedPathBit n counterWidth)

/-- The shared control bit before restoring named workspace fields. -/
def rawControlBit (n counterWidth : Nat) :
    EncodedBit (sharedWorkTupleEncoding n counterWidth) :=
  BinaryLabelEncoding.prodRightBit (coeffAdderWorkEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit (wordEncoding (counterWidth - 1))
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- The shared control bit in the named reusable workspace. -/
def sharedControlBit (n counterWidth : Nat) :
    EncodedBit (sharedWorkEncoding n counterWidth) :=
  (rawControlBit n counterWidth).relabel
    (sharedWorkTupleEquiv n counterWidth)

/-- The shared control bit in the complete compact carrier. -/
def controlBit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  liftSharedBit n counterWidth (sharedControlBit n counterWidth)

@[simp] theorem correctionCounterBit_get
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1))
    (x : Registers n counterWidth) :
    (correctionCounterBit n counterWidth bit).get x =
      x.shared.correctionCounter.val.testBit
        (WireAddress.bitIndex bit).val := by
  simp [correctionCounterBit, liftSharedBit, rawSharedBit,
    sharedCorrectionCounterBit, rawCorrectionCounterBit, sharedWorkEncoding,
    sharedWorkTupleEncoding, sharedWorkTupleEquiv, registerTupleEquiv,
    wordEncoding, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel]

/-- The little-endian value-bit view of the shared correction-counter word. -/
def correctionCounterValueBit
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    EncodedBit (encoding n counterWidth) :=
  correctionCounterBit n counterWidth (WireAddress.littleEndianWire bit)

/-- The little-endian value-word view of the shared correction-counter. -/
def correctionCounterValueWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) (counterWidth - 1) where
  bit := correctionCounterValueBit n counterWidth

@[simp] theorem correctionCounterValueBit_get
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1))
    (x : Registers n counterWidth) :
    (correctionCounterValueBit n counterWidth bit).get x =
      x.shared.correctionCounter.val.testBit bit.val := by
  simp [correctionCounterValueBit, correctionCounterBit_get]

@[simp] theorem pathBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (pathBit n counterWidth).get x = x.shared.path := by
  simp [pathBit, liftSharedBit, rawSharedBit, sharedPathBit, rawPathBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, sharedWorkTupleEquiv,
    registerTupleEquiv, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel]
  rfl

@[simp] theorem controlBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (controlBit n counterWidth).get x = x.shared.control := by
  simp [controlBit, liftSharedBit, rawSharedBit, sharedControlBit,
    rawControlBit, sharedWorkEncoding, sharedWorkTupleEncoding,
    sharedWorkTupleEquiv, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]
  rfl

/-- Every compact core bit is disjoint from every reusable shared-work bit. -/
theorem liftCoreBit_liftSharedBit_wire_ne
    (n counterWidth : Nat)
    (coreBit : EncodedBit (registerEncoding n counterWidth))
    (sharedBit : EncodedBit (sharedWorkEncoding n counterWidth)) :
    (liftCoreBit n counterWidth coreBit).wire ≠
      (liftSharedBit n counterWidth sharedBit).wire := by
  intro hw
  have hval := congrArg Fin.val hw
  have hcore := coreBit.wire.isLt
  simp [liftCoreBit, rawCoreBit, liftSharedBit, rawSharedBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel] at hval hcore
  omega

/-- Every compact core bit is disjoint from every public target bit. -/
theorem liftCoreBit_targetBit_wire_ne
    (n counterWidth : Nat)
    (coreBit : EncodedBit (registerEncoding n counterWidth))
    (targetIndex : Fin n) :
    (liftCoreBit n counterWidth coreBit).wire ≠
      (targetBit n counterWidth targetIndex).wire := by
  intro hw
  have hval := congrArg Fin.val hw
  have hcore := coreBit.wire.isLt
  simp [liftCoreBit, rawCoreBit, targetBit, rawTargetBit,
    registerTupleEncoding, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, EncodedBit.relabel] at hval hcore
  omega

/-- Every compact shared-work bit is disjoint from every public target bit. -/
theorem liftSharedBit_targetBit_wire_ne
    (n counterWidth : Nat)
    (sharedBit : EncodedBit (sharedWorkEncoding n counterWidth))
    (targetIndex : Fin n) :
    (liftSharedBit n counterWidth sharedBit).wire ≠
      (targetBit n counterWidth targetIndex).wire := by
  intro hw
  have hval := congrArg Fin.val hw
  have hshared := sharedBit.wire.isLt
  simp [liftSharedBit, rawSharedBit, targetBit, rawTargetBit,
    registerTupleEncoding, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire, EncodedBit.relabel] at hval hshared
  omega

/-- Every compact core bit is disjoint from every little-endian public target
value bit. -/
theorem liftCoreBit_targetValueBit_wire_ne
    (n counterWidth : Nat)
    (coreBit : EncodedBit (registerEncoding n counterWidth))
    (targetIndex : Fin n) :
    (liftCoreBit n counterWidth coreBit).wire ≠
      (targetValueBit n counterWidth targetIndex).wire := by
  simpa [targetValueBit] using
    liftCoreBit_targetBit_wire_ne n counterWidth coreBit
      (WireAddress.littleEndianWire targetIndex)

/-- Every compact shared-work bit is disjoint from every little-endian public
target value bit. -/
theorem liftSharedBit_targetValueBit_wire_ne
    (n counterWidth : Nat)
    (sharedBit : EncodedBit (sharedWorkEncoding n counterWidth))
    (targetIndex : Fin n) :
    (liftSharedBit n counterWidth sharedBit).wire ≠
      (targetValueBit n counterWidth targetIndex).wire := by
  simpa [targetValueBit] using
    liftSharedBit_targetBit_wire_ne n counterWidth sharedBit
      (WireAddress.littleEndianWire targetIndex)

/-- Distinct little-endian public target positions occupy distinct physical
wires. -/
theorem targetValueBit_wire_ne
    (n counterWidth : Nat) {left right : Fin n} (hne : left ≠ right) :
    (targetValueBit n counterWidth left).wire ≠
      (targetValueBit n counterWidth right).wire := by
  intro hw
  apply littleEndianWire_ne hne
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [targetValueBit, targetBit, rawTargetBit, registerTupleEncoding,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel] using hval

/-- Distinct shared correction-counter positions occupy distinct wires. -/
theorem correctionCounterBit_wire_ne
    (n counterWidth : Nat) {left right : Fin (counterWidth - 1)}
    (hne : left ≠ right) :
    (correctionCounterBit n counterWidth left).wire ≠
      (correctionCounterBit n counterWidth right).wire := by
  intro hw
  apply hne
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [correctionCounterBit, liftSharedBit, rawSharedBit,
    sharedCorrectionCounterBit, rawCorrectionCounterBit, sharedWorkEncoding,
    sharedWorkTupleEncoding, wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel] using hval

/-- The shared control bit is disjoint from every correction-counter bit. -/
theorem controlBit_correctionCounterBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    (controlBit n counterWidth).wire ≠
      (correctionCounterBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp [controlBit, sharedControlBit, rawControlBit, correctionCounterBit,
    sharedCorrectionCounterBit, rawCorrectionCounterBit, liftSharedBit,
    rawSharedBit, sharedWorkEncoding, sharedWorkTupleEncoding,
    coeffAdderWorkEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

/-- The shared route/path bit is disjoint from every correction-counter bit. -/
theorem pathBit_correctionCounterBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (counterWidth - 1)) :
    (pathBit n counterWidth).wire ≠
      (correctionCounterBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp [pathBit, sharedPathBit, rawPathBit, correctionCounterBit,
    sharedCorrectionCounterBit, rawCorrectionCounterBit, liftSharedBit,
    rawSharedBit, sharedWorkEncoding, sharedWorkTupleEncoding,
    coeffAdderWorkEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

/-- The shared route/path and control bits occupy distinct wires. -/
theorem pathBit_controlBit_wire_ne (n counterWidth : Nat) :
    (pathBit n counterWidth).wire ≠ (controlBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp [pathBit, sharedPathBit, rawPathBit, controlBit, sharedControlBit,
    rawControlBit, liftSharedBit, rawSharedBit, sharedWorkEncoding,
    sharedWorkTupleEncoding, coeffAdderWorkEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]

/-- A correction-counter bit is disjoint from every borrowed VBE carry bit. -/
theorem correctionCounterBit_coefficientCarryWorkBit_wire_ne
    (n counterWidth : Nat) (counterBit : Fin (counterWidth - 1))
    (workBit : Fin n) :
    (correctionCounterBit n counterWidth counterBit).wire ≠
      (coefficientCarryWorkBit n counterWidth workBit).wire := by
  apply Fin.ne_of_val_ne
  simp [correctionCounterBit, sharedCorrectionCounterBit,
    rawCorrectionCounterBit, coefficientCarryWorkBit,
    sharedCoefficientCarryWorkBit, rawCoefficientCarryWorkBit, liftSharedBit,
    rawSharedBit, sharedWorkEncoding, sharedWorkTupleEncoding,
    coeffAdderWorkEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

/-- The shared control bit is disjoint from every borrowed VBE carry bit. -/
theorem controlBit_coefficientCarryWorkBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (controlBit n counterWidth).wire ≠
      (coefficientCarryWorkBit n counterWidth workBit).wire := by
  apply Fin.ne_of_val_ne
  simp [controlBit, sharedControlBit, rawControlBit,
    coefficientCarryWorkBit, sharedCoefficientCarryWorkBit,
    rawCoefficientCarryWorkBit, liftSharedBit, rawSharedBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    wordEncoding, PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

/-- The shared route/path bit is disjoint from every borrowed VBE carry bit. -/
theorem pathBit_coefficientCarryWorkBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (pathBit n counterWidth).wire ≠
      (coefficientCarryWorkBit n counterWidth workBit).wire := by
  apply Fin.ne_of_val_ne
  simp [pathBit, sharedPathBit, rawPathBit,
    coefficientCarryWorkBit, sharedCoefficientCarryWorkBit,
    rawCoefficientCarryWorkBit, liftSharedBit, rawSharedBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    wordEncoding, PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

/-- Lifting distinct core bits into the compact carrier preserves wire
distinctness. -/
theorem liftCoreBit_wire_ne (n counterWidth : Nat)
    {left right : EncodedBit (registerEncoding n counterWidth)}
    (hne : left.wire ≠ right.wire) :
    (liftCoreBit n counterWidth left).wire ≠
      (liftCoreBit n counterWidth right).wire := by
  intro hw
  apply hne
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [liftCoreBit, rawCoreBit, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodLeftWire, EncodedBit.relabel] using hval

/-- Every compact core bit is disjoint from every bit of the shared VBE carry
bank. -/
theorem liftCoreBit_coefficientCarryWorkBit_wire_ne
    (n counterWidth : Nat)
    (coreBit : EncodedBit (registerEncoding n counterWidth))
    (workBit : Fin n) :
    (liftCoreBit n counterWidth coreBit).wire ≠
      (coefficientCarryWorkBit n counterWidth workBit).wire := by
  intro hw
  have hval := congrArg Fin.val hw
  have hcore := coreBit.wire.isLt
  simp [liftCoreBit, rawCoreBit, coefficientCarryWorkBit, liftSharedBit,
    rawSharedBit, sharedCoefficientCarryWorkBit,
    rawCoefficientCarryWorkBit, sharedWorkEncoding,
    sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel] at hval hcore
  omega

/-- Every compact core bit is disjoint from the VBE carry-in bit. -/
theorem liftCoreBit_coefficientCarryInBit_wire_ne
    (n counterWidth : Nat)
    (coreBit : EncodedBit (registerEncoding n counterWidth)) :
    (liftCoreBit n counterWidth coreBit).wire ≠
      (coefficientCarryInBit n counterWidth).wire := by
  intro hw
  have hval := congrArg Fin.val hw
  have hcore := coreBit.wire.isLt
  simp [liftCoreBit, rawCoreBit, coefficientCarryInBit, liftSharedBit,
    rawSharedBit, sharedCoefficientCarryInBit,
    rawCoefficientCarryInBit, sharedWorkEncoding,
    sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel] at hval hcore
  omega

/-- The VBE carry-in is disjoint from every temporary carry-work bit. -/
theorem coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (coefficientCarryInBit n counterWidth).wire ≠
      (coefficientCarryWorkBit n counterWidth bit).wire := by
  apply Fin.ne_of_val_ne
  simp [coefficientCarryInBit, liftSharedBit, rawSharedBit,
    sharedCoefficientCarryInBit, rawCoefficientCarryInBit,
    coefficientCarryWorkBit, sharedCoefficientCarryWorkBit,
    rawCoefficientCarryWorkBit, sharedWorkEncoding,
    sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

/-- The literal-load control bit is disjoint from the VBE carry-in bit. -/
theorem controlBit_coefficientCarryInBit_wire_ne
    (n counterWidth : Nat) :
    (controlBit n counterWidth).wire ≠
      (coefficientCarryInBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp [controlBit, sharedControlBit, rawControlBit,
    coefficientCarryInBit, sharedCoefficientCarryInBit,
    rawCoefficientCarryInBit, liftSharedBit, rawSharedBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.boolBit, EncodedBit.relabel]

/-- The route/path bit is disjoint from the reusable VBE carry-in bit. -/
theorem pathBit_coefficientCarryInBit_wire_ne
    (n counterWidth : Nat) :
    (pathBit n counterWidth).wire ≠
      (coefficientCarryInBit n counterWidth).wire := by
  apply Fin.ne_of_val_ne
  simp [pathBit, sharedPathBit, rawPathBit,
    coefficientCarryInBit, sharedCoefficientCarryInBit,
    rawCoefficientCarryInBit, liftSharedBit, rawSharedBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.boolBit, EncodedBit.relabel]

/-- Distinct indices select distinct bits of the shared VBE carry bank. -/
theorem coefficientCarryWorkBit_wire_ne
    (n counterWidth : Nat) {left right : Fin n} (hne : left ≠ right) :
    (coefficientCarryWorkBit n counterWidth left).wire ≠
      (coefficientCarryWorkBit n counterWidth right).wire := by
  intro hw
  apply hne
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [coefficientCarryWorkBit, liftSharedBit, rawSharedBit,
    sharedCoefficientCarryWorkBit, rawCoefficientCarryWorkBit,
    sharedWorkEncoding, sharedWorkTupleEncoding, coeffAdderWorkEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel] using hval

/-! ### Common compact core lenses -/

/-- Little-endian `u` word in the compact inversion carrier. -/
def uValueWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) n where
  bit := fun bit => liftCoreBit n counterWidth
    (RegisterBits.uValueBit n counterWidth bit)

/-- Little-endian `v` word in the compact inversion carrier. -/
def vValueWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) n where
  bit := fun bit => liftCoreBit n counterWidth
    (RegisterBits.vValueBit n counterWidth bit)

/-- Core comparison-result bit in the compact inversion carrier. -/
def compareBit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  liftCoreBit n counterWidth (RegisterBits.compareBit n counterWidth)

/-- Core clean initial-borrow bit in the compact inversion carrier. -/
def scratchABit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  liftCoreBit n counterWidth (RegisterBits.scratchABit n counterWidth)

/-- Core clean control-work bit in the compact inversion carrier.  Unlike
`scratchA`, this bit is not borrowed by the VBE source-subtract schedule, so
it can control that schedule through a clean-work lift. -/
def scratchBBit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  liftCoreBit n counterWidth (RegisterBits.scratchBBit n counterWidth)

/-- Core active-round flag in the compact inversion carrier. -/
def activeBit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  liftCoreBit n counterWidth (RegisterBits.activeBit n counterWidth)

/-- One bit of the sole persistent `2n` branch-history word in the compact
inversion carrier. -/
def historyBit (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit (encoding n counterWidth) :=
  liftCoreBit n counterWidth (RegisterBits.historyBit n counterWidth bit)

/-- The sole persistent branch-history word in the compact carrier. -/
def historyWord (n counterWidth : Nat) :
    EncodedBit.Word (encoding n counterWidth) (2 * n) where
  bit := historyBit n counterWidth

@[simp] theorem uValueWord_get (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    ((uValueWord n counterWidth).bit bit).get x =
      x.core.u.val.testBit bit.val := by
  change (RegisterBits.uValueBit n counterWidth bit).get x.core = _
  exact RegisterBits.uValueBit_get n counterWidth bit x.core

@[simp] theorem vValueWord_get (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    ((vValueWord n counterWidth).bit bit).get x =
      x.core.v.val.testBit bit.val := by
  change (RegisterBits.vValueBit n counterWidth bit).get x.core = _
  exact RegisterBits.vValueBit_get n counterWidth bit x.core

@[simp] theorem compareBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (compareBit n counterWidth).get x = x.core.compare := by
  change (RegisterBits.compareBit n counterWidth).get x.core = _
  exact RegisterBits.compareBit_get n counterWidth x.core

@[simp] theorem scratchABit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get x = x.core.scratchA := by
  change (RegisterBits.scratchABit n counterWidth).get x.core = _
  exact RegisterBits.scratchABit_get n counterWidth x.core

@[simp] theorem scratchBBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (scratchBBit n counterWidth).get x = x.core.scratchB := by
  change (RegisterBits.scratchBBit n counterWidth).get x.core = _
  exact RegisterBits.scratchBBit_get n counterWidth x.core

@[simp] theorem activeBit_get (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    (activeBit n counterWidth).get x = x.core.active := by
  change (RegisterBits.activeBit n counterWidth).get x.core = _
  exact RegisterBits.activeBit_get n counterWidth x.core

@[simp] theorem historyBit_get (n counterWidth : Nat)
    (bit : Fin (2 * n)) (x : Registers n counterWidth) :
    (historyBit n counterWidth bit).get x =
      x.core.history.val.testBit (WireAddress.bitIndex bit).val := by
  change (RegisterBits.historyBit n counterWidth bit).get x.core = _
  exact RegisterBits.historyBit_get n counterWidth bit x.core

/-- The compact active flag is disjoint from the first scratch bit. -/
theorem activeBit_scratchABit_wire_ne (n counterWidth : Nat) :
    (activeBit n counterWidth).wire ≠
      (scratchABit n counterWidth).wire := by
  simpa [activeBit, scratchABit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_scratchA_wire_ne n counterWidth)

/-- The compact active flag is disjoint from the second scratch bit. -/
theorem activeBit_scratchBBit_wire_ne (n counterWidth : Nat) :
    (activeBit n counterWidth).wire ≠
      (scratchBBit n counterWidth).wire := by
  simpa [activeBit, scratchBBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_scratchB_wire_ne n counterWidth)

/-- The compact active and comparison flags occupy distinct wires. -/
theorem activeBit_compareBit_wire_ne (n counterWidth : Nat) :
    (activeBit n counterWidth).wire ≠
      (compareBit n counterWidth).wire := by
  simpa [activeBit, compareBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_compare_wire_ne n counterWidth)

/-- The compact active flag is disjoint from every history slot. -/
theorem activeBit_historyBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (activeBit n counterWidth).wire ≠
      (historyBit n counterWidth bit).wire := by
  simpa [activeBit, historyBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_history_wire_ne n counterWidth bit)

/-- The first compact scratch bit is disjoint from every history slot. -/
theorem scratchABit_historyBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (scratchABit n counterWidth).wire ≠
      (historyBit n counterWidth bit).wire := by
  simpa [scratchABit, historyBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.scratchA_history_wire_ne n counterWidth bit)

/-- The second compact scratch bit is disjoint from every history slot. -/
theorem scratchBBit_historyBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (scratchBBit n counterWidth).wire ≠
      (historyBit n counterWidth bit).wire := by
  simpa [scratchBBit, historyBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.scratchB_history_wire_ne n counterWidth bit)

/-- The compact comparison flag is disjoint from every history slot. -/
theorem compareBit_historyBit_wire_ne
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (compareBit n counterWidth).wire ≠
      (historyBit n counterWidth bit).wire := by
  simpa [compareBit, historyBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.compare_history_wire_ne n counterWidth bit)

/-- Distinct compact history indices occupy distinct wires. -/
theorem historyBit_wire_ne
    (n counterWidth : Nat) {left right : Fin (2 * n)}
    (hne : left ≠ right) :
    (historyBit n counterWidth left).wire ≠
      (historyBit n counterWidth right).wire := by
  simpa [historyBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.history_history_wire_ne n counterWidth hne)

/-- The compact comparison bit is disjoint from the spare source-control
work bit. -/
theorem compareBit_scratchBBit_wire_ne (n counterWidth : Nat) :
    (compareBit n counterWidth).wire ≠
      (scratchBBit n counterWidth).wire := by
  simpa [compareBit, scratchBBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)

/-- The VBE source-subtract carry-in and spare source-control work bit are
distinct compact wires. -/
theorem scratchABit_scratchBBit_wire_ne (n counterWidth : Nat) :
    (scratchABit n counterWidth).wire ≠
      (scratchBBit n counterWidth).wire := by
  simpa [scratchABit, scratchBBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.scratchA_scratchB_wire_ne n counterWidth)

/-- The compact comparison bit is disjoint from the VBE source-subtract
carry-in and may therefore control a coefficient-add wrapper that borrows
that restored bit as clean work. -/
theorem compareBit_scratchABit_wire_ne (n counterWidth : Nat) :
    (compareBit n counterWidth).wire ≠
      (scratchABit n counterWidth).wire := by
  simpa [compareBit, scratchABit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)

theorem coefficientCarryWorkBit_get_clean
    (n counterWidth : Nat) (bit : Fin n)
    (core : MK.Registers n counterWidth) (target : Word n) :
    (coefficientCarryWorkBit n counterWidth bit).get
        { core := core
          shared := cleanSharedWork n counterWidth
          target := target } = false := by
  change (BinaryLabelEncoding.finIdentityBit n bit).get
      (0 : Fin (2 ^ n)) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit

theorem coefficientCarryInBit_get_clean
    (n counterWidth : Nat)
    (core : MK.Registers n counterWidth) (target : Word n) :
    (coefficientCarryInBit n counterWidth).get
        { core := core
          shared := cleanSharedWork n counterWidth
          target := target } = false := by
  rfl

@[simp] theorem sharedWorkEncoding_width (n counterWidth : Nat) :
    (sharedWorkEncoding n counterWidth).width =
      (1 + n) + ((counterWidth - 1) + 2) := by
  rfl

/-- The compact carrier width before replacing the `2n` counter width by the
equivalent `clog₂ n + 1` expression. -/
theorem encoding_width_exact (n counterWidth : Nat)
    (hcounter : 0 < counterWidth) :
    (encoding n counterWidth).width = 8 * n + 2 * counterWidth + 8 := by
  simp only [encoding, registerTupleEncoding, BinaryLabelEncoding.relabel_width,
    BinaryLabelEncoding.prod_width, registerEncoding_width,
    sharedWorkEncoding_width, wordEncoding_width]
  omega

/-- Multiplication by the binary radix increases positive-input ceiling-log
width by exactly one. -/
theorem clog_two_mul_eq_add_one (n : Nat) (hn : 0 < n) :
    Nat.clog 2 (2 * n) = Nat.clog 2 n + 1 := by
  have hdivide : (2 * n + 2 - 1) / 2 = n := by
    omega
  rw [Nat.clog_of_two_le (by omega : 1 < (2 : Nat)) (by omega)]
  rw [hdivide]

/-- Counter width used by the exact `2n` fixed-round schedule. -/
def counterWidthFor (n : Nat) : Nat :=
  Nat.clog 2 (2 * n)

/-- Canonical compact encoding at the fixed-round counter width. -/
def encodingFor (n : Nat) :
    BinaryLabelEncoding (Registers n (counterWidthFor n)) :=
  encoding n (counterWidthFor n)

/-- Exact width promised by the VBE-retaining compression boundary. -/
theorem encodingFor_width_exact (n : Nat) (hn : 0 < n) :
    (encodingFor n).width = 8 * n + 2 * Nat.clog 2 n + 10 := by
  have hcounter : 0 < counterWidthFor n := by
    unfold counterWidthFor
    exact Nat.clog_pos (by omega) (by omega)
  rw [encodingFor, encoding_width_exact n (counterWidthFor n) hcounter,
    counterWidthFor, clog_two_mul_eq_add_one n hn]
  omega

/-- The compact P-256 inversion carrier has 2074 logical qubits. -/
theorem encodingFor_256_width : (encodingFor 256).width = 2074 := by
  rw [encodingFor_width_exact 256 (by omega)]
  norm_num

end Compact

end
end MK
end MAU.Inversion
end QuantumAlg

end
