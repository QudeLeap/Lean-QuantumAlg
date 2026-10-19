/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Program
import all QuantumAlg.Primitives.MAU.Addition.TTK.WordSemantics
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Division

/-!
# Exact finite-word laws of the actual physical remainder arithmetic

The operands below are the literal same-position slices of the original
work words. The existing TTK gate programs therefore perform finite signed
or low-word addition/subtraction on those actual bits, retaining every
outside coordinate [TTK09, qic-loglogaddition-quant.tex:285-318;
HRS16, paper.tex:217-225]. The signed operand retains the original Sign
followed by the full old remainder region
[LYL+26, sec_EEA/sub_regshare.tex:278-287].

No low remainder bit is discarded before subtraction. With the internally
established zero Sign, the complete executed subtraction word equals the
previously proved `SignedDivision.difference`; its sign is the strict
underflow predicate, so equality takes the nonborrowed branch. The word
laws allow zero-length windows and arbitrary complementary quantum values.
Establishing the reachable dynamic window and subsequent quotient exchange
is a separate packed-state refinement obligation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowLaws

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram

/-- Literal complete old remainder slice in Work1, without removing its highest bit. -/
def targetWord {width : Nat} (window : Window width) (state : Registers width) :
    BitVec window.length :=
  (wordEquiv window state.firstWord).2.1

/-- Literal same-position source slice in Work2, excluding its independently retained suffix. -/
def sourceWord {width : Nat} (window : Window width) (state : Registers width) :
    BitVec window.length :=
  (wordEquiv window state.secondWord).2.1

/-- The actual original Sign bit followed by the entire old remainder region. -/
def signedTarget {width : Nat} (window : Window width) (state : Registers width) :
    BitVec (window.length + 1) :=
  BitVec.cons state.flags.sign (targetWord window state)

private lemma sourceWord_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    sourceWord window state = BitVec.ofFin (grouping window state).1.1.1 := by
  apply BitVec.eq_of_toNat_eq
  rfl

private lemma targetWord_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    targetWord window state = BitVec.ofFin (grouping window state).1.1.2 := by
  apply BitVec.eq_of_toNat_eq
  rfl

private lemma signedTarget_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    signedTarget window state = Addition.TTK.outputWord (grouping window state).1 := by
  unfold signedTarget Addition.TTK.outputWord
  rw [targetWord_grouping]
  rfl

/-- The native arithmetic source operand retains its entire original physical word. -/
lemma step_sourceWord {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    sourceWord window (ArithmeticWindowProgram.step window operation state) =
      sourceWord window state := by
  rw [sourceWord_grouping, step_grouping, sourceWord_grouping]
  exact congrArg BitVec.ofFin (focusStep_source operation (grouping window state).1)

/-- Every outside word bit, length, phase, Iter, and Ctrl stays in the same exact complement. -/
lemma step_complement {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (grouping window (ArithmeticWindowProgram.step window operation state)).2 =
      (grouping window state).2 := by
  rw [step_grouping]

/-- The actual signed TTK addition acts on the full old target and arbitrary incoming Sign. -/
lemma step_signed_add {width : Nat} (window : Window width) (state : Registers width) :
    signedTarget window (ArithmeticWindowProgram.step window .addSigned state) =
      signedTarget window state + (sourceWord window state).setWidth (window.length + 1) := by
  rw [signedTarget_grouping, step_grouping, signedTarget_grouping, sourceWord_grouping]
  exact Addition.TTK.ttkOverflowOutput_word (grouping window state).1

/-- The actual reversed TTK list subtracts on that same complete signed physical region. -/
lemma step_signed_subtract {width : Nat} (window : Window width) (state : Registers width) :
    signedTarget window (ArithmeticWindowProgram.step window .subtractSigned state) =
      signedTarget window state - (sourceWord window state).setWidth (window.length + 1) := by
  rw [signedTarget_grouping, step_grouping, signedTarget_grouping, sourceWord_grouping]
  exact Addition.TTK.ttkOverflowSubtractionOutput_word (grouping window state).1

private lemma focus_low_add {length : Nat} (state : Addition.TTK.OverflowRegisters length) :
    BitVec.ofFin (focusStep .addLow state).1.2 =
      BitVec.ofFin state.1.2 + BitVec.ofFin state.1.1 := by
  have actual := congrArg (fun word : BitVec (length + 1) => word.setWidth length)
    (Addition.TTK.ttkOverflowOutput_word state)
  have narrower : length ≤ length + 1 := by omega
  simpa only [focusStep, Addition.TTK.overflowOutput,
    Addition.TTK.outputWord, BitVec.setWidth_add _ _ narrower, BitVec.setWidth_cons,
    BitVec.setWidth_setWidth_of_le _ narrower, BitVec.setWidth_eq] using actual

private lemma focus_low_subtract {length : Nat} (state : Addition.TTK.OverflowRegisters length) :
    BitVec.ofFin (focusStep .subtractLow state).1.2 =
      BitVec.ofFin state.1.2 - BitVec.ofFin state.1.1 := by
  have actual := congrArg (fun word : BitVec (length + 1) => word.setWidth length)
    (Addition.TTK.ttkOverflowSubtractionOutput_word state)
  have narrower : length ≤ length + 1 := by omega
  simpa only [focusStep, Addition.TTK.overflowSubtractionOutput,
    Addition.TTK.outputWord, BitVec.sub_eq_add_neg,
    BitVec.setWidth_add _ _ narrower, BitVec.setWidth_cons,
    BitVec.setWidth_neg_of_le narrower, BitVec.setWidth_setWidth_of_le _ narrower,
    BitVec.setWidth_eq] using actual

/-- The actual low addition modifies precisely the full selected remainder word modulo its width. -/
lemma step_low_add {width : Nat} (window : Window width) (state : Registers width) :
    targetWord window (ArithmeticWindowProgram.step window .addLow state) =
      targetWord window state + sourceWord window state := by
  rw [targetWord_grouping, step_grouping, targetWord_grouping, sourceWord_grouping]
  exact focus_low_add (grouping window state).1

/-- The actual low subtraction is the matching finite-word subtraction on the original slice. -/
lemma step_low_subtract {width : Nat} (window : Window width) (state : Registers width) :
    targetWord window (ArithmeticWindowProgram.step window .subtractLow state) =
      targetWord window state - sourceWord window state := by
  rw [targetWord_grouping, step_grouping, targetWord_grouping, sourceWord_grouping]
  exact focus_low_subtract (grouping window state).1

private lemma cons_false_eq_setWidth {length : Nat} (word : BitVec length) :
    BitVec.cons false word = word.setWidth (length + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cons', Bool.toNat_false, Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_add,
    BitVec.toNat_setWidth_of_le (by omega : length ≤ length + 1)]

/-- Internal zero Sign connects the actual full-width subtraction to the pure division law. -/
lemma step_subtract_difference {width : Nat} (window : Window width) (state : Registers width)
    (zeroSign : state.flags.sign = false) :
    signedTarget window (ArithmeticWindowProgram.step window .subtractSigned state) =
      NumberTheory.SharedEEA.SignedDivision.difference
        (targetWord window state) (sourceWord window state) := by
  rw [step_signed_subtract, signedTarget, zeroSign, cons_false_eq_setWidth]
  rfl

/-- The actual subtraction Sign is strict underflow, including equal and zero-bit inputs. -/
lemma step_subtract_sign {width : Nat} (window : Window width) (state : Registers width)
    (zeroSign : state.flags.sign = false) :
    (ArithmeticWindowProgram.step window .subtractSigned state).flags.sign =
      decide ((targetWord window state).toNat < (sourceWord window state).toNat) := by
  have actual := congrArg BitVec.msb (step_subtract_difference window state zeroSign)
  simpa only [signedTarget, BitVec.msb_cons,
    NumberTheory.SharedEEA.SignedDivision.difference_sign] using actual

/-- All old remainder bits survive until the signed subtraction has actually been executed. -/
lemma step_subtract_low {width : Nat} (window : Window width) (state : Registers width)
    (zeroSign : state.flags.sign = false) :
    targetWord window (ArithmeticWindowProgram.step window .subtractSigned state) =
      targetWord window state - sourceWord window state := by
  have actual := congrArg (fun word : BitVec (window.length + 1) => word.setWidth window.length)
    (step_subtract_difference window state zeroSign)
  simpa only [signedTarget, BitVec.setWidth_cons,
    NumberTheory.SharedEEA.SignedDivision.difference_low] using actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowLaws
