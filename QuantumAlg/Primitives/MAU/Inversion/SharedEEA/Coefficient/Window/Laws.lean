/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Laws

/-!
# Exact word laws of the actual little-endian coefficient arithmetic

The native coefficient program reads Work1 as its source and Work2 as its
target in the physical little-endian prefix order. Its unchanged suffix
retains every rotated fractional bit
[LYL+26, sec_EEA/sub_regshare.tex:17,20,263-264,291-294]. The existing TTK
complete-word laws give the actual signed addition and low subtraction on
these precise regions [TTK09, qic-loglogaddition-quant.tex:285-318;
HRS16, paper.tex:217-225]. Reversing the mathematical reading order does not
emit a new gate or discard any original bit.

These all-input equations connect the already implemented physical program
to finite-word arithmetic, with arbitrary Sign, Iter, Ctrl, and outside
contents. The phase-specific reachable integer/fraction invariant and the
interposed Sign gate are subsequently connected at their actual owners.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowLaws

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram

/-- The actual Work1 coefficient slice, read in its physical little-endian order. -/
def sourceWord {width : Nat} (window : Window width) (state : Registers width) :
    BitVec window.length :=
  (state.firstWord.extractLsb' window.below window.length).reverse

/-- The actual aligned integer slice of Work2; its wrapped suffix remains outside this word. -/
def targetWord {width : Nat} (window : Window width) (state : Registers width) :
    BitVec window.length :=
  (state.secondWord.extractLsb' window.below window.length).reverse

/-- The actual old Sign followed by the entire aligned coefficient integer word. -/
def signedTarget {width : Nat} (window : Window width) (state : Registers width) :
    BitVec (window.length + 1) :=
  BitVec.cons state.flags.sign (targetWord window state)

private theorem sourceWord_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    sourceWord window state =
      BitVec.ofFin (CoefficientWindowOrientation.grouping window state).1.1.1 := by
  rw [CoefficientWindowOrientation.grouping_source]
  apply BitVec.eq_of_toNat_eq
  rfl

private theorem targetWord_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    targetWord window state =
      BitVec.ofFin (CoefficientWindowOrientation.grouping window state).1.1.2 := by
  rw [CoefficientWindowOrientation.grouping_target]
  apply BitVec.eq_of_toNat_eq
  rfl

private theorem signedTarget_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    signedTarget window state =
      Addition.TTK.outputWord (CoefficientWindowOrientation.grouping window state).1 := by
  unfold signedTarget Addition.TTK.outputWord
  rw [targetWord_grouping, CoefficientWindowOrientation.grouping_sign]

/-- The actual original Work1 source word is unchanged by every coefficient arithmetic mode. -/
theorem step_sourceWord {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    sourceWord window (CoefficientWindowProgram.step window operation state) =
      sourceWord window state := by
  rw [sourceWord_grouping, CoefficientWindowProgram.step_grouping, sourceWord_grouping]
  exact congrArg BitVec.ofFin
    (focusStep_source operation (CoefficientWindowOrientation.grouping window state).1)

/-- All original outside bits, including the wrapped fractional suffix, retain their joint value. -/
theorem step_complement {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (CoefficientWindowOrientation.grouping window
      (CoefficientWindowProgram.step window operation state)).2 =
        (CoefficientWindowOrientation.grouping window state).2 := by
  rw [CoefficientWindowProgram.step_grouping]

/-- The same actual native signed addition acts on the full coefficient word and original Sign. -/
theorem step_signed_add {width : Nat} (window : Window width) (state : Registers width) :
    signedTarget window (CoefficientWindowProgram.step window .addSigned state) =
      signedTarget window state + (sourceWord window state).setWidth (window.length + 1) := by
  rw [signedTarget_grouping, CoefficientWindowProgram.step_grouping, signedTarget_grouping,
    sourceWord_grouping]
  exact Addition.TTK.ttkOverflowOutput_word (CoefficientWindowOrientation.grouping window state).1

/-- Reversing that same TTK list gives complete signed subtraction at the coefficient wires. -/
theorem step_signed_subtract {width : Nat} (window : Window width) (state : Registers width) :
    signedTarget window (CoefficientWindowProgram.step window .subtractSigned state) =
      signedTarget window state - (sourceWord window state).setWidth (window.length + 1) := by
  rw [signedTarget_grouping, CoefficientWindowProgram.step_grouping, signedTarget_grouping,
    sourceWord_grouping]
  exact Addition.TTK.ttkOverflowSubtractionOutput_word
    (CoefficientWindowOrientation.grouping window state).1

/-- Actual low addition updates precisely the current integer part modulo its physical width. -/
theorem step_low_add {width : Nat} (window : Window width) (state : Registers width) :
    targetWord window (CoefficientWindowProgram.step window .addLow state) =
      targetWord window state + sourceWord window state := by
  rw [targetWord_grouping, CoefficientWindowProgram.step_grouping, targetWord_grouping,
    sourceWord_grouping]
  exact ArithmeticWindowLaws.focus_low_add (CoefficientWindowOrientation.grouping window state).1

/-- Actual low subtraction retains the original Sign and all wrapped fractional bits. -/
theorem step_low_subtract {width : Nat} (window : Window width) (state : Registers width) :
    targetWord window (CoefficientWindowProgram.step window .subtractLow state) =
      targetWord window state - sourceWord window state := by
  rw [targetWord_grouping, CoefficientWindowProgram.step_grouping, targetWord_grouping,
    sourceWord_grouping]
  exact ArithmeticWindowLaws.focus_low_subtract
    (CoefficientWindowOrientation.grouping window state).1

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowLaws
