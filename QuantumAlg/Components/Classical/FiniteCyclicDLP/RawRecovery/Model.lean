/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Model
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.TerminalDecode
import all QuantumAlg.Util.Classical.NumberTheory.Checked

/-!
# Pure raw Fourier recovery

The original big-endian decoding, integer frequency rescaling and checked
inverse determine the same optional candidate and reconstruction flag.
These existing definitions and elementary identities are separated from
machine allocation and execution, without adding a runtime inverse input.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery

open ClassicalAlgorithms
open ClassicalAlgorithms.Modular

/-- One retained terminal outcome consists of two consecutive `width`-bit
Fourier registers. -/
abbrev InputShape (width : Nat) : CShape :=
  .bits (width + width)

/-- Failure of the unit check, or the recovered candidate and its independent
reconstruction flag. -/
abbrev OutputShape (width : Nat) : CShape :=
  .option (FiniteCyclicDLP.OutputShape width)

/-- Interpret the retained terminal cell in the Core full-register convention.
The left register occupies the most-significant half. -/
def decodedTerminal {width : Nat}
    (input : CShape.Value (InputShape width)) : Nat :=
  match input with
  | .bits bits =>
      ClassicalAlgorithms.TerminalDecode.decodeNat
        { order := .bigEndian, bits := bits }

/-- High terminal register before order rescaling. -/
def leftRaw {width : Nat} (input : CShape.Value (InputShape width)) : Nat :=
  decodedTerminal input / 2 ^ width

/-- Low terminal register before order rescaling. -/
def rightRaw {width : Nat} (input : CShape.Value (InputShape width)) : Nat :=
  decodedTerminal input % 2 ^ width

/-- The integer Fourier-frequency rescaling used by finite-cyclic DLP. -/
def scaleFrequency {width : Nat} (spec : ModulusSpec width) (raw : Nat) :
    Residue spec :=
  Residue.ofNat spec (raw * spec.modulus / 2 ^ width)

/-- Normalized left and right frequencies produced from the retained raw
measurement. -/
structure NormalizedInput {width : Nat} (spec : ModulusSpec width) where
  /-- The order-normalized left Fourier frequency. -/
  left : Residue spec
  /-- The order-normalized right Fourier frequency. -/
  right : Residue spec

/-- Convert one raw retained terminal result into its two order-normalized
frequencies. -/
def normalize {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width)) : NormalizedInput spec :=
  { left := scaleFrequency spec (leftRaw input)
    right := scaleFrequency spec (rightRaw input) }

/-- The additive inverse of one normalized right frequency, represented in the
canonical residue carrier without introducing a host-level operation. -/
def negateRight {width : Nat} (spec : ModulusSpec width)
    (input : NormalizedInput spec) : Residue spec :=
  Residue.ofNat spec (spec.modulus - input.right.val)

/-- The pure normalized input consumed by the reusable typed recovery core
when the checked inverse succeeds. -/
def helperInput {width : Nat} (spec : ModulusSpec width)
    (input : NormalizedInput spec) (inverse : Residue spec) :
    FiniteCyclicDLP.Input spec :=
  { leftFrequency := input.left
    negatedRightFrequency := negateRight spec input
    leftInverse := inverse }

/-- Exact semantic result of the raw-terminal recovery: a nonunit left
frequency produces `none`; otherwise the candidate is recovered and verified
by the same typed core used by the machine implementation. -/
def outputOf {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width)) : Option (FiniteCyclicDLP.Output spec) :=
  let normalized := normalize spec input
  match ClassicalAlgorithms.NumberTheory.TryInv.eval spec normalized.left with
  | none => none
  | some inverse => some (FiniteCyclicDLP.outputOf spec
      (helperInput spec normalized inverse))

/-- The raw terminal model has no externally supplied inverse, rounding, or
classical callback: all three are fixed by `outputOf`. -/
theorem outputOf_checked_inverse {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width)) :
    outputOf spec input =
      match ClassicalAlgorithms.NumberTheory.TryInv.eval spec
        (normalize spec input).left with
      | none => none
      | some inverse => some (FiniteCyclicDLP.outputOf spec
          (helperInput spec (normalize spec input) inverse) ) := by
  rfl

private theorem outputOf_some_elim {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width)) (output : FiniteCyclicDLP.Output spec)
    (selected : outputOf spec input = some output) :
    ∃ inverse,
      ClassicalAlgorithms.NumberTheory.TryInv.eval spec
          (normalize spec input).left = some inverse ∧
        output = FiniteCyclicDLP.outputOf spec
          (helperInput spec (normalize spec input) inverse) := by
  unfold outputOf at selected
  cases inverseResult :
      ClassicalAlgorithms.NumberTheory.TryInv.eval spec
        (normalize spec input).left with
  | none => simp [inverseResult] at selected
  | some inverse =>
      refine ⟨inverse, ?_, ?_⟩
      · rfl
      · simpa [inverseResult] using selected.symm

/-- The exact three-cell observation exposed by the public raw-recovery seam.
On checked-inverse failure, the closed machine leaves its fresh candidate and
reconstruction cells at their zero initialization.  On success, it exposes
the candidate and independent reconstruction bit of the shared typed core. -/
def outputCells {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width)) :
    CShape.Value (.product .bit (.product (.unsignedWord width) .bit)) :=
  match outputOf spec input with
  | none => .product (.bit false)
      (.product (CShape.wordOfNat width 0) (.bit false))
  | some output => .product (.bit true)
      (.product (CShape.wordOfNat width output.candidate.val) (.bit output.verified))

/-- Expand the public three-cell result on an unsuccessful pure recovery. -/
theorem outputCells_of_outputOf_none {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width))
    (failure : outputOf spec input = none) :
    outputCells spec input =
      .product (.bit false)
        (.product (CShape.wordOfNat width 0) (.bit false)) := by
  unfold outputCells
  rw [failure]

/-- Expand the public three-cell result on a successful pure recovery. -/
theorem outputCells_of_outputOf_some {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width)) (output : FiniteCyclicDLP.Output spec)
    (success : outputOf spec input = some output) :
    outputCells spec input =
      .product (.bit true)
        (.product (CShape.wordOfNat width output.candidate.val) (.bit output.verified)) := by
  unfold outputCells
  rw [success]

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery
