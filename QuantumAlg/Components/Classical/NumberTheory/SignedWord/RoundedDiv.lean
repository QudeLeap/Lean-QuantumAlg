/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Layout
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification.Normalization

/-!
# Actual rounded signed division

The native circuit obtains a sign and unsigned magnitude, widens the
operands, forms the corrected dividend, performs one quotient-and-remainder
instruction, and restores the quotient's sign. The original caller supplies
all cells. No initialized scratch, extra allocation, or alternative routine
interpreter is used. The two rounding branches retain the same nearest-integer
formulas, including the negative tie correction.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Copy the actual normalized magnitude into its one-bit-wider dividend cell. -/
def resizeMagnitudeOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx (writeInput refs.magnitude) refs.wideNumerator

/-- Double the widened magnitude in the actual dividend cell. -/
def doubleNumeratorOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord (width + 1)) ctx ctx :=
  .wordUnary .shiftLeft (width + 1) ctx (writeInput refs.wideNumerator) refs.wideNumerator

/-- Resize the original positive denominator into its actual wider cell. -/
def resizeDenominatorOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx refs.denominator refs.wideDenominator

/-- Add the widened denominator to the doubled magnitude. -/
def addDenominatorOp (refs : BodyRefs ctx width) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
      (.unsignedWord (width + 1)) ctx ctx :=
  .wordBinary .add (width + 1) ctx
    (.product (writeInput refs.wideNumerator) (writeInput refs.wideDenominator)) refs.wideNumerator

/-- Correct negative nearest-integer ties by subtracting one from the actual dividend. -/
def correctNumeratorOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord (width + 1)) ctx ctx :=
  .wordUnary .decrement (width + 1) ctx (writeInput refs.wideNumerator) refs.wideNumerator

/-- The divisor in the nearest-integer formula is twice the original denominator. -/
def doubleDenominatorOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord (width + 1)) ctx ctx :=
  .wordUnary .shiftLeft (width + 1) ctx (writeInput refs.wideDenominator) refs.wideDenominator

/-- The one real quotient-and-remainder instruction. -/
def divideOp (refs : BodyRefs ctx width) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
      (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1))) ctx ctx :=
  .divRem (width + 1) (width + 1) ctx
    (.product (writeInput refs.wideNumerator) (writeInput refs.wideDenominator)) refs.division

/-- Read the actual quotient field and truncate it into the raw output word. -/
def resizeQuotientOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord width) ctx ctx :=
  .wordResize (width + 1) width ctx (.first (writeInput refs.division)) refs.output

/-- First native instruction of the final two's-complement sign restoration. -/
def complementOutputOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .complement width ctx (writeInput refs.output) refs.output

/-- Second native instruction of the final sign restoration. -/
def incrementOutputOp (refs : BodyRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (writeInput refs.output) refs.output

/-- Actual sign classification and magnitude normalization accept arbitrary initial scratch. -/
def normalizeMagnitude (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  SignedWord.normalizeMagnitude refs.numerator refs.negative refs.magnitude

/-- The actual resize and doubling of the normalized magnitude. -/
def widenMagnitude (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical (resizeMagnitudeOp refs)) (.classical (doubleNumeratorOp refs))

/-- The actual original-denominator resize. -/
def widenDenominator (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  .classical (resizeDenominatorOp refs)

/-- The complete overwrite-safe prefix before the signed rounding correction. -/
def prepare (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  .seq (normalizeMagnitude refs) (.seq (widenMagnitude refs) (widenDenominator refs))

/-- Only the negative stored flag enables the one-unit dividend correction. -/
def correctionChoice (refs : BodyRefs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => .classical (correctNumeratorOp refs)

/-- Real addition, stored-result correction and divisor doubling. -/
def roundingArm (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical (addDenominatorOp refs))
    (.seq (.branch (writeInput refs.negative) (correctionChoice refs))
      (.classical (doubleDenominatorOp refs)))

/-- Execute the actual quotient-and-remainder instruction. -/
def divide (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  .classical (divideOp refs)

/-- Select sign restoration from the actual stored sign of the original numerator. -/
def restoreChoice (refs : BodyRefs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => .seq (.classical (complementOutputOp refs))
      (.classical (incrementOutputOp refs))

/-- Resize the actual quotient and conditionally restore its sign. -/
def finish (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical (resizeQuotientOp refs))
    (.branch (writeInput refs.negative) (restoreChoice refs))

/-- The complete actual signed nearest-division circuit, with no scratch reset prefix. -/
def body (refs : BodyRefs ctx width) : Circuit ctx ctx :=
  .seq (prepare refs) (.seq (roundingArm refs) (.seq (divide refs) (finish refs)))

/-- The three real wider-word writes following the actual normalization prefix. -/
def prepareStep (refs : BodyRefs ctx width) (store : Store ctx) :
    Store ctx × (prepare refs).Path :=
  let normalized := normalizationStep refs.numerator refs.negative refs.magnitude store
  (((normalized.1.applyOp (resizeMagnitudeOp refs)).applyOp
    (doubleNumeratorOp refs)).applyOp (resizeDenominatorOp refs),
      (normalized.2, (((), ()), ())))

/-- Store update and instruction path of the chosen dividend correction. -/
def correctionStep (refs : BodyRefs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (correctionChoice refs flag).Path :=
  match flag with
  | .bit false => (store, ())
  | .bit true => (store.applyOp (correctNumeratorOp refs), ())

/-- Actual chronological stores and selected path in the dividend/divisor preparation. -/
def roundingStep (refs : BodyRefs ctx width) (store : Store ctx) :
    Store ctx × (roundingArm refs).Path :=
  let added := store.applyOp (addDenominatorOp refs)
  let corrected := correctionStep refs (added.read (writeInput refs.negative)) added
  (corrected.1.applyOp (doubleDenominatorOp refs),
    ((), (⟨added.read (writeInput refs.negative), corrected.2⟩, ())))

/-- Actual stores and instruction path of the selected quotient-sign restoration. -/
def restoreStep (refs : BodyRefs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (restoreChoice refs flag).Path :=
  match flag with
  | .bit false => (store, ())
  | .bit true => ((store.applyOp (complementOutputOp refs)).applyOp
      (incrementOutputOp refs), ((), ()))

/-- Actual quotient resize followed by the branch that reads the retained sign. -/
def finishStep (refs : BodyRefs ctx width) (store : Store ctx) :
    Store ctx × (finish refs).Path :=
  let resized := store.applyOp (resizeQuotientOp refs)
  let restored := restoreStep refs (resized.read (writeInput refs.negative)) resized
  (restored.1, ((), ⟨resized.read (writeInput refs.negative), restored.2⟩))

/-- The concrete native store updates and complete path used by the actual division body. -/
def bodyStep (refs : BodyRefs ctx width) (store : Store ctx) : Store ctx × (body refs).Path :=
  let prepared := prepareStep refs store
  let rounded := roundingStep refs prepared.1
  let divided := rounded.1.applyOp (divideOp refs)
  let finished := finishStep refs divided
  (finished.1, (prepared.2, (rounded.2, ((), finished.2))))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
