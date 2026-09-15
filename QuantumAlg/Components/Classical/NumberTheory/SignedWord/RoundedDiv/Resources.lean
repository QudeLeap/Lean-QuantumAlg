/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Native resources and live space of signed nearest division

The independent instruction trace records the chosen magnitude, correction and
sign-restoration arms. The real circuit has at most thirteen native instructions
and visits only the caller's original context, including its quantum systems.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native instruction formula for the three actual stored-sign selections. -/
def bodyTrace (width : Nat) (magnitudeNegative correctionNegative restoreNegative : Bool) :
    List (Resource.Event kind) :=
  signTrace width ++ magnitudeTrace width magnitudeNegative ++
    [.classicalOperation (.wordResize width (width + 1)),
      .classicalOperation (.wordUnary .shiftLeft (width + 1)),
      .classicalOperation (.wordResize width (width + 1)),
      .classicalOperation (.wordBinary .add (width + 1))] ++
    (if correctionNegative then [.classicalOperation (.wordUnary .decrement (width + 1))]
      else []) ++
    [.classicalOperation (.wordUnary .shiftLeft (width + 1)),
      .classicalOperation (.divRem (width + 1) (width + 1)),
      .classicalOperation (.wordResize (width + 1) width)] ++
    (if restoreNegative then [.classicalOperation (.wordUnary .complement width),
      .classicalOperation (.wordUnary .increment width)] else [])

/-- Every actual path charges exactly the instructions selected by its three recorded flags. -/
theorem body_events (refs : BodyRefs ctx width) (path : (body refs).Path) :
    (body refs).eventTrace path = bodyTrace width path.1.1.2.1.toBool
      path.2.1.2.1.1.toBool path.2.2.2.2.1.toBool := by
  rcases path with ⟨⟨normalized, widened⟩, ⟨added, ⟨correctionFlag, correctionPath⟩, doubled⟩,
    divided, resized, restoreFlag, restorePath⟩
  change (SignedWord.normalizeMagnitude refs.numerator refs.negative
    refs.magnitude).Path at normalized
  cases correctionFlag with
  | bit correctionFlag =>
      cases restoreFlag with
      | bit restoreFlag =>
          cases correctionFlag <;> cases restoreFlag <;>
            simp only [body, prepare, widenMagnitude, widenDenominator, roundingArm,
              divide, finish, Circuit.eventTrace, normalizeMagnitude,
              correctionChoice, restoreChoice,
              bodyTrace, Bool.false_eq_true, CShape.Value.toBool, if_false, if_true,
              ClassicalOp.eventTrace, ClassicalOp.event, ClassicalOp.label,
              resizeMagnitudeOp, doubleNumeratorOp, resizeDenominatorOp, addDenominatorOp,
              correctNumeratorOp, doubleDenominatorOp, divideOp, resizeQuotientOp,
              complementOutputOp, incrementOutputOp, List.append_assoc, List.cons_append,
              List.nil_append, List.append_nil]
          all_goals rw [SignedWord.normalizeMagnitude_events]
          all_goals simp only [List.append_assoc, CShape.Value.toBool]

/-- The actual store path uses the original numerator's sign in all three native selections. -/
theorem body_actualEvents (refs : BodyRefs ctx width) (separation : Separation refs)
    (store : Store ctx) (widthPositive : 0 < width) :
    (body refs).eventTrace (bodyStep refs store).2 =
      bodyTrace width (rawIsNegative (store.read refs.numerator))
        (rawIsNegative (store.read refs.numerator))
        (rawIsNegative (store.read refs.numerator)) := by
  let prepared := (prepareStep refs store).1
  let rounded := (roundingStep refs prepared).1
  let divided := rounded.applyOp (divideOp refs)
  have preparedSign : (prepared.read (writeInput refs.negative)).toBool =
      rawIsNegative (store.read refs.numerator) :=
    (prepare_values refs separation store widthPositive).2.2
  have roundingSign : ((prepared.applyOp (addDenominatorOp refs)).read
      (writeInput refs.negative)).toBool = rawIsNegative (store.read refs.numerator) := by
    rw [read_other prepared (addDenominatorOp refs) refs.negative
      (Ne.symm separation.negativeNeWideNumerator)]
    exact preparedSign
  have roundedSign : (rounded.read (writeInput refs.negative)).toBool =
      rawIsNegative (store.read refs.numerator) := by
    rw [rounding_callerFrame refs prepared (writeInput refs.negative)
      (by simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton] using
        Ne.symm separation.negativeNeWideNumerator)
      (by simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton] using
        Ne.symm separation.negativeNeWideDenominator)]
    exact preparedSign
  have finishSign : ((divided.applyOp (resizeQuotientOp refs)).read
      (writeInput refs.negative)).toBool = rawIsNegative (store.read refs.numerator) := by
    rw [read_other divided (resizeQuotientOp refs) refs.negative
      (Ne.symm separation.negativeNeOutput),
      read_other rounded (divideOp refs) refs.negative (Ne.symm separation.negativeNeDivision)]
    exact roundedSign
  rw [body_events]
  change bodyTrace width
    (((signStore refs.numerator refs.negative store).read (writeInput refs.negative)).toBool)
    (((prepared.applyOp (addDenominatorOp refs)).read (writeInput refs.negative)).toBool)
    (((divided.applyOp (resizeQuotientOp refs)).read (writeInput refs.negative)).toBool) = _
  rw [rawWord_classifySign_correct, roundingSign, finishSign]

/-- The actual ordered trace has at most thirteen native instructions on every path. -/
theorem body_eventCount_le (refs : BodyRefs ctx width) (path : (body refs).Path) :
    ((body refs).eventTrace path).length ≤ 13 := by
  rw [body_events]
  simp only [bodyTrace, signTrace, magnitudeTrace, List.length_append,
    List.length_cons, List.length_nil]
  split <;> split <;> split <;>
    simp only [List.length_cons, List.length_nil] <;> decide

/-- Unit native durations preserve every sequential dependency and total at most thirteen. -/
theorem body_depth_le (refs : BodyRefs ctx width) (path : (body refs).Path) :
    (body refs).depth (fun _ => 1) path ≤ 13 := by
  have normalizationBound := SignedWord.normalizeMagnitude_depth_le refs.numerator
    refs.negative refs.magnitude path.1.1
  rcases path with ⟨⟨normalized, widened⟩, ⟨added, ⟨correctionFlag, correctionPath⟩, doubled⟩,
    divided, resized, restoreFlag, restorePath⟩
  change (SignedWord.normalizeMagnitude refs.numerator refs.negative
    refs.magnitude).Path at normalized
  cases correctionFlag with
  | bit correctionFlag =>
      cases restoreFlag with
      | bit restoreFlag =>
          cases correctionFlag <;> cases restoreFlag <;>
            simp only [body, prepare, widenMagnitude, widenDenominator, roundingArm,
              divide, finish, correctionChoice, restoreChoice, normalizeMagnitude, Circuit.depth,
              Circuit.eventDepth, DepthExpr.depthEval] at * <;> omega

/-- Every visited context is the original complete caller context. -/
theorem body_visited (refs : BodyRefs ctx width) (path : (body refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (body refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨⟨normalized, widened⟩, ⟨added, ⟨correctionFlag, correctionPath⟩, doubled⟩,
    divided, resized, restoreFlag, restorePath⟩
  change (SignedWord.normalizeMagnitude refs.numerator refs.negative
    refs.magnitude).Path at normalized
  cases correctionFlag with
  | bit correctionFlag =>
      cases restoreFlag with
      | bit restoreFlag =>
          cases correctionFlag <;> cases restoreFlag <;>
            simp only [body, prepare, widenMagnitude, widenDenominator, roundingArm,
              divide, finish, correctionChoice, restoreChoice, Circuit.visitedContexts,
              normalizeMagnitude] at present <;>
            rw [SignedWord.normalizeMagnitude_visited] at present <;>
            split at present <;>
            simpa only [List.mem_append, List.mem_cons, List.not_mem_nil,
              or_false, or_self] using present

/-- Resident space includes every original classical cell and quantum system. -/
theorem body_resident_le (refs : BodyRefs ctx width) (path : (body refs).Path) :
    (body refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [body_visited refs path visited present]

/-- No auxiliary allocation is added to the caller-supplied scratch and quantum context. -/
theorem body_auxiliary_le (refs : BodyRefs ctx width) (path : (body refs).Path) :
    (body refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [body_visited refs path visited present]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
