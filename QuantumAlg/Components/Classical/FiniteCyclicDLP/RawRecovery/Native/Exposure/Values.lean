/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection.Original

/-!
# Original three-cell recovery values

The original checked decision exposes the successful candidate and independent
reconstruction flag. On failure, the payload remains the actual initial value
of its fresh cell. These three values are exactly the original public
`outputCells` observation, including its zero candidate and false flags on failure.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open ClassicalAlgorithms.Modular NormalizedRecovery.Native

noncomputable section

variable {width : Nat}

/-- The original checked decision and selected payload give all three original public values. -/
lemma exposedRecoveryValue_original (spec : ModulusSpec width)
    (original : CShape.Value (InputShape width)) (success : CShape.Value .bit)
    (left right inverse : CShape.Word width) (modulus : CShape.Word (width + 1))
    (modulusValue : modulus.toNat = spec.modulus)
    (leftValue : left.toNat = (normalize spec original).left.val)
    (rightValue : right.toNat = (negateRight spec (normalize spec original)).val)
    (statusValue : success = .bit (NumberTheory.Checked.Engine.unitDecision spec
      (normalize spec original).left))
    (inverseValue : NumberTheory.Checked.Engine.unitDecision spec
        (normalize spec original).left = true → inverse.toNat =
          (NumberTheory.Checked.Engine.inverseCoefficient spec
            (normalize spec original).left).val) :
    .product success (if success.toBool then recoveryValue left right inverse modulus
      else CShape.initialValue (FiniteCyclicDLP.OutputShape width)) =
        RawRecovery.outputCells spec original := by
  have encoded := selectedRecoveryValue_original spec original success left right inverse modulus
    modulusValue leftValue rightValue statusValue inverseValue
  cases success with
  | bit selected =>
    cases selected with
    | false =>
      cases outcome : RawRecovery.outputOf spec original with
      | none =>
        rw [RawRecovery.outputCells_of_outputOf_none spec original outcome]
        rfl
      | some output =>
        simp only [CShape.Value.toBool, Bool.false_eq_true, if_false, outcome,
          encodedRawOutput] at encoded
        cases encoded
    | true =>
      cases outcome : RawRecovery.outputOf spec original with
      | none =>
        simp only [CShape.Value.toBool, if_true, outcome, encodedRawOutput] at encoded
        cases encoded
      | some output =>
        have same : recoveryValue left right inverse modulus =
            encodedRecoveryOutput spec output := by
          simpa only [CShape.Value.toBool, if_true, outcome, encodedRawOutput,
            CShape.Value.optionSome.injEq] using encoded
        rw [RawRecovery.outputCells_of_outputOf_some spec original output outcome]
        exact congrArg
          (fun payload : CShape.Value (FiniteCyclicDLP.OutputShape width) =>
            CShape.Value.product (.bit true) payload) same

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
