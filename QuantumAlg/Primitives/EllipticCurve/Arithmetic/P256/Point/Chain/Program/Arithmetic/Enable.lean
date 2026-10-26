/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Operator

/-!
# The actual enable operators on an abstract complete original label

Proving these two native equations before specializing the label prevents
later composition proofs from expanding a complete resident initializer
or measured output merely to apply the same arbitrary-input enable law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

/-- Keep the placed basis vector abstract in later concrete field-coordinate compositions. -/
lemma referenceKet_eq (state : Window.Raw) {Reference : Register} (reference : Reference.Index) :
    parameters.referenceKet state reference =
      (NormalizedVector.ket (R := ctx.register.prod Reference)
        (measuredEncodedBasis (QubitLayout.canonical Window.encoding.width)
          parameters.sameWires state, reference)).vec := rfl

/-- Abstract factor composition avoids normalizing complete resident basis labels. -/
lemma measuredFactors_applyVec {R : Register} (before middle after : HilbertOperator R)
    (initial prepared measured final : HilbertVector R) (coefficient : ℂ)
    (first : before.applyVec initial = prepared)
    (second : middle.applyVec prepared = coefficient • measured)
    (third : after.applyVec measured = final) :
    HilbertOperator.applyVec (after * (middle * before)) initial = coefficient • final := by
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, first, second,
    HilbertOperator.applyVec_smul, third]

/-- The same abstract two-factor law applies to an actual call and its subsequent native clear. -/
lemma measuredClear_applyVec {R : Register} (middle after : HilbertOperator R)
    (initial measured final : HilbertVector R) (coefficient : ℂ)
    (second : middle.applyVec initial = coefficient • measured)
    (third : after.applyVec measured = final) :
    HilbertOperator.applyVec (after * middle) initial = coefficient • final := by
  rw [HilbertOperator.mul_applyVec, second, HilbertOperator.applyVec_smul, third]

/-- Convert an already established actual basis action before specializing its complete labels. -/
lemma referenceKet_action {Reference : Register}
    (operator : HilbertOperator (ctx.register.prod Reference))
    (initial final : Window.Raw) (reference : Reference.Index) (coefficient : ℂ)
    (actual : operator.applyVec
      (NormalizedVector.ket (R := ctx.register.prod Reference)
        (measuredEncodedBasis (QubitLayout.canonical Window.encoding.width)
          parameters.sameWires initial, reference)).vec =
      coefficient • (NormalizedVector.ket (R := ctx.register.prod Reference)
        (measuredEncodedBasis (QubitLayout.canonical Window.encoding.width)
          parameters.sameWires final, reference)).vec) :
    operator.applyVec (parameters.referenceKet initial reference) =
      coefficient • parameters.referenceKet final reference := actual

/-- The original paid enable changes only its original output on the same full physical bank. -/
lemma enableOperator_original (environment : OracleModel.empty.Interpretation)
    (state : Window.Raw) {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator
      (Window.Enable.program parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference).applyVec (parameters.referenceKet state reference) =
      parameters.referenceKet (Window.Enable.step parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound state)
        reference :=
  parameters.nativeOperator_original _ environment state _
    (Window.Enable.program_ket parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment state)
    reference

/-- The actual inverse enable has the same exact all-label action beside the original reference. -/
lemma clearEnableOperator_original (environment : OracleModel.empty.Interpretation)
    (state : Window.Raw) {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator
      (Window.Enable.inverseProgram parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference).applyVec (parameters.referenceKet state reference) =
      parameters.referenceKet (Window.Enable.step parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound state)
        reference :=
  parameters.nativeOperator_original _ environment state _
    (Window.Enable.inverseProgram_ket parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment state)
    reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
