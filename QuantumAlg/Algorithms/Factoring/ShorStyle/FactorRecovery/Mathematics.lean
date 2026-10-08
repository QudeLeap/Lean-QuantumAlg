/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Mathematics
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.SamplingInput
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector

/-!
# Source mathematics of canonical Shor factor recovery

The even-modulus shortcut returns two. Otherwise the retained sampler's
nontrivial factor has priority, followed by the accepted even order and the
left-then-right half-order GCD reduction. Natural powers and their canonical
modular residues select exactly the same factor. The source-good sample and
Born outcome retain their common unit in the intrinsic recovery input.
These are mathematical selectors and correctness facts; actual classical
execution must derive their values from its real stored parameter and phase.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery

noncomputable section

/-- A good unit's true order makes the pure left gcd branch return a declared
semiprime factor. -/
theorem factorFromOrderValue_returns_declared_of_goodBase {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (odd : ¬ Even N) (unit : (ZMod N)ˣ)
    (good :
      NumberTheory.Factoring.RandomBaseUnitSample.GoodEvent
        (NumberTheory.Factoring.RandomBaseUnitSample.ofUnit
          (model := model) unit)) :
    ∃ factor,
      factorFromOrderValue N (Probability.sampledBase unit) (orderOf unit) =
          some factor ∧
        (factor = model.leftFactor ∨ factor = model.rightFactor) := by
  let sample :=
    NumberTheory.Factoring.RandomBaseUnitSample.ofUnit (model := model) unit
  obtain ⟨leftGt, rightGt⟩ := model.factors_gt_two_of_not_even odd
  have halfOrder :
      NumberTheory.Factoring.HalfOrderGcdInput N
        (Probability.sampledBase unit) (orderOf unit) := by
    simpa [sample, Probability.sampledBase,
      NumberTheory.Factoring.RandomBaseUnitSample.baseResidue] using
      sample.halfOrderGcdInput_of_goodBase rfl leftGt rightGt good
  have bridge := NumberTheory.Factoring.gcd_bridge_of_half_order halfOrder
  let factor := Nat.gcd
    (Probability.sampledBase unit ^ (orderOf unit / 2) - 1) N
  have result :
      factorFromOrderValue N (Probability.sampledBase unit) (orderOf unit) =
        some factor := by
    simp [factorFromOrderValue, factorFromHalfPowerValue, odd, halfOrder.order_pos,
      halfOrder.even_order, bridge.1.1, bridge.1.2, factor]
  have declared : factor = model.leftFactor ∨ factor = model.rightFactor :=
    model.nontrivial_factor_eq_declared
      (Nat.gcd_dvd_right
        (Probability.sampledBase unit ^ (orderOf unit / 2) - 1) N)
      bridge.1.1 bridge.1.2
  exact ⟨factor, result, declared⟩

/-- For an even semiprime, the public shortcut factor is one of the declared
prime factors.  This is intentionally local to the typed canonical boundary
and is proved from the semiprime model itself. -/
theorem two_eq_declaredFactor_of_even {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (even : Even N) :
    2 = model.leftFactor ∨ 2 = model.rightFactor :=
  model.nontrivial_factor_eq_declared (even_iff_two_dvd.mp even)
    (by norm_num) model.modulus_gt_two

/-- The machine-facing pure output has the same total even-modulus shortcut:
the sampled parameter and terminal recovery latch are irrelevant once the
public modulus itself exposes factor two. -/
theorem outputOf_eq_some_two_of_even {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (even : Even N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (orderAccepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1)) :
    outputOf parameter orderAccepted order = some 2 := by
  simp [outputOf, model.modulus_gt_two, even]

/-- On an even semiprime every pure machine-facing attempt returns the
declared factor two, independently of its sampled parameter and terminal
measurement. -/
theorem outputOf_even_declared {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (even : Even N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (orderAccepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1)) :
    ∃ factor, outputOf parameter orderAccepted order = some factor ∧
      (factor = model.leftFactor ∨ factor = model.rightFactor) :=
  ⟨2, outputOf_eq_some_two_of_even model even parameter orderAccepted order,
    two_eq_declaredFactor_of_even model even⟩

/-- The true unit order fits the recovery candidate word used by the machine. -/
@[nolint unusedArguments]
noncomputable def trueOrderWord {N : Nat} (_input : Input N) (unit : (ZMod N)ˣ) :
    ClassicalAlgorithms.Word (phaseBits N + 1) :=
  ClassicalAlgorithms.OrderRecovery.candidateWord
    (phaseBits N) (orderOf unit)

private theorem trueOrderWord_fits {N : Nat} (input : Input N) (unit : (ZMod N)ˣ) :
    orderOf unit < 2 ^ (phaseBits N + 1) := by
  have orderLt : orderOf unit < N :=
    OrderFinding.input_order_lt_modulus
      (Probability.sampledOrderInput input unit)
  calc
    orderOf unit < N := orderLt
    _ ≤ N ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right N input.modulus_pos
    _ ≤ 2 ^ phaseBits N := input.registerSquare_fits
    _ < 2 ^ (phaseBits N + 1) := by
      exact Nat.pow_lt_pow_right (by decide)
        (Nat.lt_succ_self (phaseBits N))

@[simp] theorem trueOrderWord_val {N : Nat} (input : Input N)
    (unit : (ZMod N)ˣ) : (trueOrderWord input unit).val = orderOf unit := by
  unfold trueOrderWord
  exact ClassicalAlgorithms.OrderRecovery.candidateWord_val_of_lt
    (trueOrderWord_fits input unit)

/-- On an odd semiprime, a counted good unit and its accepted true order make
the machine-facing pure relation return a declared factor. -/
theorem outputOf_unitParameter_trueOrder_declared {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (odd : ¬ Even N) (unit : (ZMod N)ˣ)
    (good :
      NumberTheory.Factoring.RandomBaseUnitSample.GoodEvent
        (NumberTheory.Factoring.RandomBaseUnitSample.ofUnit
          (model := model) unit)) :
    ∃ factor,
      outputOf
          (Probability.unitParameter (Probability.Input.ofSemiprimeModel model) unit)
          true (trueOrderWord (Probability.Input.ofSemiprimeModel model) unit) =
        some factor ∧
      (factor = model.leftFactor ∨ factor = model.rightFactor) := by
  obtain ⟨factor, result, declared⟩ :=
    factorFromOrderValue_returns_declared_of_goodBase model odd unit good
  refine ⟨factor, ?_, declared⟩
  unfold outputOf
  rw [if_neg]
  · simp only [Probability.unitParameter, Probability.sampledBaseIndex,
      Probability.sampledBase, CShape.Value.first, CShape.Value.second,
      CShape.Value.toBool, CShape.Value.toNat, Bool.false_eq_true,
      if_false, if_true, trueOrderWord_val]
    exact result
  · rintro ⟨_modulusGtTwo, modulusEven⟩
    exact odd modulusEven

/-- Any encoded success from the ordinary half-order route is sound. -/
theorem outputOf_some_sound_of_noEarly {N : Nat} (_input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (noEarly : parameter.second.first.toBool = false)
    (orderAccepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1))
    {factor : Nat} (result :
      outputOf parameter orderAccepted order = some factor) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  unfold outputOf at result
  split at result
  next evenModulus =>
    injection result with factorEq
    subst factor
    exact ⟨even_iff_two_dvd.mp evenModulus.2, by norm_num, evenModulus.1⟩
  next _notEvenModulus =>
    rw [noEarly] at result
    simp only [Bool.false_eq_true, if_false] at result
    split at result
    next => exact factorFromOrderValue_some_sound result
    next => simp at result

/-- Every successful output computed from the actual sampler parameter is a
nontrivial factor of the public modulus. -/
theorem outputOf_parameterValue_some_sound {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (orderAccepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1))
    {factor : Nat}
    (result : outputOf (parameterValue input sample) orderAccepted order =
      some factor) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  let prepared := RSA.prepareResidueFromBits N (modulusBits N)
    residueProposalCount sample
  cases earlyEq : prepared.earlyFactor with
  | none =>
      have noEarly :
          (parameterValue input sample).second.first.toBool = false :=
        parameterValue_earlyFactor_none input sample earlyEq
      exact outputOf_some_sound_of_noEarly input (parameterValue input sample)
        noEarly orderAccepted order result
  | some early =>
      have earlyValue :=
        parameterValue_earlyFactor_some input sample earlyEq
      unfold outputOf at result
      split at result
      next evenModulus =>
        injection result with factorEq
        subst factor
        exact ⟨even_iff_two_dvd.mp evenModulus.2, by norm_num,
          evenModulus.1⟩
      next _notEvenModulus =>
        rw [earlyValue.1] at result
        simp only [if_true] at result
        rw [earlyValue.2] at result
        injection result with factorEq
        subst factor
        exact prepared.earlyFactor_sound early earlyEq

/-- The optional order value supplied by the seam preserves the ordinary
sampler-parameter soundness guarantee on every successful factor result. -/
theorem outputOfRecovered_parameterValue_some_sound {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (recovered :
      ClassicalAlgorithms.OrderRecovery.Output (modulusBits N) (phaseBits N))
    {factor : Nat}
    (result : outputOfRecovered (parameterValue input sample) recovered =
      some factor) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  cases recovered with
  | none =>
      exact outputOf_parameterValue_some_sound input sample false
        (ClassicalAlgorithms.OrderRecovery.candidateWord
          (phaseBits N) 0) result
  | some order =>
      exact outputOf_parameterValue_some_sound input sample true order result

/-- The even-modulus shortcut remains total after the optional order
result is exposed: no sampler or terminal value can bypass factor two. -/
theorem outputOfRecovered_eq_some_two_of_even {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (even : Even N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (recovered :
      ClassicalAlgorithms.OrderRecovery.Output (modulusBits N) (phaseBits N)) :
    outputOfRecovered parameter recovered = some 2 := by
  cases recovered with
  | none =>
      exact outputOf_eq_some_two_of_even model even parameter false
        (ClassicalAlgorithms.OrderRecovery.candidateWord
          (phaseBits N) 0)
  | some order =>
      exact outputOf_eq_some_two_of_even model even parameter true order

/-- A source-good sampled outcome fixes a concrete semantic recovery
input.  The definition names the actual sampled unit and terminal
measurement together, so later endpoint projections cannot mix them. -/
def goodAttemptSemanticInput {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (unit : (ZMod N)ˣ)
    (outcome : SourceOutcome N) :=
  OrderFinding.ShorSourceJoint.semanticInput
    (Probability.sampledOrderInput (Probability.Input.ofSemiprimeModel model) unit)
    (Probability.sampledOracleAccess (Probability.Input.ofSemiprimeModel model) unit)
    outcome.measurement

/-- One fixed source-good unit and its actual terminal outcome make the pure
recovery result select a declared semiprime factor.  Even moduli use their
total factor-two route; the odd case invokes the source-certified
continued-fraction recovery bridge and then the ordinary half-order gcd
theorem. -/
theorem outputOfRecovered_unitOutcome_declared {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (outcome : SourceOutcome N) (unit : (ZMod N)ˣ)
    (unitMember : unit ∈ model.goodEventUnits)
    (parameterEq : parameterValue (Probability.Input.ofSemiprimeModel model) outcome.sample =
      Probability.unitParameter (Probability.Input.ofSemiprimeModel model) unit)
    (recoverable : OrderFinding.ShorSourceJoint.NativeRecoverableOutcome unit (orderOf unit)
      outcome.measurement) :
    ∃ factor,
      outputOfRecovered
          (parameterValue (Probability.Input.ofSemiprimeModel model) outcome.sample)
          (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
            (OrderFinding.ShorSourceJoint.recoverySpec
                (Probability.sampledOrderInput (Probability.Input.ofSemiprimeModel model)
                  unit)
                (Probability.sampledOracleAccess (Probability.Input.ofSemiprimeModel model)
                  unit))
            (goodAttemptSemanticInput model unit outcome)) = some factor ∧
        (factor = model.leftFactor ∨ factor = model.rightFactor) := by
  by_cases even : Even N
  · exact ⟨2,
      outputOfRecovered_eq_some_two_of_even model even
        (parameterValue (Probability.Input.ofSemiprimeModel model) outcome.sample) _,
      two_eq_declaredFactor_of_even model even⟩
  · have unitGood :
      NumberTheory.Factoring.RandomBaseUnitSample.GoodEvent
        (NumberTheory.Factoring.RandomBaseUnitSample.ofUnit (model := model) unit) := by
      simpa [NumberTheory.Factoring.SemiprimeFactorModel.goodEventUnits] using unitMember
    have candidateFits : orderOf unit < 2 ^ (phaseBits N + 1) :=
      OrderFinding.ShorSourceJoint.order_fits_candidateWord
        (Probability.sampledOrderInput (Probability.Input.ofSemiprimeModel model) unit)
        (Probability.Input.ofSemiprimeModel model).registerSquare_fits
    have canonicalRecoverable :
        OrderFinding.ShorSourceJoint.NativeRecoverableOutcome
          (ZMod.unitOfCoprime (Probability.sampledBase unit)
            (Probability.sampledOrderInput
              (Probability.Input.ofSemiprimeModel model) unit).coprime)
          (orderOf unit) outcome.measurement := by
      rw [Probability.unitOfCoprime_sampledBase_eq
        (Probability.Input.ofSemiprimeModel model) unit]
      exact recoverable
    have recoveredOrder :=
      OrderFinding.ShorSourceJoint.recoverUnitOrder_eq_some_of_recoverableOutcome
        (Probability.sampledOrderInput (Probability.Input.ofSemiprimeModel model) unit)
        (Probability.sampledOracleAccess (Probability.Input.ofSemiprimeModel model) unit)
        candidateFits canonicalRecoverable
    obtain ⟨factor, ordinaryResult, declared⟩ :=
      outputOf_unitParameter_trueOrder_declared model even unit unitGood
    refine ⟨factor, ?_, declared⟩
    have semanticInput_eq :
        goodAttemptSemanticInput model unit outcome =
          OrderFinding.ShorSourceJoint.semanticInput
            (Probability.sampledOrderInput
              (Probability.Input.ofSemiprimeModel model) unit)
            (Probability.sampledOracleAccess
              (Probability.Input.ofSemiprimeModel model) unit)
            outcome.measurement := rfl
    rw [parameterEq, semanticInput_eq, recoveredOrder]
    simpa only [outputOfRecovered, trueOrderWord]
      using ordinaryResult

/-- A counted source-good outcome supplies a concrete unit witness for the
previous recovery theorem. -/
theorem outputOfRecovered_goodAttemptOutcome_declared {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (outcome : SourceOutcome N)
    (good : Probability.GoodAttemptOutcome model outcome) :
    ∃ unit factor,
      unit ∈ model.goodEventUnits ∧
        parameterValue (Probability.Input.ofSemiprimeModel model) outcome.sample =
          Probability.unitParameter (Probability.Input.ofSemiprimeModel model) unit ∧
        outputOfRecovered
            (parameterValue (Probability.Input.ofSemiprimeModel model) outcome.sample)
            (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
              (OrderFinding.ShorSourceJoint.recoverySpec
                  (Probability.sampledOrderInput (Probability.Input.ofSemiprimeModel model)
                    unit)
                  (Probability.sampledOracleAccess (Probability.Input.ofSemiprimeModel model)
                    unit))
              (goodAttemptSemanticInput model unit outcome)) = some factor ∧
          (factor = model.leftFactor ∨ factor = model.rightFactor) := by
  rcases good with ⟨unit, unitMember, parameterEq, recoverable⟩
  obtain ⟨factor, result, declared⟩ :=
    outputOfRecovered_unitOutcome_declared model outcome unit unitMember
      parameterEq recoverable
  exact ⟨unit, factor, unitMember, parameterEq, result, declared⟩

/-! ## Source recovery input -/


end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery
