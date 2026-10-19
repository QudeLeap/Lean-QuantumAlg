/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Probability.Finite
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Offset

/-!
# Original fixed-offset success on the actual streaming recovery execution

The original canonical secret is a proof witness, not an executable input.
The same allocated streaming run satisfies the original accepted-output event
on every complete input in the original two-point local domain, expressed in
the new physical public frame. Its allocation remains inside its actual code.

Finite averaging chooses one public nonidentity subgroup seed before every
retry count, input state and external Reference. Monotonicity transfers the
complete exceptional error to the original averaged failure coefficient. No
caller cleanliness, point interpretation, positive floor or independent
sampling premise is introduced. The old and new physical contexts are not
identified. Resource conjunction is a separate same-run obligation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.FixedOffsetSuccess

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace
open FiniteCyclicDLP Canonical.Probability ECDLP.Measured

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

private lemma output_probability_le_relational {model : ExecutionModel}
    {environment : model.Environment}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (actual : AlgorithmRun model pre post shape) {Reference : Register}
    (supplied : OracleInput model.classicalOracles pre Reference) (value : shape.Value)
    (accepts : Store pre → shape.Value → Prop) (accepted : ∀ stored, accepts stored value) :
    actual.outputDistribution environment supplied value ≤
      (actual.relationalDistribution environment supplied).toOuterMeasure {pair | accepts pair.1
        pair.2} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  apply (actual.executionDistribution environment supplied).toOuterMeasure_mono
  intro record member
  have same : actual.result record = value := Set.mem_singleton_iff.mp member.1
  change accepts record.2.2.1 (actual.result record)
  rw [same]
  exact accepted record.2.2.1

/-- Original calibration bounds the same run's actual canonical-secret output probability. -/
lemma actual_run_output_probability_ge
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : LogicalResources.AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : LogicalResources.RepetitionCondition E I points seed count failure)
    {Reference : Register}
    (supplied : OracleInput .empty
      (Recovery.PublicInput.frame E (orderWidth (ECDLP.Canonical.problem I))) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth (ECDLP.Canonical.problem I))
      (ECDLP.Canonical.problem I) supplied.caller.localState) :
    1 - ENNReal.ofReal failure ≤
      (run E fieldTail (ECDLP.Canonical.problem I) points seed I.subgroupOrder
        (Semantics.radixUnit p fieldTail.succ odd)
        I.subgroupOrder_prime.two_le count).outputDistribution environment supplied
            (.optionSome (CShape.wordOfNat (orderWidth (ECDLP.Canonical.problem I))
              (ECDLP.Canonical.secret I).val)) := by
  let witness : SecretInput (ECDLP.Canonical.problem I) :=
    ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I⟩
  have actual := FiniteSuccess.actual_run_secret_probability_ge_on_domain (environment :=
    environment) E fieldTail odd
    (ECDLP.Canonical.problem I) points seed sameWidth fits I.subgroupOrder_prime.two_le
    addends count witness supplied valid
  exact (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal calibrated) 1).trans actual

/-- The original accepted event keeps the actual initial Store and output jointly observed. -/
lemma actual_run_relational_success
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : LogicalResources.AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : LogicalResources.RepetitionCondition E I points seed count failure)
    {Reference : Register}
    (supplied : OracleInput .empty
      (Recovery.PublicInput.frame E (orderWidth (ECDLP.Canonical.problem I))) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth (ECDLP.Canonical.problem I))
      (ECDLP.Canonical.problem I) supplied.caller.localState) :
    (LogicalResources.successLowerBound failure).value ≤
      ((run E fieldTail (ECDLP.Canonical.problem I) points seed I.subgroupOrder
        (Semantics.radixUnit p fieldTail.succ odd)
        I.subgroupOrder_prime.two_le count).relationalDistribution environment
          supplied).toOuterMeasure
            {pair | LogicalResources.AcceptedOutput E I pair.2} := by
  have output := actual_run_output_probability_ge (environment := environment) E fieldTail
    sameWidth fits odd I points seed
    addends count failure calibrated supplied valid
  have relational := output_probability_le_relational (environment := environment)
    (run E fieldTail (ECDLP.Canonical.problem I) points seed I.subgroupOrder
      (Semantics.radixUnit p fieldTail.succ odd) I.subgroupOrder_prime.two_le count)
    supplied (.optionSome (CShape.wordOfNat (orderWidth (ECDLP.Canonical.problem I))
      (ECDLP.Canonical.secret I).val))
    (fun _stored output => LogicalResources.AcceptedOutput E I output)
    (fun _stored => ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I, rfl⟩)
  exact output.trans relational

/-- The original two-exceptions-per-step average supplies this independent coefficient. -/
def averageFailureRatio (I : ECDLPInstance E) : ℝ :=
  let problem := ECDLP.Canonical.problem I
  1 - ((problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
        ((problem.order - 1 : Nat) : ℝ)))

/-- One public seed is chosen before the retry budget, input and Reference extension. -/
def fixedOffset (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E) : AffinePoint E :=
  Classical.choose (exists_fixedOffset_exceptionalMass_bound (ECDLP.Canonical.problem I)
    I.subgroupOrder_prime.two_le points)

omit [Fact p.Prime] in
/-- The selected seed remains an original nonidentity point in the public cyclic subgroup. -/
lemma fixedOffset_original_subgroup (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E) :
    (fixedOffset E I points).toGroupPoint ∈
        Subgroup.zpowers (ECDLP.Canonical.problem I).generator ∧
      (fixedOffset E I points).toGroupPoint ≠ 1 := by
  have selected := Classical.choose_spec
    (exists_fixedOffset_exceptionalMass_bound (ECDLP.Canonical.problem I)
      I.subgroupOrder_prime.two_le points)
  exact ⟨selected.1, selected.2.1⟩

omit [Fact p.Prime] in
/-- The fixed seed's actual prepared exceptional mass has the original averaging constant. -/
lemma fixedOffset_exceptionalMass_le (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E) :
    preparedExceptionalMass (ECDLP.Canonical.problem I) points (fixedOffset E I points) ≤
      (2 * (2 * orderWidth (ECDLP.Canonical.problem I)) : Nat) /
        (((ECDLP.Canonical.problem I).order - 1 : Nat) : ℝ) :=
  (Classical.choose_spec (exists_fixedOffset_exceptionalMass_bound (ECDLP.Canonical.problem I)
    I.subgroupOrder_prime.two_le points)).2.2

omit [Fact p.Prime] in
/-- Monotonicity retains the full four-square-root error and every finite retry count. -/
lemma fixedOffset_failurePower_le (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (count : Nat) :
    LogicalResources.RepetitionCondition E I points (fixedOffset E I points) count
      (averageFailureRatio E I ^ count) := by
  let problem := ECDLP.Canonical.problem I
  have errorBound :
      4 * Real.sqrt (preparedExceptionalMass problem points (fixedOffset E I points)) ≤
        4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
          ((problem.order - 1 : Nat) : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (fixedOffset_exceptionalMass_le E I points))
      (by norm_num)
  have ratioBound :
      FiniteSuccess.failureRatio E problem points (fixedOffset E I points) ≤
        averageFailureRatio E I :=
    sub_le_sub_left (sub_le_sub_left errorBound _) _
  exact pow_le_pow_left₀
    (samplingFailureRatio_nonneg problem points (fixedOffset E I points)) ratioBound count

/-- The single selected public seed gives the original averaged floor on the actual run. -/
lemma actual_fixedOffset_relational_success
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (addends : LogicalResources.AddendEncoding E I points) (count : Nat)
    {Reference : Register}
    (supplied : OracleInput .empty
      (Recovery.PublicInput.frame E (orderWidth (ECDLP.Canonical.problem I))) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth (ECDLP.Canonical.problem I))
      (ECDLP.Canonical.problem I) supplied.caller.localState) :
    (LogicalResources.successLowerBound (averageFailureRatio E I ^ count)).value ≤
      ((run E fieldTail (ECDLP.Canonical.problem I) points (fixedOffset E I points)
        I.subgroupOrder (Semantics.radixUnit p fieldTail.succ odd)
          I.subgroupOrder_prime.two_le count).relationalDistribution environment
            supplied).toOuterMeasure
            {pair | LogicalResources.AcceptedOutput E I pair.2} :=
  actual_run_relational_success E fieldTail sameWidth fits odd I points (fixedOffset E I points)
    addends count (averageFailureRatio E I ^ count)
    (fixedOffset_failurePower_le E I points count) supplied valid

/-- The same seed works simultaneously for every retry budget and admitted Reference input. -/
lemma exists_fixedOffset_actual_run_success
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (addends : LogicalResources.AddendEncoding E I points) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers (ECDLP.Canonical.problem I).generator ∧
      seed.toGroupPoint ≠ 1 ∧
      ∀ (count : Nat) (Reference : Register)
        (supplied : OracleInput .empty
          (Recovery.PublicInput.frame E (orderWidth (ECDLP.Canonical.problem I))) Reference),
        Recovery.PublicInput.Support.inputDomain E (orderWidth (ECDLP.Canonical.problem I))
          (ECDLP.Canonical.problem I) supplied.caller.localState →
        (LogicalResources.successLowerBound (averageFailureRatio E I ^ count)).value ≤
          ((run E fieldTail (ECDLP.Canonical.problem I) points seed I.subgroupOrder
            (Semantics.radixUnit p fieldTail.succ odd)
            I.subgroupOrder_prime.two_le count).relationalDistribution environment
              supplied).toOuterMeasure
                {pair | LogicalResources.AcceptedOutput E I pair.2} := by
  refine ⟨fixedOffset E I points, (fixedOffset_original_subgroup E I points).1,
    (fixedOffset_original_subgroup E I points).2, ?_⟩
  intro count Reference supplied valid
  exact actual_fixedOffset_relational_success E fieldTail sameWidth fits odd I points addends
    count supplied valid

end

end ExecutionContract.FixedOffsetSuccess
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
