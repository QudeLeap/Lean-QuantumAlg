/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Success
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete actual logical resources for original elliptic-curve discrete logarithms

One actual circuit supplies the returned scalar, every probability, all
native events, live spaces and depth. The original exceptional error remains
in its finite repetition condition. The hidden scalar is selected only inside
the proof; neither it nor an external reference is an executable parameter.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured
open FiniteCyclicDLP.Canonical.Probability

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem output_probability_le_relational {kind : ProblemKind}
    {pre post : RuntimeCtx kind} {shape : CShape} (run : AlgorithmRun pre post shape)
    {Reference : Register} (supplied : Input pre Reference) (value : shape.Value)
    (accepts : Store pre → shape.Value → Prop) (accepted : ∀ store, accepts store value) :
    run.outputDistribution supplied value ≤
      (run.relationalDistribution supplied).toOuterMeasure {pair | accepts pair.1 pair.2} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  apply (run.executionDistribution supplied).toOuterMeasure_mono
  intro record member
  have same : run.result record = value := member.1
  change accepts record.2.1 (run.result record)
  rw [same]
  exact accepted record.2.1

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The algorithm contains exactly the original actual repeated measured execution. -/
public def algorithm (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (count : Nat) :
    Algorithm .quantum (inputContext E I) (outputContext E I)
      (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))) where
  run := exponentRepeatedRun E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I)
    points seed I.subgroupOrder_prime.two_le count

/-- The same actual run solves the original problem under its complete error/retry condition. -/
public theorem main (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure) :
    (algorithm E fieldTail sameWidth fits odd I points seed count).Solves
      (problem E fieldTail sameWidth fits I seed count failure) where
  success := by
    intro Reference supplied valid
    let original := PublicInput.unframedInput E (orderWidth (ECDLP.Canonical.problem I)) supplied
    let witness : SecretInput (ECDLP.Canonical.problem I) :=
      ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I⟩
    have same := PublicInput.initialInput_unframedInput E
      (orderWidth (ECDLP.Canonical.problem I)) (ECDLP.Canonical.problem I) supplied valid
    have correct := exponentRepeatedRun_secret_probability_ge E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) I.subgroupOrder_prime.two_le points seed addends count witness
      original
    rw [same] at correct
    refine ((tsub_le_tsub_left (ENNReal.ofReal_le_ofReal calibrated) 1).trans correct).trans ?_
    exact output_probability_le_relational _ supplied _ _ (fun _store =>
      ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I, rfl⟩)
  states := by
    intro Reference supplied valid requirement member
    cases member
  borrowed := by
    intro Reference supplied valid
    exact Circuit.borrowedRestored_of_noBorrowedQuantum _
      (PublicInput.before_noBorrowedQuantum E (orderWidth (ECDLP.Canonical.problem I)))
      Reference (supplied.state.mapClassical (fun store => (store, store)))
  events := by
    intro Reference supplied valid path supported
    exact exponentRepeatedRun_pool_le E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I)
      points seed I.subgroupOrder_prime.two_le count path
  resident := by
    intro Reference supplied valid path supported
    exact exponentRepeatedRun_resident_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path
  auxiliary := by
    intro Reference supplied valid path supported
    exact exponentRepeatedRun_auxiliary_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path
  depth := by
    intro Reference supplied valid path supported
    exact exponentRepeatedRun_unitDepth_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path

end

end QuantumAlg.EllipticCurve.LogicalResources
