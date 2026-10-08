/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Zero

/-!
# All-count algorithm endpoint for independently completed EH batches

Zero requested batches execute the original empty-result classical branch.
Every positive count executes the independently packed and physically reset
batch schedule. Both branches retain the original all-input source acceptance
and complete state/resource contracts on their actual code.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The all-count candidate uses the actual zero branch and the new completed
schedule for every positive count. -/
public def completedAlgorithm (input : Input N) : (count : Nat) →
    Algorithm (model input) base (context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => zeroAlgorithm base input
  | laterCount + 1 => completedFiniteAlgorithm base noQuantum input laterCount

/-- Zero requested batches emit no native event on any actual execution path. -/
public theorem completedAlgorithm_zero_resourcePool (input : Input N)
    (path : (completedAlgorithm base noQuantum input 0).run.code.Path) :
    (completedAlgorithm base noQuantum input 0).run.code.resourcePool path = 0 := by rfl

/-- The independent source problem charges the actual code selected by the
requested count, including the zero branch's allocation and no quantum event. -/
public def completedAllProblem (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (count : Nat) → Problem (model input) base (context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => AllKeys.problem base noQuantum input 0 duration unitQueries
  | laterCount + 1 =>
      completedProblem base noQuantum input laterCount duration unitQueries

/-- The completed execution directly realizes the independent source law,
including its classical empty branch. -/
public theorem completedAlgorithm_sourceDistribution (input : Input N) (count : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    (completedAlgorithm base noQuantum input count).run.outputDistribution original =
      AllKeys.sourceDistribution input count := by
  cases count with
  | zero =>
      exact zeroAlgorithm_sourceDistribution base input original
  | succ laterCount =>
      exact Cleanup.completed_outputDistribution base noQuantum N input laterCount original

/-- Every supported completed result is a nontrivial factor of the input modulus. -/
theorem completedAlgorithm_some_sound (input : Input N) (count : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((completedAlgorithm base noQuantum input count).run.outputDistribution original).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [completedAlgorithm_sourceDistribution] at supported
  exact AllKeys.sourceDistribution_some_sound input count word supported

/-- The actual completed factor output has the exact finite populated mass. -/
theorem completedAlgorithm_populatedProbability (input : Input N) (count : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    ((completedAlgorithm base noQuantum input count).run.outputDistribution original).toOuterMeasure
      {output | output ≠ CShape.Value.optionNone} = 1 - AllKeys.sourceFailure input ^ count := by
  rw [completedAlgorithm_sourceDistribution]
  exact AllKeys.sourceDistribution_populated input count

/-- The original good-key floor bounds the failure of this same completed execution. -/
theorem completedAlgorithm_successProbability_ge (good : GoodKeyModel N) (count : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model good.input).classicalOracles base Reference) :
    1 - (1 - NativeBatchSuccess.successFloor good.bitWidth) ^ count ≤
      ((completedAlgorithm base noQuantum good.input count).run.outputDistribution
        original).toOuterMeasure {output | output ≠ CShape.Value.optionNone} := by
  rw [completedAlgorithm_populatedProbability]
  exact tsub_le_tsub_left (pow_le_pow_left' (NativeBatchSuccess.sampled_none_le good) count) 1

/-- At every count, zero included, the actual completed candidate meets its
all-input source success, joint state, restoration and resource requirements. -/
public theorem completedAlgorithm_solves (input : Input N) (count : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.Solves (completedAlgorithm base noQuantum input count)
      (completedAllProblem base noQuantum input duration unitQueries count) := by
  cases count with
  | zero =>
      exact zeroAlgorithm_solves base noQuantum input duration unitQueries
  | succ laterCount =>
      exact completedFiniteAlgorithm_solves
        base noQuantum input laterCount duration unitQueries

/-- At every total count, including the classical zero branch, the completed
algorithm lists the whole original caller, output and owned bank interface. -/
theorem completedAlgorithm_output_listing (input : Input N) (count : Nat) :
    (completedAlgorithm base noQuantum input count).run.output.listing =
      (context base noQuantum N count).keys := by
  cases count with
  | zero => rfl
  | succ laterCount =>
      exact completedFiniteAlgorithm_output_listing
        base noQuantum input laterCount

/-- The actual all-count completed candidate uses the same fixed resident
bank and classical capacity on every path, with no count-dependent bank growth. -/
theorem completedAlgorithm_peakResidentSpace_le (input : Input N) (count : Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    (completedAlgorithm base noQuantum input count).run.code.peakResidentSpace path ≤
      additionalSpace N count + base.residentSpace := by
  cases count with
  | zero =>
      intro axis
      change max (base.residentSpace axis)
        (max (SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis +
          base.residentSpace axis) 0) ≤
        SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis + base.residentSpace axis
      omega
  | succ laterCount =>
      exact completedFiniteAlgorithm_peakResidentSpace_le
        base noQuantum input laterCount path

/-- Every actual all-count path preserves the caller's separate auxiliary role. -/
theorem completedAlgorithm_peakAuxiliarySpace_le (input : Input N) (count : Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    (completedAlgorithm base noQuantum input count).run.code.peakAuxiliarySpace path ≤
      additionalSpace N count + base.auxiliarySpace := by
  cases count with
  | zero =>
      intro axis
      change max (base.auxiliarySpace axis)
        (max (SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis +
          base.auxiliarySpace axis) 0) ≤
        SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis + base.auxiliarySpace axis
      omega
  | succ laterCount =>
      exact completedFiniteAlgorithm_peakAuxiliarySpace_le
        base noQuantum input laterCount path

/-- The all-count independent problem retains the original fixed resident
allowance, with its zero branch's classical allocation included. -/
theorem completedAllProblem_residentSpace (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (count : Nat) :
    (completedAllProblem base noQuantum input duration unitQueries count).resources.resident =
      additionalSpace N count + base.residentSpace := by
  cases count <;> rfl

/-- The same independent completed problem preserves the caller's separate
auxiliary role at every count. -/
theorem completedAllProblem_auxiliarySpace (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (count : Nat) :
    (completedAllProblem base noQuantum input duration unitQueries count).resources.auxiliary =
      additionalSpace N count + base.auxiliarySpace := by
  cases count <;> rfl

/-- The independent public auxiliary budget bounds every actual path at every count. -/
public theorem completedAlgorithm_peakAuxiliarySpace_le_budget (input : Input N)
    (count : Nat) (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    (completedAlgorithm base noQuantum input count).run.code.peakAuxiliarySpace path ≤
      (completedAllProblem base noQuantum input duration unitQueries
        count).resources.auxiliary := by
  rw [completedAllProblem_auxiliarySpace]
  exact completedAlgorithm_peakAuxiliarySpace_le base noQuantum input count path

/-- The all-count completed code charges serial dependencies of each real
batch, pack and physical reset for any native event-duration assignment. -/
theorem completedAlgorithm_depth_le (input : Input N) (count : Nat)
    (duration : Resource.Event (model input) → Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    (completedAlgorithm base noQuantum input count).run.code.depth duration path ≤
      match count with
      | 0 => Cleanup.durationBudget input duration 0
      | laterCount + 1 =>
          Cleanup.completedDurationBudget N input laterCount duration := by
  cases count with
  | zero =>
      exact Nat.le_refl 0
  | succ laterCount =>
      exact completedFiniteAlgorithm_depth_le
        base noQuantum input laterCount duration path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
