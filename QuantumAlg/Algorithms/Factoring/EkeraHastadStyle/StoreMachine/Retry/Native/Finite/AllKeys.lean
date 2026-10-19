/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.InputProtocol
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint

/-!
# All-input exact source law for the actual native finite retry

The executable native algorithm takes the original modulus input. Its accepted
event is a checked nontrivial divisor, including on exceptional keys. The
actual selected output has exact success probability `1 - q^k`, where `q` is
the independently specified single-batch source failure mass. This remains
separate from the stronger conditional good-key and average-key bounds.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry.AllKeys

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The complete native algorithm's independent finite-count all-input contract. -/
def problem (input : Input N) (count : Nat) :
    Problem RuntimeRound.model base (context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ output => NativeCycles.InputProtocol.accepts N output
  successLB := fun _ _ => ⟨1 - NativeCycles.InputProtocol.sourceFailure input ^ count, tsub_le_self⟩
  states := fun _ _ => [stateRequirement base noQuantum N count]
  resources :=
    { events := eventEnvelope N count
      resident := base.residentSpace + additionalSpace N count
      auxiliary := base.auxiliarySpace + additionalSpace N count }
  quantumTimeLimit := depthBound N count

private lemma accepted_iff_populated (input : Input N) (count : Nat)
    {Reference : Register}
    (original : OracleInput RuntimeRound.model.classicalOracles base Reference)
    (output : (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (supported : output ∈
      ((run base noQuantum input count).outputDistribution environment original).support) :
    output ∈ NativeCycles.InputProtocol.accepts N ↔
      output ≠ CShape.Value.optionNone := by
  cases output with
  | optionNone => simp [NativeCycles.InputProtocol.accepts]
  | optionSome word =>
      have sound := run_some_sound (environment := environment)
        base noQuantum input count original word supported
      constructor
      · intro _ impossible
        cases impossible
      · intro _
        exact ⟨word, rfl, sound.1, sound.2.1, sound.2.2⟩

/-- The actual native run has the exact source failure power on every input. -/
lemma successProbability (input : Input N) (count : Nat)
    {Reference : Register}
    (original : OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((run base noQuantum input count).outputDistribution environment original).toOuterMeasure
        (NativeCycles.InputProtocol.accepts N) =
      1 - NativeCycles.InputProtocol.sourceFailure input ^ count := by
  calc
    ((run base noQuantum input count).outputDistribution environment original).toOuterMeasure
        (NativeCycles.InputProtocol.accepts N) =
      ((run base noQuantum input count).outputDistribution environment original).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
      apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
      ext output
      simp only [Set.mem_inter_iff]
      apply and_congr_left
      intro supported
      exact accepted_iff_populated base noQuantum input count original output supported
    _ = 1 - NativeCycles.InputProtocol.sourceFailure input ^ count :=
      run_successProbability base noQuantum input count original

private lemma relationalProbability (input : Input N) (count : Nat)
    {Reference : Register}
    (original : OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((algorithm base noQuantum input count).relationalDistribution environment
      original).toOuterMeasure
        {pair | (problem base noQuantum input count).accepts environment () pair.1 pair.2} =
      1 - NativeCycles.InputProtocol.sourceFailure input ^ count := by
  have projection :
      ((algorithm base noQuantum input count).relationalDistribution environment
        original).toOuterMeasure
          {pair | (problem base noQuantum input count).accepts environment () pair.1 pair.2} =
        ((run base noQuantum input count).outputDistribution environment original).toOuterMeasure
          (NativeCycles.InputProtocol.accepts N) := by
    simp only [Algorithm.relationalDistribution, algorithm,
      AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans (successProbability base noQuantum input count original)

/-- Exact success, full state, borrowed restoration and budgets for every native input. -/
lemma solves (input : Input N) (count : Nat) :
    Algorithm.Solves (algorithm base noQuantum input count)
      (problem base noQuantum input count) := by
  constructor
  · intro environment _witness Reference original _valid _initialized
    exact le_of_eq (relationalProbability base noQuantum input count original).symm
  · intro environment _witness Reference original _valid _initialized requirement present
    have same : requirement = stateRequirement base noQuantum N count :=
      List.mem_singleton.mp present
    subst requirement
    exact stateRequirement_holds base noQuantum N input count original
  · intro environment _witness Reference original _valid _initialized
    exact run_restoresBorrowed base noQuantum input count original
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact run_pool_le base noQuantum input count path
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact run_resident_le base noQuantum input count path
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact run_auxiliary_le base noQuantum input count path
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact run_quantumTime_le base noQuantum input count path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry.AllKeys
