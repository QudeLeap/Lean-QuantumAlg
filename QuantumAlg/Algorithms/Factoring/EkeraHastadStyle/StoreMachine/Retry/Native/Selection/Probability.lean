/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Core.Algorithm.ClassicalOp

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Probability
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution

/-!
# Exact empty and populated probabilities of the actual first-success output

The real selection tail maps the real chronological factor-vector law.
Its original optional-word update is the mathematical first-success fold,
so the actual empty output has the original one-batch empty probability
raised to the total number of batches. Natural-number decoding below is
only a mathematical observation of the same actual optional word.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection

noncomputable section

open Execution ClassicalRoutines.FirstAccepted.Direct

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem firstValue_encoded {N length : Nat}
    (values : List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value length) :
    firstValue (.fixedVector values.get) = Optional.Distribution.firstValue values.toList := by
  unfold firstValue Optional.Distribution.firstValue
  have listed : List.ofFn values.get = values.toList :=
    (List.Vector.toList_ofFn values.get).symm.trans
      (congrArg List.Vector.toList (List.Vector.ofFn_get values))
  exact congrArg (fun entries => entries.foldl Optional.retainValue CShape.Value.optionNone)
    listed

private theorem map_point_of_singleton_fiber {Source Target : Type}
    (distribution : PMF Source) (read : Source → Target) (source : Source) (target : Target)
    (fiber : ∀ value, target = read value ↔ value = source) :
    distribution.map read target = distribution source := by
  rw [PMF.map_apply]
  simp only [fiber, tsum_ite_eq]

/-- Typed optional encoding has exactly the original empty value as its empty-output preimage. -/
theorem batch_outputValue_none {N : Nat} (specification : Input N) :
    (sampledBatchOutputPMF specification).map (LatticeBatchRecoveryOutput.outputValue (N := N))
        CShape.Value.optionNone = sampledBatchOutputPMF specification none := by
  apply map_point_of_singleton_fiber (sampledBatchOutputPMF specification)
    (LatticeBatchRecoveryOutput.outputValue (N := N)) none CShape.Value.optionNone
  intro value
  cases value <;> simp [LatticeBatchRecoveryOutput.outputValue]

/-- Read the natural payload of the actual nominal optional word as a mathematical observation. -/
public def decodeFactor {N : Nat} : (LatticeBatchRecoveryOutput.OutputShape N).Value → Option Nat
  | .optionNone => none
  | .optionSome word => some word.toNat

private theorem decodedDistribution_none {N : Nat}
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    distribution.map decodeFactor none = distribution CShape.Value.optionNone := by
  apply map_point_of_singleton_fiber distribution decodeFactor CShape.Value.optionNone none
  intro value
  cases value with
  | optionNone => constructor <;> intro _ <;> rfl
  | optionSome word =>
      change ((none : Option Nat) = some word.toNat ↔ _)
      simp only [reduceCtorEq]

attribute [local irreducible] NativeRetryChain.context NativeRetryChain.code code tail step

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The actual selected run has the original chronological first-success distribution. -/
theorem run_selectedDistribution (specification : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum specification count).outputDistribution input =
      Optional.Distribution.selectedDistribution
        ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue)
        (count + 1) := by
  rw [outputDistribution, NativeRetryChain.run_outputDistribution, PMF.map_comp]
  exact congrArg
    (fun read => (PMF.independentReplicateVector
      ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue)
      (count + 1)).map read)
    (funext fun values => firstValue_encoded values)

/-- Actual selection is empty exactly with the original one-batch empty probability's power. -/
theorem run_none (specification : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum specification count).outputDistribution input CShape.Value.optionNone =
      sampledBatchOutputPMF specification none ^ (count + 1) := by
  rw [run_selectedDistribution, Optional.Distribution.selectedDistribution_none,
    batch_outputValue_none]

/-- Natural observation preserves exactly the same actual empty-output event and probability. -/
theorem run_decoded_none (specification : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum specification count).outputDistribution input).map decodeFactor none =
      sampledBatchOutputPMF specification none ^ (count + 1) := by
  rw [decodedDistribution_none, run_none]

/-- The actual populated-output event has the complementary exact finite success probability. -/
theorem run_successProbability (specification : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum specification count).outputDistribution input).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} =
      1 - sampledBatchOutputPMF specification none ^ (count + 1) := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  have complement : {value : (LatticeBatchRecoveryOutput.OutputShape N).Value |
      ¬ value ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
    ext value
    simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [complement, PMF.toOuterMeasure_apply_singleton, run_none]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection
