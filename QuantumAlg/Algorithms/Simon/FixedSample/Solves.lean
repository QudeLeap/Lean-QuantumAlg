/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Simon.FixedSample.Spec
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.Simon.FixedSample.Spec
import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Resources
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete correctness of the actual fixed-sample Simon run

Success, event coordinates, live spaces and unit depth concern the same
sample-and-recovery execution. The hidden word and semantic model occur
only in the proof; the algorithm receives the actual sampling circuit and
positive slack. The original finite-sample scope is unchanged.
-/

namespace QuantumAlg.SimonsProblem

open Execution FixedSample

noncomputable section

universe u

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma output_probability_le_relational {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape} (run : AlgorithmRun model pre post shape)
    (environment : model.Environment)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference) (value :
      shape.Value) :
    run.outputDistribution environment input value ≤
      (run.relationalDistribution environment input).toOuterMeasure {pair | pair.2 = value} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  apply (run.executionDistribution environment input).toOuterMeasure_mono
  intro record member
  exact member.1

/-- The actual algorithm takes the sampling circuit and slack, with no hidden-word input. -/
public def algorithm {n : Nat} (sampling : SamplingCircuit n) (κ : SecurityParameter) :
    Algorithm (executionModel n) inputContext (outputContext n κ) (.option
      (.unsignedWord n)) where
  run := Native.recoveryRun inputContext rfl n (sampleCount n κ) sampling

attribute [local irreducible] Native.recoveryCode Native.code Native.sampleBatch Native.allocate

/-- One physical-bank implementation meets the original fixed-sample Simon contract. -/
private lemma algorithm_solves {n : Nat} (sampling : SamplingCircuit n)
    (κ : SecurityParameter) :
    (algorithm sampling κ).Solves (problem sampling κ) where
  success := by
    intro environment secret Reference input promise initialization
    exact (Native.nativeSimon_recovery_success inputContext rfl n sampling secret κ promise
      input).trans
      (output_probability_le_relational (algorithm sampling κ).run environment input
        (.optionSome (.unsignedWord secret)))
  states := by
    intro environment secret Reference input valid initialization requirement member
    cases member
  borrowed := by
    intro environment secret Reference input valid initialization
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (Native.recoveryCode inputContext rfl n (sampleCount n κ) sampling)
      environment rfl reference state
  events := by
    intro environment secret Reference input valid initialization path supported
    exact Native.nativeSimon_recovery_pool_le inputContext rfl n (sampleCount n κ)
      sampling path
  resident := by
    intro environment secret Reference input valid initialization path supported
    change (Native.recoveryCode inputContext rfl n (sampleCount n κ)
      sampling).peakResidentSpace path ≤
        Native.recoveryScratchSpace (sourceModel n) n (sampleCount n κ) +
          Native.samplingSpace n (sampleCount n κ)
    have emptySpace : inputContext.residentSpace = 0 := RuntimeCtx.residentSpace_empty
    simpa only [emptySpace, add_zero] using
      Native.nativeSimon_recovery_resident_le inputContext rfl n (sampleCount n κ)
        sampling path
  auxiliary := by
    intro environment secret Reference input valid initialization path supported
    change (Native.recoveryCode inputContext rfl n (sampleCount n κ)
      sampling).peakAuxiliarySpace path ≤
        Native.recoveryScratchSpace (sourceModel n) n (sampleCount n κ) +
          Native.samplingSpace n (sampleCount n κ)
    have emptySpace : inputContext.auxiliarySpace = 0 := RuntimeCtx.auxiliarySpace_empty
    simpa only [emptySpace, add_zero] using
      Native.nativeSimon_recovery_auxiliary_le inputContext rfl n (sampleCount n κ)
        sampling path
  time := by
    intro environment secret Reference input valid initialization path supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact Native.nativeSimon_recovery_depth_le inputContext rfl n (sampleCount n κ)
      sampling path

/-- One fixed sampler meets the complete contract for every admitted oracle and hidden word. -/
public theorem main {n : Nat} (sampling : SamplingCircuit n) (κ : SecurityParameter) :
    ∃ candidate : Algorithm (executionModel n) inputContext (outputContext n κ)
      (.option (.unsignedWord n)), candidate.Solves (problem sampling κ) :=
  ⟨algorithm sampling κ, algorithm_solves sampling κ⟩

end

end QuantumAlg.SimonsProblem
