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

private theorem output_probability_le_relational {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape} (run : AlgorithmRun model pre post shape)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference) (value :
      shape.Value) :
    run.outputDistribution input value ≤
      (run.relationalDistribution input).toOuterMeasure {pair | pair.2 = value} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  apply (run.executionDistribution input).toOuterMeasure_mono
  intro record member
  exact member.1

/-- The actual algorithm takes the sampling circuit and slack, with no hidden-word input. -/
public def algorithm {n : Nat} (sampling : SamplingCircuit n) (κ : SecurityParameter) :
    Algorithm (executionModel sampling.oracle) inputContext (outputContext n κ) (.option
      (.unsignedWord n)) where
  run := Native.recoveryRun inputContext rfl n (sampleCount n κ) sampling

attribute [local irreducible] Native.recoveryCode Native.code Native.sampleBatch Native.allocate

/-- One physical-bank implementation meets the original fixed-sample Simon contract. -/
public theorem main {n : Nat} {α : Type u} {f : Simon.Oracle n α}
    {secret : Simon.BitVec n} (model : Model f secret) (κ : SecurityParameter) :
    (algorithm model.sampling κ).Solves (problem model κ) where
  success := by
    intro Reference input promise initialization
    exact (Native.nativeSimon_recovery_success inputContext rfl n model κ promise input).trans
      (output_probability_le_relational (algorithm model.sampling κ).run input
        (.optionSome (.unsignedWord model.secret)))
  states := by
    intro Reference input valid initialization requirement member
    cases member
  borrowed := by
    intro Reference input valid initialization
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (Native.recoveryCode inputContext rfl n (sampleCount n κ) model.sampling)
      rfl reference state
  events := by
    intro Reference input valid initialization path supported
    exact Native.nativeSimon_recovery_pool_le inputContext rfl n (sampleCount n κ)
      model.sampling path
  resident := by
    intro Reference input valid initialization path supported
    change (Native.recoveryCode inputContext rfl n (sampleCount n κ)
      model.sampling).peakResidentSpace path ≤
        Native.recoveryScratchSpace (sourceModel model.sampling.oracle) n (sampleCount n κ) +
          Native.samplingSpace n (sampleCount n κ)
    have emptySpace : inputContext.residentSpace = 0 := RuntimeCtx.residentSpace_empty
    simpa only [emptySpace, add_zero] using
      Native.nativeSimon_recovery_resident_le inputContext rfl n (sampleCount n κ)
        model.sampling path
  auxiliary := by
    intro Reference input valid initialization path supported
    change (Native.recoveryCode inputContext rfl n (sampleCount n κ)
      model.sampling).peakAuxiliarySpace path ≤
        Native.recoveryScratchSpace (sourceModel model.sampling.oracle) n (sampleCount n κ) +
          Native.samplingSpace n (sampleCount n κ)
    have emptySpace : inputContext.auxiliarySpace = 0 := RuntimeCtx.auxiliarySpace_empty
    simpa only [emptySpace, add_zero] using
      Native.nativeSimon_recovery_auxiliary_le inputContext rfl n (sampleCount n κ)
        model.sampling path
  depth := by
    intro Reference input valid initialization path supported
    exact Native.nativeSimon_recovery_depth_le inputContext rfl n (sampleCount n κ)
      model.sampling path

end

end QuantumAlg.SimonsProblem
