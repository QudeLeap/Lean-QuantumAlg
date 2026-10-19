/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Retry
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Member
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Recovery
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Batch
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Source
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Selection
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Kernel
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Observation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Preparation.Observation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Empty
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# The actual recycled RSA output has the original finite-retry distribution

The first source is drawn on the actual classical frame before allocation of
the bank. The complete-Store kernel carries that draw through preparation,
sixteen members, recovery, chronological later draws and actual selection.
Only the final output weight becomes independent of the incoming Store.
The zero-count branch is the literal native empty-result program.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program.Probability

noncomputable section

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- The unchanged mathematical first-success law of the original one-batch distribution. -/
def outputDistribution {N : Nat} (input : Input N) (count : Nat) : PMF (Factor N) :=
  FirstAccepted.Direct.Optional.Distribution.selectedDistribution (batchDistribution input) count

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma firstPrepared_parameter (input : Input N) (laterCount : Nat)
    (stored : Store (ClassicalFrame.context base N (laterCount + 1)))
    (sample : Fin (2 ^ residueSamplingBits N)) :
    parameterRead base noQuantum N (laterCount + 1) 0
      (ShortDLP.CompiledMAU.Recycling.PreparationObservation.preparedStore
        (ClassicalFrame.context base N (laterCount + 1))
        (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
        (sourceStore N (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
          (ClassicalFrame.parameterRef base N (laterCount + 1) 0) stored sample)) =
      parameterValue input sample := by
  have preserved (original : Store (ClassicalFrame.context base N (laterCount + 1))) :
      parameterRead base noQuantum N (laterCount + 1) 0
        (ShortDLP.CompiledMAU.Recycling.PreparationObservation.preparedStore
          (ClassicalFrame.context base N (laterCount + 1))
          (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) original) =
        original.read (FirstAccepted.cellRead
          (ClassicalFrame.parameterRef base N (laterCount + 1) 0)) := by
    have cells := MeasurementCells.read_pushStore_liftWrite 2
      (ShortDLP.CompiledMAU.Recycling.resultBits (shortLogBits N) (tradeoffBits N))
      (original.pushOwnedLayout (ClassicalFrame.context base N (laterCount + 1)).canonicalFreshKey
        (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout (arithmeticBits N)).toQuantum
        (ClassicalFrame.context base N (laterCount + 1)).canonicalFreshKey_fresh
        (ClassicalFrame.bankDisjoint base noQuantum N (laterCount + 1)))
      { toCStorageRef :=
          (ClassicalFrame.parameterRef base N (laterCount + 1) 0).toCStorageRef.underOwnedLayout
            (ClassicalFrame.context base N (laterCount + 1)).canonicalFreshKey
            (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout (arithmeticBits N)).toQuantum
            (ClassicalFrame.context base N (laterCount + 1)).canonicalFreshKey_fresh
            (ClassicalFrame.bankDisjoint base noQuantum N (laterCount + 1))
        writable := (ClassicalFrame.parameterRef base N (laterCount + 1) 0).writable }
    have bank := Store.read_pushOwnedLayout_underOwnedLayout original
      (ClassicalFrame.context base N (laterCount + 1)).canonicalFreshKey
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout (arithmeticBits N)).toQuantum
      (ClassicalFrame.context base N (laterCount + 1)).canonicalFreshKey_fresh
      (ClassicalFrame.bankDisjoint base noQuantum N (laterCount + 1))
      (FirstAccepted.cellRead (ClassicalFrame.parameterRef base N (laterCount + 1) 0))
    exact cells.trans bank
  exact (preserved (sourceStore N (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (ClassicalFrame.parameterRef base N (laterCount + 1) 0) stored sample)).trans
      (rsaRecyclingParent_sourceStore_parameter N
        (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
        (ClassicalFrame.parameterRef base N (laterCount + 1) 0) input stored sample)

/-- Arbitrary final output weights of positive execution are constant on every incoming Store. -/
lemma positiveReferenceKernel_output (input : Input N) (laterCount : Nat)
    (weight : Factor N → ℂ) (original : Store base) :
    positiveReferenceKernel base noQuantum N input laterCount
        (fun stored => weight ((positiveRun base noQuantum N input laterCount).output.eval stored))
        original =
      ∑ output : Factor N,
        ((outputDistribution input (laterCount + 1) output).toReal : ℂ) * weight output := by
  let remaining : Factor N → ℂ := fun first =>
    ∑ values : List.Vector (Factor N) laterCount,
      ((PMF.independentReplicateVector (batchDistribution input) laterCount values).toReal : ℂ) *
        weight (FirstAccepted.Direct.Optional.Distribution.firstValue (first :: values.toList))
  have tail : laterBatchesReferenceKernel base noQuantum N input laterCount
      (fun stored => weight ((positiveRun base noQuantum N input laterCount).output.eval
        (selectionStore base noQuantum N (laterCount + 1) stored))) =
      (fun stored => remaining (factorRead base noQuantum N (laterCount + 1) stored 0)) := by
    funext stored
    exact laterBatches_selected base noQuantum N input laterCount weight stored
  have firstMoment : positiveReferenceKernel base noQuantum N input laterCount
      (fun stored => weight ((positiveRun base noQuantum N input laterCount).output.eval stored))
      original =
      ∑ factor : Factor N, ((batchDistribution input factor).toReal : ℂ) * remaining factor := by
    rw [batchDistribution_weighted]
    unfold positiveReferenceKernel tailReferenceKernel
    rw [tail]
    apply Finset.sum_congr rfl
    intro sample _
    apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
    have actual := batchBody_factorKernel base noQuantum N (laterCount + 1) input sample 0
      (fun factors => remaining (factors 0)) _
      (firstPrepared_parameter base noQuantum N input laterCount
        (ClassicalFrame.pushStore base N (laterCount + 1) original) sample)
    simpa only [Function.update_self] using actual
  refine firstMoment.trans ?_
  have mapped := PMF.sum_map_toReal_mul
    (PMF.independentReplicateVector (batchDistribution input) (laterCount + 1))
    (fun values => FirstAccepted.Direct.Optional.Distribution.firstValue values.toList) weight
  have vector := PMF.independentReplicateVector_weighted_cons (batchDistribution input)
    laterCount (fun values => weight
      (FirstAccepted.Direct.Optional.Distribution.firstValue values.toList))
  exact (mapped.trans (by simpa only [List.Vector.toList_cons] using vector)).symm

/-- The literal actual run output has the original selected-distribution moment at every count. -/
lemma referenceKernel_output (input : Input N) (count : Nat)
    (weight : Factor N → ℂ) (original : Store base) :
    referenceKernel base noQuantum N input count
        (fun stored => weight ((run base noQuantum N input count).output.eval stored)) original =
      ∑ output : Factor N,
        ((outputDistribution input count output).toReal : ℂ) * weight output := by
  cases count with
  | zero =>
      change weight ((NativeRetryEmpty.run base N).output.eval
        (original.pushRetained base.canonicalFreshKey
          (LatticeBatchRecoveryOutput.OutputShape N) base.runtimeCtx_canonicalFreshKey_fresh)) = _
      rw [NativeRetryEmpty.run_output]
      simp only [outputDistribution,
        FirstAccepted.Direct.Optional.Distribution.selectedDistribution,
        PMF.independentReplicateVector, PMF.pure_map,
        FirstAccepted.Direct.Optional.Distribution.firstValue, List.Vector.toList_nil,
        List.foldl_nil, PMF.pure_apply, apply_ite, ENNReal.toReal_one,
        ENNReal.toReal_zero, Complex.ofReal_one, Complex.ofReal_zero,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | succ laterCount =>
      exact positiveReferenceKernel_output base noQuantum N input laterCount weight original

/-- The original output law holds entrywise for both coordinates of every external reference. -/
lemma run_output_reference (input : Input N) (count : Nat)
    {Reference : Register}
    (state : ExecutionState
      (Store base × ShortDLP.CompiledMAU.Recycling.model.HiddenState)
      (Register.prod base.register Reference))
    (weight : Factor N → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((run base noQuantum N input count).execute environment Reference state)
        (fun entry _ => weight ((run base noQuantum N input count).output.eval entry.1))
        left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ output : Factor N,
          ((outputDistribution input count output).toReal : ℂ) * weight output) left right := by
  refine (rsaRecyclingParent_run_referenceFiberSum base noQuantum N input count state
    (fun stored => weight ((run base noQuantum N input count).output.eval stored))
      left right).trans ?_
  apply congrArg (fun observed => ExecutionState.referenceFiberSum state observed left right)
  funext entry _basis
  exact referenceKernel_output base noQuantum N input count weight entry.1

/-- Actual trace-derived output probabilities equal the original finite-retry PMF. -/
lemma run_outputPMF (input : Input N) (count : Nat) {Reference : Register}
    (state : ExecutionState
      (Store base × ShortDLP.CompiledMAU.Recycling.model.HiddenState)
      (Register.prod base.register Reference)) (normalized : state.IsNormalized) :
    (((run base noQuantum N input count).execute environment Reference state).toPMF
      (((run base noQuantum N input count).execute_mass environment Reference state).trans
        normalized)).map
        (fun entry => (run base noQuantum N input count).output.eval entry.1) =
      outputDistribution input count := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state _ normalized
    (((run base noQuantum N input count).execute_mass environment Reference state).trans normalized)
  intro selected left right
  exact (run_output_reference base noQuantum N input count state
    (fun value => if value = selected then 1 else 0) left right).trans
    (congrArg (fun coefficient : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => coefficient) left right)
      (PMF.sum_toReal_indicator (outputDistribution input count) selected))

end

end QuantumAlg.Factoring.RSA.Recycling.Program.Probability
