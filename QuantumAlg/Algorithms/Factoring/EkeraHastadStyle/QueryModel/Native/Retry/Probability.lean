/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Observation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Sampled
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Util.PMF.VectorMass

/-!
# First-success probabilities of the actual reused original oracle bank

The same actual fixed context executes its first prepared batch, then every
requested later redraw and paid reset batch. A finite weighted fold follows
the real selector update in that chronological order. The independent-vector
expression is its derived mathematical distribution, rather than a sampler
assumption or replacement execution. Final output reads the one actual paid
pack into the existing factor cell. Every original input and Reference is
preserved; the good-key assumption enters only the final numerical bound.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def moment {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (previous : (CShape.option (.unsignedWord width)).Value)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) : ℂ :=
  ∑ samples : List.Vector (CShape.option (.unsignedWord width)).Value count,
    ((PMF.independentReplicateVector distribution count samples).toReal : ℂ) *
      weight (samples.toList.foldl Optional.retainValue previous)

private theorem moment_zero {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value)
    (previous : (CShape.option (.unsignedWord width)).Value)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) :
    moment distribution 0 previous weight = weight previous := by
  simp [moment, PMF.independentReplicateVector, apply_ite]

private theorem moment_succ {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (previous : (CShape.option (.unsignedWord width)).Value)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) :
    moment distribution (count + 1) previous weight =
      ∑ candidate : (CShape.option (.unsignedWord width)).Value,
        ((distribution candidate).toReal : ℂ) *
          moment distribution count (Optional.retainValue previous candidate) weight :=
  PMF.independentReplicateVector_weighted_cons distribution count
    (fun values => weight (values.toList.foldl Optional.retainValue previous))

private theorem moment_selected {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) :
    moment distribution count .optionNone weight =
      ∑ selected : (CShape.option (.unsignedWord width)).Value,
        ((Optional.Distribution.selectedDistribution distribution count selected).toReal : ℂ) *
          weight selected :=
  (PMF.sum_map_toReal_mul (PMF.independentReplicateVector distribution count)
    (fun values => Optional.Distribution.firstValue values.toList) weight).symm

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem range_reference (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Circuit.forRange count (fun _ => next base noQuantum N input)).execute Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => moment
          ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue) count
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1) weight)
        left right := by
  induction count generalizing History with
  | zero =>
      have executed := congrArg
        (fun output : State (context base noQuantum N) Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight
              (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
            left right) (Circuit.execute_id_mapClassical Reference state)
      refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2, ())))
        (fun entry _ => weight
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
        left right).trans ?_)
      simp only [moment_zero]
  | succ count ih =>
      let head := next base noQuantum N input
      let tail := Circuit.forRange count (fun _ => next base noQuantum N input)
      have later := ih (head.execute Reference state)
      have earlier := nativeOracle_retry_next_reference base noQuantum N input state
        (fun selected => moment
          ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          count selected weight) left right
      refine (Circuit.referenceFiberSum_execute_seq head tail state
        (fun store => weight
          (Optional.selectedValue (selectionRefs base noQuantum N).selection store))
        left right).trans (later.trans (earlier.trans ?_))
      apply congrArg
        (fun observe : (Store (context base noQuantum N) × History) →
            (context base noQuantum N).register.Index → ℂ =>
          ExecutionState.referenceFiberSum state observe left right)
      funext entry basis
      exact (moment_succ _ count _ weight).symm

/-- The real first batch, later loop and final paid pack have the original first-value law. -/
theorem nativeOracle_retry_reference (input : Input N) (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum N input laterCount).execute Reference state)
      (fun entry _ => weight (entry.1.read
        (.storage (factorRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((Optional.Distribution.selectedDistribution
            ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            (laterCount + 1) selected).toReal : ℂ) * weight selected) left right := by
  let entered := (first base noQuantum N input).execute Reference state
  let loop := Circuit.forRange laterCount (fun _ => next base noQuantum N input)
  let observe := fun store : Store (context base noQuantum N) =>
    weight (store.read (.storage (factorRef base noQuantum N).toCStorageRef))
  have packed := nativeOracle_retry_pack_reference base noQuantum N
    (loop.execute Reference entered) weight left right
  have repeated := range_reference base noQuantum N input laterCount entered weight left right
  have initialized := nativeOracle_retry_first_reference base noQuantum N input state
    (fun selected => moment
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
      laterCount selected weight) left right
  have combined := (Circuit.referenceFiberSum_execute_seq (first base noQuantum N input)
    (loop.seq (pack base noQuantum N)) state observe left right).trans
      ((Circuit.referenceFiberSum_execute_seq loop (pack base noQuantum N) entered observe
        left right).trans (packed.trans (repeated.trans initialized)))
  refine combined.trans ?_
  apply congrArg
    (fun scalar : ℂ => ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
  exact (moment_succ _ laterCount .optionNone weight).symm.trans
    (moment_selected _ (laterCount + 1) weight)

/-- The actual complete output distribution is chronological first success in the original bank. -/
theorem nativeOracle_retry_outputDistribution (input : Input N) (laterCount : Nat)
    {Reference : Register} (original : Execution.Input base Reference) :
    (run base noQuantum N input laterCount).outputDistribution original =
      Optional.Distribution.selectedDistribution
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        (laterCount + 1) := by
  let entered : State base Reference (Store base) :=
    original.state.mapClassical (fun store => (store, store))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun store => (store, store))
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum entered
    ((code base noQuantum N input laterCount).execute Reference entered) normalized
    (((code base noQuantum N input laterCount).execute_mass Reference entered).trans normalized)
    (fun entry => entry.1.read (.storage (factorRef base noQuantum N).toCStorageRef))
    (Optional.Distribution.selectedDistribution
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue) (laterCount + 1))
  intro selected left right
  exact (nativeOracle_retry_reference base noQuantum N input laterCount entered
    (fun value => if value = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum entered (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator _ selected))

/-- The actual empty output is precisely the original batch failure raised to its real count. -/
theorem nativeOracle_retry_none (input : Input N) (laterCount : Nat)
    {Reference : Register} (original : Execution.Input base Reference) :
    (run base noQuantum N input laterCount).outputDistribution original .optionNone =
      sampledBatchOutputPMF input none ^ (laterCount + 1) := by
  rw [nativeOracle_retry_outputDistribution, Optional.Distribution.selectedDistribution_none,
    NativeRetrySelection.batch_outputValue_none]

/-- Only the original good-key domain is needed for the original complementary success floor. -/
theorem nativeOracle_retry_none_le (model : GoodKeyModel N) (laterCount : Nat)
    {Reference : Register} (original : Execution.Input base Reference) :
    (run base noQuantum N model.input laterCount).outputDistribution original .optionNone ≤
      (1 - NativeBatchSuccess.successFloor model.bitWidth) ^ (laterCount + 1) := by
  rw [nativeOracle_retry_none]
  exact pow_le_pow_left' (NativeBatchSuccess.sampled_none_le model) (laterCount + 1)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry
