/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Recovery
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Batch
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Selection
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution
import all QuantumAlg.Core.Execution.Reference.Kernel
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Util.PMF.VectorMass
import Mathlib.Data.Vector.Basic

/-!
# Chronological fresh batches and actual first-success selection

Each batch projects to a fresh sample of the same independent mathematical
factor law, while preserving all other factor cells. The finite induction
follows the actual increasing indices, including the empty suffix. It never
equates an arbitrary full-Store observation with a constant.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program.Probability

noncomputable section

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- The factor-coordinate projection of the actual chronological Store updates. -/
def factorUpdates {N count : Nat} : (length : Nat) → (Fin length → Fin count) →
    List.Vector (Factor N) length → (Fin count → Factor N) → (Fin count → Factor N)
  | 0, _, _, before => before
  | length + 1, indices, values, before =>
      factorUpdates length (fun index => indices index.succ) values.tail
        (Function.update before (indices 0) values.head)

private lemma factorUpdates_other {N count : Nat} (length : Nat)
    (indices : Fin length → Fin count) (other : Fin count)
    (outside : ∀ index, indices index ≠ other) (values : List.Vector (Factor N) length)
    (before : Fin count → Factor N) :
    factorUpdates length indices values before other = before other := by
  induction length generalizing before with
  | zero => rfl
  | succ length ih =>
      exact (ih (fun index => indices index.succ) (fun index => outside index.succ)
        values.tail _).trans (Function.update_of_ne (Ne.symm (outside 0)) _ _)

private lemma factorUpdates_read {N count : Nat} (length : Nat)
    (indices : Fin length → Fin count) (injective : Function.Injective indices)
    (values : List.Vector (Factor N) length) (before : Fin count → Factor N)
    (index : Fin length) : factorUpdates length indices values before (indices index) =
      values.get index := by
  induction length generalizing before with
  | zero => exact Fin.elim0 index
  | succ length ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · simpa only [factorUpdates, List.Vector.get_zero] using
          (factorUpdates_other length (fun index => indices index.succ) (indices 0)
          (fun index same => Fin.succ_ne_zero index (injective same)) values.tail _).trans
            (Function.update_self _ _ _)
      · simpa only [factorUpdates, List.Vector.get_tail_succ] using
          ih (fun index => indices index.succ)
            (fun _ _ same => Fin.succ_injective _ (injective same)) values.tail
            (Function.update before (indices 0) values.head) index

/-- Updating every later factor leaves only the actual first factor beside the new suffix. -/
lemma factorUpdates_suffix {N : Nat} (laterCount : Nat)
    (values : List.Vector (Factor N) laterCount) (before : Fin (laterCount + 1) → Factor N) :
    List.ofFn (factorUpdates laterCount Fin.succ values before) = before 0 :: values.toList := by
  have vector : List.Vector.ofFn (factorUpdates laterCount Fin.succ values before) =
      List.Vector.cons (before 0) values := by
    apply List.Vector.ext
    intro index
    simp only [List.Vector.get_ofFn]
    refine Fin.cases ?_ (fun index => ?_) index
    · simpa only [List.Vector.get_cons_zero] using
        factorUpdates_other laterCount Fin.succ 0
          (fun index => Fin.succ_ne_zero index) values before
    · simpa only [List.Vector.get_cons_succ] using
        factorUpdates_read laterCount Fin.succ (Fin.succ_injective _) values before index
  simpa only [List.Vector.toList_ofFn, List.Vector.toList_cons] using
    congrArg List.Vector.toList vector

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- Arbitrary factor-vector weights follow the actual sequence of independent fresh batch laws. -/
lemma nextSequence_factorKernel (input : Input N) (length : Nat)
    (indices : Fin length → Fin count) (weight : (Fin count → Factor N) → ℂ)
    (stored : Store (readyContext base noQuantum N count)) :
    Circuit.forRangeReferenceKernel length
        (fun index => nextBatchReferenceKernel base noQuantum N input count (indices index))
        (fun after => weight (factorRead base noQuantum N count after)) stored =
      ∑ values : List.Vector (Factor N) length,
        ((PMF.independentReplicateVector (batchDistribution input) length values).toReal : ℂ) *
          weight (factorUpdates length indices values
            (factorRead base noQuantum N count stored)) := by
  induction length generalizing stored with
  | zero =>
      simp only [Circuit.forRangeReferenceKernel, factorUpdates,
        PMF.independentReplicateVector, PMF.pure_apply, apply_ite, ENNReal.toReal_one,
        ENNReal.toReal_zero, Complex.ofReal_one, Complex.ofReal_zero,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | succ length ih =>
      let tailWeight : (Fin count → Factor N) → ℂ := fun before =>
        ∑ values : List.Vector (Factor N) length,
          ((PMF.independentReplicateVector (batchDistribution input) length values).toReal : ℂ) *
            weight (factorUpdates length (fun index => indices index.succ) values before)
      have tail : Circuit.forRangeReferenceKernel length
          (fun index => nextBatchReferenceKernel base noQuantum N input count (indices index.succ))
          (fun after => weight (factorRead base noQuantum N count after)) =
          (fun after => tailWeight (factorRead base noQuantum N count after)) := by
        funext after
        exact ih (fun index => indices index.succ) after
      rw [Circuit.forRangeReferenceKernel, tail,
        nextBatch_factorKernel base noQuantum N count input,
        PMF.independentReplicateVector_weighted_cons]
      rfl

/-- The actual selector reads exactly the chronological recovered-factor vector. -/
lemma selectionStore_output (input : Input N) (laterCount : Nat)
    (stored : Store (readyContext base noQuantum N (laterCount + 1))) :
    (positiveRun base noQuantum N input laterCount).output.eval
        (selectionStore base noQuantum N (laterCount + 1) stored) =
      FirstAccepted.Direct.Optional.Distribution.firstValue
        (List.ofFn (factorRead base noQuantum N (laterCount + 1) stored)) :=
  Store.read_write_same stored _ _

/-- The actual later-batch suffix supplies independent factors after the preserved first result. -/
lemma laterBatches_selected (input : Input N) (laterCount : Nat) (weight : Factor N → ℂ)
    (stored : Store (readyContext base noQuantum N (laterCount + 1))) :
    laterBatchesReferenceKernel base noQuantum N input laterCount
        (fun after => weight ((positiveRun base noQuantum N input laterCount).output.eval
          (selectionStore base noQuantum N (laterCount + 1) after))) stored =
      ∑ values : List.Vector (Factor N) laterCount,
        ((PMF.independentReplicateVector (batchDistribution input) laterCount values).toReal : ℂ) *
          weight (FirstAccepted.Direct.Optional.Distribution.firstValue
            (factorRead base noQuantum N (laterCount + 1) stored 0 :: values.toList)) := by
  have observed : (fun after => weight
      ((positiveRun base noQuantum N input laterCount).output.eval
        (selectionStore base noQuantum N (laterCount + 1) after))) =
      (fun after => weight (FirstAccepted.Direct.Optional.Distribution.firstValue
        (List.ofFn (factorRead base noQuantum N (laterCount + 1) after)))) := by
    funext after
    exact congrArg weight (selectionStore_output base noQuantum N input laterCount after)
  rw [observed]
  have actual := nextSequence_factorKernel base noQuantum N (laterCount + 1) input
    laterCount Fin.succ
    (fun factors => weight (FirstAccepted.Direct.Optional.Distribution.firstValue
      (List.ofFn factors))) stored
  simpa only [laterBatchesReferenceKernel, factorUpdates_suffix] using actual

end

end QuantumAlg.Factoring.RSA.Recycling.Program.Probability
