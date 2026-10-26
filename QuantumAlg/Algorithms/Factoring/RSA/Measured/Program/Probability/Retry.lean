/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Probability.Recovery
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Kernel
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution
import all QuantumAlg.Util.PMF.VectorMass

/-!
# Chronological original factor law of the complete measured parent kernels

Actual fresh-source batches update only their own original factor coordinate.
The induction follows their real increasing order and the actual final
first-populated selector [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program.Probability

noncomputable section

variable [configuration : Configuration]

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

omit configuration in
private lemma rsaMeasuredProbability_factorUpdates_other {N count : Nat} (length : Nat)
    (indices : Fin length → Fin count) (other : Fin count)
    (outside : ∀ index, indices index ≠ other) (values : List.Vector (Factor N) length)
    (before : Fin count → Factor N) :
    factorUpdates length indices values before other = before other := by
  induction length generalizing before with
  | zero => rfl
  | succ length ih =>
      exact (ih (fun index => indices index.succ) (fun index => outside index.succ)
        values.tail _).trans (Function.update_of_ne (Ne.symm (outside 0)) _ _)

omit configuration in
private lemma rsaMeasuredProbability_factorUpdates_read {N count : Nat} (length : Nat)
    (indices : Fin length → Fin count) (injective : Function.Injective indices)
    (values : List.Vector (Factor N) length) (before : Fin count → Factor N)
    (index : Fin length) : factorUpdates length indices values before (indices index) =
      values.get index := by
  induction length generalizing before with
  | zero => exact Fin.elim0 index
  | succ length ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · simpa only [factorUpdates, List.Vector.get_zero] using
          (rsaMeasuredProbability_factorUpdates_other length
            (fun index => indices index.succ) (indices 0)
          (fun index same => Fin.succ_ne_zero index (injective same)) values.tail _).trans
            (Function.update_self _ _ _)
      · simpa only [factorUpdates, List.Vector.get_tail_succ] using
          ih (fun index => indices index.succ)
            (fun _ _ same => Fin.succ_injective _ (injective same)) values.tail
            (Function.update before (indices 0) values.head) index

omit configuration in
/-- Updating every later factor leaves only the actual first factor beside the new suffix. -/
lemma rsaMeasuredProbability_factorUpdates_suffix {N : Nat} (laterCount : Nat)
    (values : List.Vector (Factor N) laterCount) (before : Fin (laterCount + 1) → Factor N) :
    List.ofFn (factorUpdates laterCount Fin.succ values before) = before 0 :: values.toList := by
  have vector : List.Vector.ofFn (factorUpdates laterCount Fin.succ values before) =
      List.Vector.cons (before 0) values := by
    apply List.Vector.ext
    intro index
    simp only [List.Vector.get_ofFn]
    refine Fin.cases ?_ (fun index => ?_) index
    · simpa only [List.Vector.get_cons_zero] using
        rsaMeasuredProbability_factorUpdates_other laterCount Fin.succ 0
          (fun index => Fin.succ_ne_zero index) values before
    · simpa only [List.Vector.get_cons_succ] using
        rsaMeasuredProbability_factorUpdates_read laterCount Fin.succ (Fin.succ_injective _)
          values before index
  simpa only [List.Vector.toList_ofFn, List.Vector.toList_cons] using
    congrArg List.Vector.toList vector

variable (base : RuntimeCtx .quantum) (N count : Nat)

/-- Arbitrary factor-vector weights follow the actual sequence of independent fresh batch laws. -/
lemma rsaMeasuredProbability_nextSequence_factorKernel (input : Input N) (length : Nat)
    (indices : Fin length → Fin count) (weight : (Fin count → Factor N) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    Circuit.forRangeReferenceKernel length
        (fun index => nextBatchParentReferenceKernel base N count (indices index))
        (fun after => weight (factorRead base N count after)) stored =
      ∑ values : List.Vector (Factor N) length,
        ((PMF.independentReplicateVector (batchDistribution input) length values).toReal : ℂ) *
          weight (factorUpdates length indices values
            (factorRead base N count stored)) := by
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
          (fun index => nextBatchParentReferenceKernel base N count (indices index.succ))
          (fun after => weight (factorRead base N count after)) =
          (fun after => tailWeight (factorRead base N count after)) := by
        funext after
        exact ih (fun index => indices index.succ) after
      rw [Circuit.forRangeReferenceKernel, tail,
        rsaMeasuredProbability_nextBatch_factorKernel base N count input,
        PMF.independentReplicateVector_weighted_cons]
      rfl

/-- The actual selector's complete parent destination supplies the final optional factor. -/
def selectedRead (stored : Store (Recycling.ClassicalFrame.context base N count)) : Factor N :=
  stored.read (FirstAccepted.cellRead (Recycling.ClassicalFrame.selectedRef base N count))

/-- The actual paid selection parent write reads exactly the chronological factor vector. -/
lemma rsaMeasuredProbability_selectionStore_output (laterCount : Nat)
    (stored : Store (Recycling.ClassicalFrame.context base N (laterCount + 1))) :
    selectedRead base N (laterCount + 1)
        (parentSelectionStore base N (laterCount + 1) stored) =
      FirstAccepted.Direct.Optional.Distribution.firstValue
        (List.ofFn (factorRead base N (laterCount + 1) stored)) :=
  Store.read_write_same stored _ _

/-- Every real later batch supplies a fresh factor after the preserved first result. -/
lemma rsaMeasuredProbability_laterBatches_selected (input : Input N) (laterCount : Nat)
    (weight : Factor N → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N (laterCount + 1))) :
    laterBatchesParentReferenceKernel base N laterCount
        (fun after => weight (selectedRead base N (laterCount + 1)
          (parentSelectionStore base N (laterCount + 1) after))) stored =
      ∑ values : List.Vector (Factor N) laterCount,
        ((PMF.independentReplicateVector (batchDistribution input) laterCount values).toReal : ℂ) *
          weight (FirstAccepted.Direct.Optional.Distribution.firstValue
            (factorRead base N (laterCount + 1) stored 0 :: values.toList)) := by
  have observed : (fun after => weight
      (selectedRead base N (laterCount + 1)
        (parentSelectionStore base N (laterCount + 1) after))) =
      (fun after => weight (FirstAccepted.Direct.Optional.Distribution.firstValue
        (List.ofFn (factorRead base N (laterCount + 1) after)))) := by
    funext after
    exact congrArg weight (rsaMeasuredProbability_selectionStore_output base N laterCount after)
  rw [observed]
  have actual := rsaMeasuredProbability_nextSequence_factorKernel base N (laterCount + 1) input
    laterCount Fin.succ
    (fun factors => weight (FirstAccepted.Direct.Optional.Distribution.firstValue
      (List.ofFn factors))) stored
  simpa only [laterBatchesParentReferenceKernel, rsaMeasuredProbability_factorUpdates_suffix]
    using actual

end

end QuantumAlg.Factoring.RSA.Measured.Program.Probability
