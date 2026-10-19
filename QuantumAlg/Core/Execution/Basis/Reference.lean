/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Preparation
import all QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Core.Execution.State.Promise

/-!
# Basis-state targets with the complete incoming reference density

The target uses the existing pure-state tensor construction from physical
preparation. Exact output entries imply a mixed state promise weighted by
the actual output block's own mass, including an impossible output. Taking
the reference marginal here is only a mathematical observation. Restoration
of borrowed classical values jointly with that reference is a separate
execution obligation and is not replaced by this state promise.
-/

namespace QuantumAlg

noncomputable section

namespace ExecutionState

variable {C : Type} [Fintype C] {R Reference : Register}

/-- The complete external reference, summing the actual classical and local quantum labels. -/
def referenceMarginal (state : ExecutionState C (Register.prod R Reference)) :
    DensityOperator Reference :=
  DensityOperator.marginalLeft
    (DensityOperator.reindex (S := Register.prod Reference R) state.quantumMarginal
      (Equiv.prodComm R.Index Reference.Index))

/-- The reference observation retains the total probability of the same state. -/
lemma referenceMarginal_mass (state : ExecutionState C (Register.prod R Reference)) :
    state.referenceMarginal.mass = state.mass :=
  (DensityOperator.marginalLeft_mass _).trans
    ((DensityOperator.reindex_mass _ _).trans (quantumMarginal_mass state))

/-- A constant full-reference fiber is the same scalar times the actual reference marginal. -/
lemma referenceFiberSum_constant_eq
    (state : ExecutionState C (Register.prod R Reference)) (coefficient : ℂ)
    (left right : Reference.Index) :
    referenceFiberSum state (fun _ _ => coefficient) left right =
      coefficient * state.referenceMarginal.matrix left right := by
  simp only [referenceFiberSum, referenceMarginal, DensityOperator.marginalLeft_matrix,
    DensityOperator.reindex_entry, quantumMarginal, Matrix.sum_apply, ← Finset.mul_sum]
  rfl

end ExecutionState

namespace Execution.BasisReference

variable {R Reference : Register}

/-- Independent basis seed tensor the complete reference, using the unique preparation tensor. -/
def target (seed : R.Index) (reference : DensityOperator Reference) :
    DensityOperator (Register.prod R Reference) :=
  prependPrepared reference (NormalizedVector.ket seed)

/-- The basis factor has trace one, so the target retains exactly the reference mass. -/
lemma target_mass (seed : R.Index) (reference : DensityOperator Reference) :
    (target seed reference).mass = reference.mass :=
  prependPrepared_mass reference (NormalizedVector.ket seed)

/-- A normalized incoming reference gives a normalized independent joint target. -/
lemma target_normalized (seed : R.Index) (reference : DensityOperator Reference)
    (normalized : reference.IsNormalized) : (target seed reference).IsNormalized :=
  (target_mass seed reference).trans normalized

/-- Every target entry keeps both reference coordinates and fixes both local coordinates. -/
lemma target_entry (seed : R.Index) (reference : DensityOperator Reference)
    (left right : R.Index) (leftRef rightRef : Reference.Index) :
    (target seed reference).matrix (left, leftRef) (right, rightRef) =
      if left = seed ∧ right = seed then reference.matrix leftRef rightRef else 0 := by
  change ((NormalizedVector.ket seed) left * star ((NormalizedVector.ket seed) right)) *
    reference.matrix leftRef rightRef = _
  rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  by_cases first : left = seed <;> by_cases second : right = seed <;>
    simp only [first, second, and_self, and_false, false_and, if_true, if_false,
      star_one, star_zero, one_mul, zero_mul, mul_zero]

/-- A complete entry formula is precisely a scalar multiple of the independent target. -/
lemma matrix_eq_smul_of_entries (seed : R.Index) (reference : DensityOperator Reference)
    (state : DensityOperator (Register.prod R Reference)) (probability : ℝ)
    (entries : ∀ left right leftRef rightRef,
      state.matrix (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then
          (probability : ℂ) * reference.matrix leftRef rightRef else 0) :
    state.matrix = probability • (target seed reference).matrix := by
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  change state.matrix (left, leftRef) (right, rightRef) =
    probability • (target seed reference).matrix (left, leftRef) (right, rightRef)
  rw [entries, target_entry]
  split_ifs <;> simp only [Complex.real_smul, smul_zero]

/-- The exact joint entry formula establishes the existing mass-weighted mixed promise. -/
lemma promise_of_entries (seed : R.Index) (reference : DensityOperator Reference)
    (normalized : reference.IsNormalized)
    (state : DensityOperator (Register.prod R Reference)) (probability : ℝ)
    (entries : ∀ left right leftRef rightRef,
      state.matrix (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then
          (probability : ℂ) * reference.matrix leftRef rightRef else 0) :
    (StatePromise.mixed (target seed reference)
      (target_normalized seed reference normalized)).Holds state := by
  have matrixEquation := matrix_eq_smul_of_entries seed reference state probability entries
  have targetMass : (target seed reference).mass = 1 :=
    (target_mass seed reference).trans normalized
  have actualMass : state.mass = probability := by
    change state.matrix.trace.re = probability
    rw [matrixEquation, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    change probability * (target seed reference).mass = probability
    rw [targetMass, mul_one]
  change state.matrix = state.mass • (target seed reference).matrix
  exact matrixEquation.trans (congrArg
    (fun coefficient : ℝ => coefficient • (target seed reference).matrix) actualMass.symm)

end Execution.BasisReference

end

end QuantumAlg
