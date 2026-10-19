/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ExecutionState
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite stochastic choices on complete execution blocks

A declared finite distribution may depend on the existing classical record,
including an oracle's internal state. Each outcome retains the complete
conditional quantum block multiplied by its actual probability. Summing the
outcomes preserves the original block and every reference correlation it holds.

This is a mathematical state transformation. Executable operations obtain their
distributions from the selected model and record their own native/query events.
No uniformity, independence from the classical record, or normalization of a
zero-probability branch is assumed here.
-/

namespace QuantumAlg.Execution

open scoped ComplexOrder

noncomputable section

private lemma finite_probability_sum {Outcome : Type} [Fintype Outcome]
    (distribution : PMF Outcome) : ∑ outcome, (distribution outcome).toReal = 1 := by
  have total : ∑ outcome, distribution outcome = 1 := by
    simpa only [tsum_fintype] using distribution.tsum_coe
  rw [← ENNReal.toReal_sum (fun outcome _ => distribution.apply_ne_top outcome),
    total, ENNReal.toReal_one]

private def weightBlock {R : Register} (state : DensityOperator R)
    {Outcome : Type} (distribution : PMF Outcome) (outcome : Outcome) :
    DensityOperator R where
  matrix := (distribution outcome).toReal • state.matrix
  positive := state.positive.smul ENNReal.toReal_nonneg
  trace_le_one := by
    simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    calc
      (distribution outcome).toReal * state.matrix.trace.re ≤
          (distribution outcome).toReal * 1 :=
        mul_le_mul_of_nonneg_left state.trace_le_one ENNReal.toReal_nonneg
      _ = (distribution outcome).toReal := mul_one _
      _ ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top (distribution.coe_le_one outcome)

private lemma weightBlock_mass {R : Register} (state : DensityOperator R)
    {Outcome : Type} (distribution : PMF Outcome) (outcome : Outcome) :
    (weightBlock state distribution outcome).mass =
      (distribution outcome).toReal * state.mass := by
  simp only [DensityOperator.mass, weightBlock, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul]

private lemma sum_weightBlock_mass {R : Register} (state : DensityOperator R)
    {Outcome : Type} [Fintype Outcome] (distribution : PMF Outcome) :
    ∑ outcome, (weightBlock state distribution outcome).mass = state.mass := by
  simp only [weightBlock_mass]
  rw [← Finset.sum_mul, finite_probability_sum, one_mul]

/-- Sample from the declared distribution at each complete classical record. -/
public def kernelChoice {C Outcome : Type} [Fintype C] [Fintype Outcome] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome) :
    ExecutionState (C × Outcome) R where
  block result := weightBlock (state.block result.1) (transition result.1) result.2
  total_le_one := by
    rw [Fintype.sum_prod_type]
    simp only [sum_weightBlock_mass]
    exact state.total_le_one

private lemma kernelChoice_block_matrix_proof
    {C Outcome : Type} [Fintype C] [Fintype Outcome] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome)
    (value : C) (outcome : Outcome) :
    ((kernelChoice state transition).block (value, outcome)).matrix =
      (transition value outcome).toReal • (state.block value).matrix := rfl

/-- The full conditional quantum matrix carries precisely the declared probability. -/
public lemma kernelChoice_block_matrix
    {C Outcome : Type} [Fintype C] [Fintype Outcome] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome)
    (value : C) (outcome : Outcome) :
    ((kernelChoice state transition).block (value, outcome)).matrix =
      (transition value outcome).toReal • (state.block value).matrix :=
  kernelChoice_block_matrix_proof state transition value outcome

/-- Stochastic classical execution preserves the complete subnormalized mass. -/
public lemma kernelChoice_mass
    {C Outcome : Type} [Fintype C] [Fintype Outcome] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome) :
    (kernelChoice state transition).mass = state.mass := by
  change (∑ result : C × Outcome,
    (weightBlock (state.block result.1) (transition result.1) result.2).mass) = _
  rw [Fintype.sum_prod_type]
  simp only [sum_weightBlock_mass, ExecutionState.mass]

/-- Forgetting the sampled classical label preserves every quantum and reference entry. -/
public lemma kernelChoice_quantumMarginal
    {C Outcome : Type} [Fintype C] [Fintype Outcome] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome) :
    (kernelChoice state transition).quantumMarginal = state.quantumMarginal := by
  apply DensityOperator.ext
  change (∑ result : C × Outcome,
    (transition result.1 result.2).toReal • (state.block result.1).matrix) =
      ∑ value, (state.block value).matrix
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro value _
  change (∑ outcome, (transition value outcome).toReal • (state.block value).matrix) =
    (state.block value).matrix
  rw [← Finset.sum_smul, finite_probability_sum, one_smul]

/-- An impossible sampled result has an exactly zero conditional operator. -/
public lemma kernelChoice_zero_probability
    {C Outcome : Type} [Fintype C] [Fintype Outcome] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome)
    (value : C) (outcome : Outcome) (impossible : transition value outcome = 0) :
    (kernelChoice state transition).block (value, outcome) = DensityOperator.zero R := by
  apply DensityOperator.ext
  rw [kernelChoice_block_matrix, impossible, ENNReal.toReal_zero, zero_smul,
    DensityOperator.zero_matrix]

end

end QuantumAlg.Execution
