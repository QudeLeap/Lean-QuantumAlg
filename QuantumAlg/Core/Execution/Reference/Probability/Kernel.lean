/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# Readout laws for input-dependent finite probability kernels

Tracing a weighted reference fiber recovers the ordinary mass of each input
record. This is the bridge from a reference-safe transition equation to its
classical conditional output law.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C : Type} [Fintype C] {R Reference : Register}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Summing the diagonal reference fibers of an input-dependent real weight
is exactly the weighted sum of the actual classical block masses. -/
lemma referenceFiberSum_diagonal_weighted_mass
    (state : ExecutionState C (Register.prod R Reference)) (weight : C → ℝ) :
    (∑ reference : Reference.Index,
      referenceFiberSum state (fun entry _ => (weight entry : ℂ))
        reference reference).re =
      ∑ entry : C, weight entry * (state.block entry).mass := by
  have reordered :
      (∑ reference : Reference.Index, ∑ basis : R.Index,
        ∑ entry : C, (weight entry : ℂ) *
          (state.block entry).matrix (basis, reference) (basis, reference)) =
      ∑ entry : C, (weight entry : ℂ) *
        (∑ reference : Reference.Index, ∑ basis : R.Index,
          (state.block entry).matrix (basis, reference) (basis, reference)) := by
    calc
      _ = ∑ reference : Reference.Index, ∑ entry : C, ∑ basis : R.Index,
          (weight entry : ℂ) *
            (state.block entry).matrix (basis, reference) (basis, reference) := by
              apply Finset.sum_congr rfl
              intro reference _
              exact Finset.sum_comm
      _ = ∑ entry : C, ∑ reference : Reference.Index, ∑ basis : R.Index,
          (weight entry : ℂ) *
            (state.block entry).matrix (basis, reference) (basis, reference) :=
              Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum]
  have traceEntry (entry : C) :
      (∑ reference : Reference.Index, ∑ basis : R.Index,
        (state.block entry).matrix (basis, reference) (basis, reference)).re =
      (state.block entry).mass := by
    rw [Finset.sum_comm]
    simpa only [DensityOperator.mass, Matrix.trace, Matrix.diag,
      DensityOperator.marginalLeft_matrix] using
        (DensityOperator.marginalLeft_mass (state.block entry))
  change (∑ reference : Reference.Index, ∑ basis : R.Index,
    ∑ entry : C, (weight entry : ℂ) *
      (state.block entry).matrix (basis, reference) (basis, reference)).re = _
  rw [reordered, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro entry _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, traceEntry]

/-- A reference-safe fiber equation with an input-dependent finite probability
kernel determines the actual classical output PMF as a bind of the input PMF. -/
lemma toPMF_map_eq_bind_of_referenceFiberSum
    {D Outcome : Type} [Fintype D] [Finite Outcome] {S : Register}
    (initial : ExecutionState C (Register.prod R Reference))
    (final : ExecutionState D (Register.prod S Reference))
    (initialNormalized : initial.IsNormalized) (finalNormalized : final.IsNormalized)
    (read : D → Outcome) (kernel : C → PMF Outcome)
    (observed : ∀ value (left right : Reference.Index),
      referenceFiberSum final
        (fun entry _ => if read entry = value then 1 else 0)
        left right =
      referenceFiberSum initial
        (fun entry _ => ((kernel entry value).toReal : ℂ))
        left right) :
    (final.toPMF finalNormalized).map read =
      (initial.toPMF initialNormalized).bind kernel := by
  let : Fintype Outcome := Fintype.ofFinite Outcome
  apply PMF.ext
  intro value
  have massEquation :
      ((final.mapClassical read).block value).mass =
        ∑ entry : C, (kernel entry value).toReal * (initial.block entry).mass := by
    calc
      _ = (∑ reference : Reference.Index,
        referenceFiberSum final
          (fun entry _ => if read entry = value then 1 else 0)
          reference reference).re :=
            mapClassical_block_mass_referenceFiberSum final read value
      _ = (∑ reference : Reference.Index,
        referenceFiberSum initial
          (fun entry _ => ((kernel entry value).toReal : ℂ))
          reference reference).re := by
            congr 1
            apply Finset.sum_congr rfl
            intro reference _
            exact observed value reference reference
      _ = _ := referenceFiberSum_diagonal_weighted_mass initial
        (fun entry => (kernel entry value).toReal)
  have mapped := congrArg (fun distribution : PMF Outcome => distribution value)
    (ExecutionState.toPMF_mapClassical final finalNormalized read)
  rw [ExecutionState.toPMF_apply] at mapped
  calc
    ((final.toPMF finalNormalized).map read) value =
        ENNReal.ofReal (((final.mapClassical read).block value).mass) := mapped.symm
    _ = ENNReal.ofReal
          (∑ entry : C, (kernel entry value).toReal *
            (initial.block entry).mass) := congrArg ENNReal.ofReal massEquation
    _ = ∑ entry : C,
          (initial.toPMF initialNormalized) entry * kernel entry value := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun entry _ =>
              mul_nonneg ENNReal.toReal_nonneg (initial.block entry).mass_nonneg)]
            apply Finset.sum_congr rfl
            intro entry _
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal ((kernel entry).apply_ne_top value),
              ExecutionState.toPMF_apply, mul_comm]
    _ = ((initial.toPMF initialNormalized).bind kernel) value := by
          rw [PMF.bind_apply, tsum_fintype]

end

end QuantumAlg.ExecutionState
