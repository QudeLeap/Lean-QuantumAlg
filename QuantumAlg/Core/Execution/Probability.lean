/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ExecutionState
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.BigOperators

/-!
# Probability distributions derived from actual execution blocks

The probability of a classical execution record is the trace of its quantum
block, as for the weighted mixed-state representation [dW19, qcnotes.tex:5381]
and measurement probabilities [dW19, qcnotes.tex:5409]. A normalized execution
state therefore determines a probability mass function without any independent
distribution witness. Deterministic classical processing pushes that same
distribution forward, including when several records have the same result.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D : Type} [Fintype C] [Fintype D] {R : Register}

/-- The probability distribution determined by a normalized state's quantum block traces. -/
public def toPMF (state : ExecutionState C R) (normalized : state.IsNormalized) : PMF C :=
  PMF.ofFintype (fun value => ENNReal.ofReal (state.block value).mass) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun value _ => (state.block value).mass_nonneg)]
    change ENNReal.ofReal state.mass = 1
    rw [normalized, ENNReal.ofReal_one])

/-- The probability of a record is exactly the mass of its actual execution block. -/
@[simp] theorem toPMF_apply (state : ExecutionState C R) (normalized : state.IsNormalized)
    (value : C) :
    state.toPMF normalized value = ENNReal.ofReal (state.block value).mass := rfl

/-- Supported records are precisely those with positive execution mass. -/
theorem mem_support_toPMF_iff (state : ExecutionState C R)
    (normalized : state.IsNormalized) (value : C) :
    value ∈ (state.toPMF normalized).support ↔ 0 < (state.block value).mass := by
  rw [PMF.mem_support_iff, toPMF_apply, ENNReal.ofReal_ne_zero_iff]

/-- Every mapped record sums the probabilities of exactly its contributing input records. -/
theorem mapClassical_block_mass [DecidableEq D] (state : ExecutionState C R)
    (f : C → D) (value : D) :
    ((state.mapClassical f).block value).mass =
      ∑ input, if f input = value then (state.block input).mass else 0 :=
  sum_fiber_trace state f value

/-- Finite deterministic classical processing preserves normalization. -/
theorem mapClassical_normalized [DecidableEq D] (state : ExecutionState C R)
    (normalized : state.IsNormalized) (f : C → D) :
    (state.mapClassical f).IsNormalized :=
  (state.mapClassical_mass f).trans normalized

/-- The derived probability distribution commutes with actual classical record updates. -/
theorem toPMF_mapClassical [DecidableEq D] (state : ExecutionState C R)
    (normalized : state.IsNormalized) (f : C → D) :
    (state.mapClassical f).toPMF (state.mapClassical_normalized normalized f) =
      (state.toPMF normalized).map f := by
  apply PMF.ext
  intro value
  rw [toPMF_apply, mapClassical_block_mass,
    ENNReal.ofReal_sum_of_nonneg (fun input _ => by
      split
      · exact (state.block input).mass_nonneg
      · exact le_rfl), PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro input _
  by_cases matched : f input = value
  · simp only [matched, if_true, toPMF_apply]
  · simp only [matched, Ne.symm matched, if_false, ENNReal.ofReal_zero]

end

end QuantumAlg.ExecutionState
