/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Core.Execution.Probability

/-!
# Probabilities from the same complete reference observations

Tracing the reference coordinates of an actual observed classical block gives
that block's probability mass. Consequently an equality of full-reference
weighted observations determines the actual finite output PMF. This bridge
uses the existing state and its trace-derived probability distribution; it
introduces no separate execution state or sampling semantics.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D Outcome : Type} [Fintype C] [Fintype D]
  {R S Reference : Register}

/-- The full trace of a constant reference observation is the same state's weighted mass. -/
theorem referenceFiberSum_sum_constant
    (state : ExecutionState C (Register.prod R Reference)) (coefficient : ℂ) :
    (∑ reference : Reference.Index,
      referenceFiberSum state (fun _ _ => coefficient) reference reference) =
        coefficient * (state.mass : ℂ) := by
  have traceSum :
      (∑ reference : Reference.Index, ∑ basis : R.Index, ∑ value : C,
        (state.block value).matrix (basis, reference) (basis, reference)) =
      state.quantumMarginal.matrix.trace := by
    have products := (Register.prodIndexEquiv R Reference).sum_comp
      (fun basis => ∑ value : C, (state.block value).matrix basis basis)
    have ordered := (Finset.sum_comm (f := fun reference : Reference.Index =>
      fun basis : R.Index => ∑ value : C,
        (state.block value).matrix (basis, reference) (basis, reference))).trans
      ((Fintype.sum_prod_type (fun pair : R.Index × Reference.Index =>
        ∑ value : C, (state.block value).matrix pair pair)).symm.trans products)
    simpa only [quantumMarginal, Matrix.trace, Matrix.diag, Matrix.sum_apply] using ordered
  have traceMass : state.quantumMarginal.matrix.trace = (state.mass : ℂ) :=
    Complex.ext (quantumMarginal_mass state) state.quantumMarginal.trace_im_eq_zero
  simp only [referenceFiberSum, ← Finset.mul_sum]
  exact congrArg (fun value : ℂ => coefficient * value) (traceSum.trans traceMass)

/-- Tracing every reference diagonal of a readout fiber gives its actual observed block mass. -/
theorem mapClassical_block_mass_referenceFiberSum [Fintype Outcome] [DecidableEq Outcome]
    (state : ExecutionState C (Register.prod R Reference)) (read : C → Outcome)
    (value : Outcome) :
    ((state.mapClassical read).block value).mass =
      (∑ reference : Reference.Index,
        referenceFiberSum state (fun entry _ => if read entry = value then 1 else 0)
          reference reference).re := by
  have traceOrder :
      ((state.mapClassical read).block value).mass =
        (∑ reference : Reference.Index, ∑ basis : R.Index,
          ((state.mapClassical read).block value).matrix
            (basis, reference) (basis, reference)).re := by
    have products := (Register.prodIndexEquiv R Reference).sum_comp
      (fun basis => ((state.mapClassical read).block value).matrix basis basis)
    have ordered := products.symm.trans
      ((Fintype.sum_prod_type (fun pair : R.Index × Reference.Index =>
        ((state.mapClassical read).block value).matrix pair pair)).trans Finset.sum_comm)
    exact congrArg Complex.re ordered
  refine traceOrder.trans (congrArg Complex.re ?_)
  apply Finset.sum_congr rfl
  intro reference _
  exact mapClassical_block_referenceFiberSum state read value reference reference

/-- Full-reference readout equations determine the actual trace-derived finite output PMF. -/
theorem toPMF_map_eq_of_referenceFiberSum [Finite Outcome] [DecidableEq Outcome]
    (initial : ExecutionState C (Register.prod R Reference))
    (final : ExecutionState D (Register.prod S Reference))
    (initialNormalized : initial.IsNormalized) (finalNormalized : final.IsNormalized)
    (read : D → Outcome) (distribution : PMF Outcome)
    (observed : ∀ value (leftRef rightRef : Reference.Index),
      referenceFiberSum final (fun entry _ => if read entry = value then 1 else 0)
          leftRef rightRef =
        referenceFiberSum initial (fun _ _ => ((distribution value).toReal : ℂ))
          leftRef rightRef) :
    (final.toPMF finalNormalized).map read = distribution := by
  let : Fintype Outcome := Fintype.ofFinite Outcome
  apply PMF.ext
  intro value
  have massEquation : ((final.mapClassical read).block value).mass =
      (distribution value).toReal := by
    refine (mapClassical_block_mass_referenceFiberSum final read value).trans ?_
    have entries := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun reference _ => observed value reference reference)
    have summed := entries.trans
      (referenceFiberSum_sum_constant initial ((distribution value).toReal : ℂ))
    have realEquation := congrArg Complex.re summed
    change initial.mass = 1 at initialNormalized
    simpa only [initialNormalized, Complex.ofReal_one, mul_one, Complex.ofReal_re]
      using realEquation
  have actual := congrArg (fun probability : PMF Outcome => probability value)
    (toPMF_mapClassical final finalNormalized read).symm
  exact actual.trans ((congrArg ENNReal.ofReal massEquation).trans
    (ENNReal.ofReal_toReal (distribution.apply_ne_top value)))

end

end QuantumAlg.ExecutionState
