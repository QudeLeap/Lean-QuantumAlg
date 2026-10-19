/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Born
import all QuantumAlg.Core.Measure.Distribution

/-!
# The runtime source-amplitude fibers are the original outcome probabilities

The physical basis equivalence transports the finite squared-amplitude sum
without changing any value. Summing exactly the labels with a given source
readout is the existing Born outcome PMF. This scalar identity connects the
full store-reference formulas to the source probability analysis; it does
not substitute a PMF for the actual Z instructions.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Each physical measurement fiber has precisely the source compiled outcome probability. -/
lemma shortDLP_runtimeBorn_outcome_weight (N : Nat) (generator target : (ZMod N)ˣ)
    (outcome : TerminalZMeasure.Outcome (firstBits (registerParameters m ell width) + ell)) :
    (∑ basis : ctx.register.Index,
      if (ShortDLP.measurement (registerParameters m ell width)).readout
          (basisEquiv m ell width sameWires basis) = outcome then
        ‖(CompiledMAU.evolvedState m ell width N generator target).normalized
          (basisEquiv m ell width sameWires basis)‖ ^ 2 else 0) =
      ((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
        (CompiledMAU.evolvedState m ell width N generator target) outcome).toReal := by
  let measure := ShortDLP.measurement (registerParameters m ell width)
  let source := CompiledMAU.evolvedState m ell width N generator target
  have transported := (basisEquiv m ell width sameWires).sum_comp
    (fun basis => if measure.readout basis = outcome then ‖source.normalized basis‖ ^ 2 else 0)
  have sourceProbability := congrArg ENNReal.toReal
    (TerminalZMeasure.outcomePMF_apply measure source outcome)
  have finite :
      (∑ basis with measure.readout basis = outcome,
        ENNReal.ofReal (‖source.normalized basis‖ ^ 2)).toReal =
      ∑ basis with measure.readout basis = outcome, ‖source.normalized basis‖ ^ 2 := by
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro basis _
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  exact transported.trans ((Finset.sum_filter (s := Finset.univ)
    (fun basis => measure.readout basis = outcome)
    (fun basis => ‖source.normalized basis‖ ^ 2)).symm.trans
      (sourceProbability.trans finite).symm)

/-- On the original arithmetic domain, the same actual fiber equals the ideal source PMF. -/
lemma shortDLP_runtimeBorn_ideal_outcome_weight (N : Nat) (generator target : (ZMod N)ˣ)
    (nontrivial : 1 < N) (capacity : N < 2 ^ width)
    (outcome : TerminalZMeasure.Outcome (firstBits (registerParameters m ell width) + ell)) :
    (∑ basis : ctx.register.Index,
      if (ShortDLP.measurement (registerParameters m ell width)).readout
          (basisEquiv m ell width sameWires basis) = outcome then
        ‖(CompiledMAU.evolvedState m ell width N generator target).normalized
          (basisEquiv m ell width sameWires basis)‖ ^ 2 else 0) =
      ((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
        (BornProbability.evolvedState (unitEncoding width N nontrivial capacity)
          generator target) outcome).toReal :=
  (shortDLP_runtimeBorn_outcome_weight m ell width sameWires N generator target outcome).trans
    (congrArg (fun distribution => (distribution outcome).toReal)
      (CompiledMAU.outcomePMF_eq_ideal m ell width N generator target nontrivial capacity))

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement
