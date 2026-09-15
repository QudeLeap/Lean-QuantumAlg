/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Measure.Distribution

/-!
# Real finite weights of the computational-basis Born law

The existing normalized-state outcome PMF has exactly the finite sum of
squared amplitudes in each readout fiber. This is a scalar mathematical
identity about that distribution, with no additional execution or state.
-/

namespace QuantumAlg.TerminalZMeasure

noncomputable section

/-- The real value of the Born outcome is the exact finite squared-amplitude fiber. -/
theorem outcomePMF_toReal {total measured : Nat} {layout : QubitLayout total}
    (measurement : TerminalZMeasure layout measured) (state : QubitLayout.State layout)
    (outcome : Outcome measured) :
    (measurement.outcomePMF state outcome).toReal =
      ∑ basis : Fin (2 ^ total), if measurement.readout basis = outcome then
        ‖state.normalized basis‖ ^ 2 else 0 := by
  classical
  have actual := congrArg ENNReal.toReal (outcomePMF_apply measurement state outcome)
  refine actual.trans ?_
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  have finite :
      (∑ basis with measurement.readout basis = outcome,
        (ENNReal.ofReal (‖state.normalized basis‖ ^ 2)).toReal) =
        ∑ basis with measurement.readout basis = outcome, ‖state.normalized basis‖ ^ 2 :=
    Finset.sum_congr rfl fun basis _ => ENNReal.toReal_ofReal (sq_nonneg _)
  exact finite.trans (Finset.sum_filter (s := Finset.univ)
    (fun basis => measurement.readout basis = outcome)
    (fun basis => ‖state.normalized basis‖ ^ 2))

end

end QuantumAlg.TerminalZMeasure
