/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Measure
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Terminal Z-measurement distributions

This module derives computational-basis probability mass functions from the
amplitudes of normalized qubit states. A partial terminal measurement is the
map of that basis PMF through the descriptor's canonical big-endian readout.
No API accepts a selected outcome, an arbitrary probability kernel, or
hand-written probability weights.
-/

section

namespace QuantumAlg

noncomputable section

namespace QubitLayout

/-- Computational-basis PMF of a normalized qubit state. -/
def basisPMF {qubitCount : Nat} {layout : QubitLayout qubitCount}
    (state : QubitLayout.State layout) : PMF (Fin (2 ^ qubitCount)) :=
  PMF.ofFintype
    (fun outcome => ENNReal.ofReal (‖state.normalized outcome‖ ^ 2))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      rw [← EuclideanSpace.norm_sq_eq, state.normalized.norm_eq_one]
      norm_num)

@[simp] theorem basisPMF_apply {qubitCount : Nat}
    {layout : QubitLayout qubitCount} (state : QubitLayout.State layout)
    (outcome : Fin (2 ^ qubitCount)) :
    QubitLayout.basisPMF state outcome =
      ENNReal.ofReal (‖state.normalized outcome‖ ^ 2) := rfl

theorem basisPMF_total {qubitCount : Nat}
    {layout : QubitLayout qubitCount} (state : QubitLayout.State layout) :
    ∑' outcome, QubitLayout.basisPMF state outcome = 1 :=
  PMF.tsum_coe (QubitLayout.basisPMF state)

end QubitLayout

namespace TerminalZMeasure

/-- Big-endian readout of the logical qubits selected by a terminal descriptor. -/
def readout {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (basis : Fin (2 ^ totalQubits)) : Outcome measuredQubits :=
  fun outputIndex =>
    Nat.testBit basis.val
      (totalQubits - 1 - (measurement.logical_idx outputIndex).val)

/-- Decode a full-register big-endian terminal outcome back to its
computational-basis index. -/
public def fullRegisterIndex {qubitCount : Nat}
    (outcome : Fin qubitCount → Bool) : Fin (2 ^ qubitCount) :=
  ⟨Nat.ofBits (outcome ∘ Fin.rev), Nat.ofBits_lt_two_pow _⟩

/-- Full-register Z readout followed by the canonical big-endian decoder
recovers the measured computational-basis index. -/
@[simp] theorem fullRegisterIndex_zMeasure_readout {qubitCount : Nat}
    (layout : QubitLayout qubitCount) (basis : Fin (2 ^ qubitCount)) :
    fullRegisterIndex ((zMeasure layout).readout basis) = basis := by
  apply Fin.val_injective
  change Nat.ofBits (((zMeasure layout).readout basis) ∘ Fin.rev) = basis.val
  have hreadout :
      ((zMeasure layout).readout basis) ∘ Fin.rev =
        fun bit : Fin qubitCount => basis.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, readout, zMeasure, zMeasureAt, id_eq]
    apply congrArg basis.val.testBit
    calc
      qubitCount - 1 - (Fin.rev bit).val =
          qubitCount - ((Fin.rev bit).val + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hreadout, Nat.ofBits_testBit, Nat.mod_eq_of_lt basis.isLt]

/-- Terminal outcome PMF derived by mapping the normalized basis PMF through
the descriptor's canonical readout. -/
def outcomePMF {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (state : QubitLayout.State layout) : PMF (Outcome measuredQubits) :=
  PMF.map measurement.readout (QubitLayout.basisPMF state)

@[simp] theorem outcomePMF_apply {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (state : QubitLayout.State layout) (outcome : Outcome measuredQubits) :
    measurement.outcomePMF state outcome =
      ∑ basis with measurement.readout basis = outcome,
        ENNReal.ofReal (‖state.normalized basis‖ ^ 2) := by
  rw [outcomePMF, QubitLayout.basisPMF, PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply]
  refine Finset.sum_congr ?_ ?_
  · ext basis
    simp
  · intro basis hbasis
    rfl

/-- Terminal Born distributions depend only on the normalized mathematical
state; preparation-cost metadata attached to equal vectors is irrelevant. -/
theorem outcomePMF_congr_normalized {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    {left right : QubitLayout.State layout}
    (equal : left.normalized = right.normalized) :
    measurement.outcomePMF left = measurement.outcomePMF right := by
  apply PMF.ext
  intro outcome
  simp only [outcomePMF_apply]
  rw [equal]

theorem outcomePMF_total {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (state : QubitLayout.State layout) :
    ∑' outcome, measurement.outcomePMF state outcome = 1 :=
  PMF.tsum_coe (measurement.outcomePMF state)

end TerminalZMeasure

end

end QuantumAlg

end
