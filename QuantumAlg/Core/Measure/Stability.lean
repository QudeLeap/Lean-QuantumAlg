/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Measure.Distribution
import Mathlib.Analysis.Real.Sqrt

/-!
# Stability of terminal Born probabilities

This module turns an `L²` distance between normalized finite-dimensional state
vectors into a bound on every event in a terminal computational-basis
measurement.  The bound is derived from the amplitudes of the two states; no
caller-supplied probability distribution or selected outcome enters the state
semantics.

The constant two is intentionally elementary rather than optimal.  First the
full `L¹` difference of the two computational-basis Born weight vectors is
bounded by twice the state-vector distance.  Restricting to an event and
pushing forward through a terminal readout can only decrease that bound.
-/

section

namespace QuantumAlg

noncomputable section

namespace BornWeight

/-- The difference of two scalar Born weights is controlled by the amplitude
distance times the sum of the amplitude norms. -/
theorem abs_norm_sq_sub_norm_sq_le (left right : ℂ) :
    |‖left‖ ^ 2 - ‖right‖ ^ 2| ≤
      ‖left - right‖ * (‖left‖ + ‖right‖) := by
  calc
    |‖left‖ ^ 2 - ‖right‖ ^ 2| =
        |(‖left‖ + ‖right‖) * (‖left‖ - ‖right‖)| := by
      rw [sq_sub_sq]
    _ = (‖left‖ + ‖right‖) * |‖left‖ - ‖right‖| := by
      rw [abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ (‖left‖ + ‖right‖) * ‖left - right‖ :=
      mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le left right)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖left - right‖ * (‖left‖ + ‖right‖) := by
      rw [mul_comm]

/-- The full `L¹` difference of the computational-basis Born weights of two
normalized vectors is at most twice their `L²` distance. -/
theorem sum_abs_norm_sq_sub_norm_sq_le_two_mul_norm_sub
    {R : Register} (left right : NormalizedVector R) :
    ∑ index : R.Index, |‖left index‖ ^ 2 - ‖right index‖ ^ 2| ≤
      2 * ‖(left : HilbertVector R) - (right : HilbertVector R)‖ := by
  have leftCauchy :
      (∑ index : R.Index, ‖left index - right index‖ * ‖left index‖) ≤
        ‖(left : HilbertVector R) - (right : HilbertVector R)‖ *
          ‖(left : HilbertVector R)‖ := by
    simpa [EuclideanSpace.norm_eq] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset R.Index)
        (fun index => ‖left index - right index‖)
        (fun index => ‖left index‖))
  have rightCauchy :
      (∑ index : R.Index, ‖left index - right index‖ * ‖right index‖) ≤
        ‖(left : HilbertVector R) - (right : HilbertVector R)‖ *
          ‖(right : HilbertVector R)‖ := by
    simpa [EuclideanSpace.norm_eq] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset R.Index)
        (fun index => ‖left index - right index‖)
        (fun index => ‖right index‖))
  calc
    ∑ index : R.Index, |‖left index‖ ^ 2 - ‖right index‖ ^ 2| ≤
        ∑ index : R.Index,
          ‖left index - right index‖ * (‖left index‖ + ‖right index‖) :=
      Finset.sum_le_sum fun index _ => abs_norm_sq_sub_norm_sq_le _ _
    _ =
        (∑ index : R.Index, ‖left index - right index‖ * ‖left index‖) +
          ∑ index : R.Index, ‖left index - right index‖ * ‖right index‖ := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤
        ‖(left : HilbertVector R) - (right : HilbertVector R)‖ *
            ‖(left : HilbertVector R)‖ +
          ‖(left : HilbertVector R) - (right : HilbertVector R)‖ *
            ‖(right : HilbertVector R)‖ :=
      add_le_add leftCauchy rightCauchy
    _ = 2 * ‖(left : HilbertVector R) - (right : HilbertVector R)‖ := by
      rw [left.norm_eq_one, right.norm_eq_one]
      ring

end BornWeight

namespace QubitLayout

/-- Real-valued expansion of the probability of an arbitrary basis event. -/
theorem basisPMF_toOuterMeasure_toReal {qubitCount : Nat}
    {layout : QubitLayout qubitCount} (state : QubitLayout.State layout)
    (event : Set (Fin (2 ^ qubitCount))) :
    ((QubitLayout.basisPMF state).toOuterMeasure event).toReal =
      ∑ basis : Fin (2 ^ qubitCount),
        event.indicator (fun index => ‖state.normalized index‖ ^ 2) basis := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro basis _
    by_cases member : basis ∈ event
    · simp [Set.indicator_of_mem member, QubitLayout.basisPMF_apply]
    · simp [Set.indicator_of_notMem member]
  · intro basis _
    by_cases member : basis ∈ event
    · simp [Set.indicator_of_mem member, QubitLayout.basisPMF_apply]
    · simp [Set.indicator_of_notMem member]

/-- Every computational-basis event for `left` has probability at most the
same event for `right` plus twice the distance between their normalized state
vectors. -/
theorem basisPMF_toOuterMeasure_le_add_normError {qubitCount : Nat}
    {layout : QubitLayout qubitCount} (left right : QubitLayout.State layout)
    (event : Set (Fin (2 ^ qubitCount))) :
    (QubitLayout.basisPMF left).toOuterMeasure event ≤
      (QubitLayout.basisPMF right).toOuterMeasure event +
        ENNReal.ofReal
          (2 * ‖(left.normalized : HilbertVector (Qubits qubitCount)) -
            (right.normalized : HilbertVector (Qubits qubitCount))‖) := by
  classical
  have realBound :
      ((QubitLayout.basisPMF left).toOuterMeasure event).toReal ≤
        ((QubitLayout.basisPMF right).toOuterMeasure event).toReal +
          2 * ‖(left.normalized : HilbertVector (Qubits qubitCount)) -
            (right.normalized : HilbertVector (Qubits qubitCount))‖ := by
    rw [basisPMF_toOuterMeasure_toReal, basisPMF_toOuterMeasure_toReal]
    calc
      (∑ basis : Fin (2 ^ qubitCount),
          event.indicator (fun index => ‖left.normalized index‖ ^ 2) basis) ≤
          ∑ basis : Fin (2 ^ qubitCount),
            (event.indicator (fun index => ‖right.normalized index‖ ^ 2) basis +
              |‖left.normalized basis‖ ^ 2 - ‖right.normalized basis‖ ^ 2|) := by
        apply Finset.sum_le_sum
        intro basis _
        by_cases member : basis ∈ event
        · simp only [Set.indicator_of_mem member]
          linarith [le_abs_self
            (‖left.normalized basis‖ ^ 2 - ‖right.normalized basis‖ ^ 2)]
        · simp only [Set.indicator_of_notMem member, zero_add]
          exact abs_nonneg _
      _ =
          (∑ basis : Fin (2 ^ qubitCount),
            event.indicator (fun index => ‖right.normalized index‖ ^ 2) basis) +
            ∑ basis : Fin (2 ^ qubitCount),
              |‖left.normalized basis‖ ^ 2 - ‖right.normalized basis‖ ^ 2| := by
        rw [Finset.sum_add_distrib]
      _ ≤
          (∑ basis : Fin (2 ^ qubitCount),
            event.indicator (fun index => ‖right.normalized index‖ ^ 2) basis) +
            2 * ‖(left.normalized : HilbertVector (Qubits qubitCount)) -
              (right.normalized : HilbertVector (Qubits qubitCount))‖ :=
        add_le_add (le_refl _)
          (BornWeight.sum_abs_norm_sq_sub_norm_sq_le_two_mul_norm_sub
            left.normalized right.normalized)
  have leftFinite :
      (QubitLayout.basisPMF left).toOuterMeasure event ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact (QubitLayout.basisPMF left).tsum_coe_indicator_ne_top event
  have rightFinite :
      (QubitLayout.basisPMF right).toOuterMeasure event ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact (QubitLayout.basisPMF right).tsum_coe_indicator_ne_top event
  apply (ENNReal.toReal_le_toReal leftFinite
    (ENNReal.add_ne_top.2 ⟨rightFinite, ENNReal.ofReal_ne_top⟩)).1
  rw [ENNReal.toReal_add rightFinite ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal]
  · exact realBound
  · positivity

end QubitLayout

namespace TerminalZMeasure

/-- A terminal event is exactly the corresponding preimage event in the
computational basis. -/
theorem outcomePMF_toOuterMeasure_eq_basis_preimage
    {totalQubits measuredQubits : Nat} {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (state : QubitLayout.State layout)
    (event : Set (Outcome measuredQubits)) :
    (measurement.outcomePMF state).toOuterMeasure event =
      (QubitLayout.basisPMF state).toOuterMeasure
        (measurement.readout ⁻¹' event) := by
  simpa only [outcomePMF] using
    PMF.toOuterMeasure_map_apply measurement.readout
      (QubitLayout.basisPMF state) event

/-- Every terminal Born event for `left` has probability at most the same
event for `right` plus twice the distance between their normalized vectors. -/
theorem outcomePMF_toOuterMeasure_le_add_normError
    {totalQubits measuredQubits : Nat} {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (left right : QubitLayout.State layout)
    (event : Set (Outcome measuredQubits)) :
    (measurement.outcomePMF left).toOuterMeasure event ≤
      (measurement.outcomePMF right).toOuterMeasure event +
        ENNReal.ofReal
          (2 * ‖(left.normalized : HilbertVector (Qubits totalQubits)) -
            (right.normalized : HilbertVector (Qubits totalQubits))‖) := by
  rw [outcomePMF_toOuterMeasure_eq_basis_preimage,
    outcomePMF_toOuterMeasure_eq_basis_preimage]
  exact QubitLayout.basisPMF_toOuterMeasure_le_add_normError left right _

/-- A supplied state-distance bound can be substituted into the terminal Born
event estimate. -/
theorem outcomePMF_toOuterMeasure_le_add_of_norm_sub_le
    {totalQubits measuredQubits : Nat} {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (left right : QubitLayout.State layout)
    (event : Set (Outcome measuredQubits)) {error : ℝ}
    (distanceBound :
      ‖(left.normalized : HilbertVector (Qubits totalQubits)) -
        (right.normalized : HilbertVector (Qubits totalQubits))‖ ≤ error) :
    (measurement.outcomePMF left).toOuterMeasure event ≤
      (measurement.outcomePMF right).toOuterMeasure event +
        ENNReal.ofReal (2 * error) := by
  refine (outcomePMF_toOuterMeasure_le_add_normError
    measurement left right event).trans ?_
  gcongr

end TerminalZMeasure

end

end QuantumAlg

end
