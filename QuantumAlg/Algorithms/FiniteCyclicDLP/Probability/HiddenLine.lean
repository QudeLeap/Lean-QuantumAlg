/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected
import QuantumAlg.Init
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base
public import QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Util.FiniteCyclicDLP
public import Mathlib.Data.ZMod.Basic
import all QuantumAlg.Core.Algorithm.QuantumState
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Util.Complex
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.PMF
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Access
import all QuantumAlg.Algorithms.FiniteCyclicDLP.BornBridge

/-!
# Canonical finite-cyclic DLP raw-outcome probability

This module identifies a finite family of raw terminal outcomes determined by
an advertised discrete logarithm and proves their one-attempt Born mass from
the canonical prepare-query-readout circuit.  It deliberately stops before
classical decoding, recovery, or verification.
-/

section

namespace QuantumAlg

open scoped BigOperators

noncomputable section

namespace FiniteCyclicDLP
namespace Canonical
namespace Probability

universe u

variable {G : Type u} [Group G]

private def selectedWorkspace {P : KnownOrderProblem G} (A : Access P)
    (k : Fin P.order) : Fin (2 ^ orderWidth P) :=
  A.ux.encode (P.generator ^ k.val)

private theorem selectedWorkspace_injective {P : KnownOrderProblem G}
    (A : Access P) : Function.Injective (selectedWorkspace A) := by
  intro left right h
  have hpower := A.ux.encode_injective h
  have hmod := (pow_inj_mod).mp hpower
  apply Fin.ext
  simpa [P.order_eq_orderOf.symm, Nat.mod_eq_of_lt left.isLt,
    Nat.mod_eq_of_lt right.isLt] using hmod

private theorem postUxVec_apply_selectedWorkspace
    {P : KnownOrderProblem G} (input : SecretInput P) (A : Access P)
    (a : Fin (2 ^ orderWidth P)) (b k : Fin P.order) :
    BornBridge.postUxVec A
        (tripleIndex a
          ⟨b.val, b.isLt.trans_le (order_le_fourierModulus P)⟩
          (selectedWorkspace A k)) =
      if a.val = (fiberLeft P input k b).val then
        invSqrtOrder P.order * invSqrtOrder P.order
      else
        0 := by
  rw [BornBridge.postUxVec_apply]
  simp only [b.isLt, if_true]
  by_cases ha : a.val < P.order
  · simp only [ha, if_true]
    have hencode :
        selectedWorkspace A k =
            A.ux.encode (P.toSourceScope.oracleMultiplier a.val b.val) ↔
          a.val = (fiberLeft P input k b).val := by
      constructor
      · intro h
        have hgroup :
            P.generator ^ k.val =
              P.toSourceScope.oracleMultiplier a.val b.val := by
          apply A.ux.encode_injective
          simpa [selectedWorkspace] using h
        have hiff :=
          (oracleMultiplier_eq_generator_pow_iff P input
            ⟨a.val, ha⟩ b k).mp hgroup.symm
        exact congrArg Fin.val hiff
      · intro h
        have hfin : (⟨a.val, ha⟩ : Fin P.order) = fiberLeft P input k b :=
          Fin.ext h
        have hgroup :
            P.toSourceScope.oracleMultiplier a.val b.val =
              P.generator ^ k.val := by
          rw [congrArg Fin.val hfin]
          exact oracleMultiplier_fiber P input k b
        simp [selectedWorkspace, hgroup]
    rw [if_congr hencode rfl rfl]
  · have hne : a.val ≠ (fiberLeft P input k b).val := by
      intro h
      exact ha (h ▸ (fiberLeft P input k b).isLt)
    simp [ha, hne]

private theorem postUxVec_apply_selectedWorkspace_raw
    {P : KnownOrderProblem G} (input : SecretInput P) (A : Access P)
    (a b : Fin (2 ^ orderWidth P)) (k : Fin P.order) :
    BornBridge.postUxVec A (tripleIndex a b (selectedWorkspace A k)) =
      if hb : b.val < P.order then
        if a.val = (fiberLeft P input k ⟨b.val, hb⟩).val then
          invSqrtOrder P.order * invSqrtOrder P.order
        else
          0
      else
        0 := by
  by_cases hb : b.val < P.order
  · have h := postUxVec_apply_selectedWorkspace input A a
      (⟨b.val, hb⟩ : Fin P.order) k
    have hlift :
        (⟨(⟨b.val, hb⟩ : Fin P.order).val,
          (⟨b.val, hb⟩ : Fin P.order).isLt.trans_le
            (order_le_fourierModulus P)⟩ : Fin (2 ^ orderWidth P)) = b :=
      Fin.ext rfl
    rw [hlift] at h
    simpa [hb] using h
  · rw [BornBridge.postUxVec_apply]
    simp [hb]


private theorem circuitAmplitude_selectedWorkspace_eq_sum
    {P : KnownOrderProblem G} (input : SecretInput P) (A : Access P)
    (left right : Fin (2 ^ orderWidth P)) (k : Fin P.order) :
    BornBridge.circuitAmplitude A left right (selectedWorkspace A k) =
      ∑ b : Fin P.order, selectedFiberTerm input left right k b := by
  classical
  unfold BornBridge.circuitAmplitude
  rw [Finset.sum_comm]
  calc
    (∑ b : Fin (2 ^ orderWidth P),
        ∑ a : Fin (2 ^ orderWidth P),
          star (invSqrtN (orderWidth P) *
              ω (orderWidth P) ^ (a.val * left.val)) *
            star (invSqrtN (orderWidth P) *
              ω (orderWidth P) ^ (b.val * right.val)) *
            BornBridge.postUxVec A
              (tripleIndex a b (selectedWorkspace A k))) =
      ∑ b : Fin (2 ^ orderWidth P),
        if hb : b.val < P.order then
          selectedFiberTerm input left right k ⟨b.val, hb⟩
        else
          0 := by
      apply Finset.sum_congr rfl
      intro b _
      simp_rw [postUxVec_apply_selectedWorkspace_raw input A]
      by_cases hb : b.val < P.order
      · simp only [hb, dite_true]
        simp_rw [mul_ite, mul_zero]
        let selected : Fin (2 ^ orderWidth P) :=
          ⟨(fiberLeft P input k ⟨b.val, hb⟩).val,
            (fiberLeft P input k ⟨b.val, hb⟩).isLt.trans_le
              (order_le_fourierModulus P)⟩
        rw [Fintype.sum_eq_single selected]
        · simp [selected, selectedFiberTerm]
        · intro other hne
          have hval :
              other.val ≠ (fiberLeft P input k ⟨b.val, hb⟩).val := by
            intro h
            exact hne (Fin.ext h)
          simp [hval]
      · simp [hb]
    _ = ∑ b : Fin P.order, selectedFiberTerm input left right k b :=
      sum_fin_fourierModulus_if_sourceRange P
        (selectedFiberTerm input left right k)

private theorem one_div_two_fourierModulus_le_norm_circuitAmplitude_selected
    (P : KnownOrderProblem G) (input : SecretInput P) (A : Access P)
    (unit : (ZMod P.order)ˣ) (tail : Fin P.order) :
    1 / (2 * (fourierModulus P : ℝ)) ≤
      ‖BornBridge.circuitAmplitude A
        (selectedIndex P (unit : ZMod P.order))
        (selectedIndex P (-input.secret * (unit : ZMod P.order)))
        (selectedWorkspace A tail)‖ := by
  rw [circuitAmplitude_selectedWorkspace_eq_sum]
  rw [show
    (∑ b : Fin P.order,
      selectedFiberTerm input
        (selectedIndex P (unit : ZMod P.order))
        (selectedIndex P (-input.secret * (unit : ZMod P.order)))
        tail b) =
      ∑ b : Fin P.order,
        amplitudeScale P * selectedFiberPhase P input unit tail b by
    apply Finset.sum_congr rfl
    intro b _
    exact selectedFiberTerm_eq_scale_mul_phase P input unit tail b]
  rw [← Finset.mul_sum, norm_mul]
  have horder : (0 : ℝ) < P.order := by exact_mod_cast P.order_pos
  have hmodulus : (0 : ℝ) < fourierModulus P := by
    unfold fourierModulus
    positivity
  have hscale :
      ‖amplitudeScale P‖ =
        (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) := by
    have hpow :
        ‖(((2 : ℝ) ^ orderWidth P : ℂ))‖ =
          (2 : ℝ) ^ orderWidth P := by
      rw [norm_pow]
      norm_num
    have horderNorm :
        ‖((P.order : ℝ) : ℂ)‖ = (P.order : ℝ) := by norm_num
    unfold amplitudeScale
    rw [norm_mul, norm_inv, norm_inv, hpow, horderNorm, ← mul_inv]
    congr 2
    norm_num [fourierModulus, Nat.cast_pow]
  rw [hscale]
  calc
    1 / (2 * (fourierModulus P : ℝ)) =
        (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) *
          ((P.order : ℝ) / 2) := by field_simp
    _ ≤ (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) *
        ‖∑ b : Fin P.order, selectedFiberPhase P input unit tail b‖ :=
      mul_le_mul_of_nonneg_left
        (half_order_le_norm_sum_selectedFiberPhase P input unit tail)
        (by positivity)

/-- Each selected raw outcome has the pointwise mass forced by the canonical
hidden-line amplitude.  The conclusion concerns the raw terminal PMF only. -/
theorem selectedRawOutcomePointwiseLowerBound_le_probability
    (P : KnownOrderProblem G) (input : SecretInput P) (A : Access P)
    (unit : (ZMod P.order)ˣ) :
    selectedRawOutcomePointwiseLowerBound P ≤
      (terminalMeasurement P).outcomePMF (BornBridge.evolvedState A)
        (selectedRawOutcome P input unit) := by
  have hmodulus : (0 : ℝ) < fourierModulus P := by
    unfold fourierModulus
    positivity
  have htail (tail : Fin P.order) :
      selectedTailPointwiseLowerBound P ≤
        ENNReal.ofReal
          (‖BornBridge.circuitAmplitude A
            (selectedIndex P (unit : ZMod P.order))
            (selectedIndex P (-input.secret * (unit : ZMod P.order)))
            (selectedWorkspace A tail)‖ ^ 2) := by
    have hamp :=
      one_div_two_fourierModulus_le_norm_circuitAmplitude_selected
        P input A unit tail
    have hsquare :
        1 / (4 * (fourierModulus P : ℝ) ^ 2) ≤
          ‖BornBridge.circuitAmplitude A
            (selectedIndex P (unit : ZMod P.order))
            (selectedIndex P (-input.secret * (unit : ZMod P.order)))
            (selectedWorkspace A tail)‖ ^ 2 := by
      calc
        1 / (4 * (fourierModulus P : ℝ) ^ 2) =
            (1 / (2 * (fourierModulus P : ℝ))) ^ 2 := by
          field_simp
          ring
        _ ≤ ‖BornBridge.circuitAmplitude A
            (selectedIndex P (unit : ZMod P.order))
            (selectedIndex P (-input.secret * (unit : ZMod P.order)))
            (selectedWorkspace A tail)‖ ^ 2 :=
          (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hamp
    unfold selectedTailPointwiseLowerBound
    exact ENNReal.ofReal_le_ofReal hsquare
  unfold selectedRawOutcomePointwiseLowerBound selectedRawOutcome
  rw [BornBridge.bornOutcomeProbability_eq_sourceMarginal]
  calc
    P.order • selectedTailPointwiseLowerBound P =
        ∑ tail : Fin P.order, selectedTailPointwiseLowerBound P := by simp
    _ ≤ ∑ tail : Fin P.order,
        ENNReal.ofReal
          (‖BornBridge.circuitAmplitude A
            (selectedIndex P (unit : ZMod P.order))
            (selectedIndex P (-input.secret * (unit : ZMod P.order)))
            (selectedWorkspace A tail)‖ ^ 2) :=
      Finset.sum_le_sum fun tail _ => htail tail
    _ = (Finset.univ.image (selectedWorkspace A)).sum
        (fun workspace =>
          ENNReal.ofReal
            (‖BornBridge.circuitAmplitude A
              (selectedIndex P (unit : ZMod P.order))
              (selectedIndex P (-input.secret * (unit : ZMod P.order)))
              workspace‖ ^ 2)) := by
      rw [Finset.sum_image (selectedWorkspace_injective A).injOn]
    _ ≤ ∑ workspace : Fin (2 ^ orderWidth P),
        ENNReal.ofReal
          (‖BornBridge.circuitAmplitude A
            (selectedIndex P (unit : ZMod P.order))
            (selectedIndex P (-input.secret * (unit : ZMod P.order)))
            workspace‖ ^ 2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (by intro workspace _; simp) ?_
      intro workspace _ _
      exact bot_le

/-- One canonical attempt assigns at least the explicit selected-family floor
to useful raw terminal outcomes.  This is not a classical recovery theorem. -/
theorem selectedRawOutcomeFamilyLowerBound_le_probability
    (P : KnownOrderProblem G) (input : SecretInput P) (A : Access P) :
    selectedRawOutcomeFamilyLowerBound P ≤
      ((terminalMeasurement P).outcomePMF
        (BornBridge.evolvedState A)).toOuterMeasure
        {outcome | SelectedRawOutcome P input outcome} := by
  classical
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  let distribution :=
    (terminalMeasurement P).outcomePMF (BornBridge.evolvedState A)
  calc
    selectedRawOutcomeFamilyLowerBound P =
        ∑ _unit : (ZMod P.order)ˣ,
          selectedRawOutcomePointwiseLowerBound P := by
      simp [selectedRawOutcomeFamilyLowerBound]
    _ ≤ ∑ unit : (ZMod P.order)ˣ,
        distribution (selectedRawOutcome P input unit) := by
      exact Finset.sum_le_sum fun unit _ =>
        selectedRawOutcomePointwiseLowerBound_le_probability
          P input A unit
    _ = (selectedRawOutcomeFamily P input).sum distribution := by
      rw [selectedRawOutcomeFamily,
        Finset.sum_image (selectedRawOutcome_injective P input).injOn]
    _ = (selectedRawOutcomeFamily P input).sum
        (Set.indicator {outcome | SelectedRawOutcome P input outcome}
          distribution) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      have houtcome' : outcome ∈
          Finset.univ.image (selectedRawOutcome P input) := by
        simpa [selectedRawOutcomeFamily] using houtcome
      rcases Finset.mem_image.mp houtcome' with ⟨unit, _hunit, rfl⟩
      simp [SelectedRawOutcome]
    _ ≤ Finset.univ.sum
        (Set.indicator {outcome | SelectedRawOutcome P input outcome}
          distribution) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (by intro outcome _; simp) ?_
      intro outcome _houtcome _houtside
      by_cases hselected : SelectedRawOutcome P input outcome <;>
        simp [hselected]
    _ = ((terminalMeasurement P).outcomePMF
          (BornBridge.evolvedState A)).toOuterMeasure
        {outcome | SelectedRawOutcome P input outcome} := by
      change Finset.univ.sum
          (Set.indicator {outcome | SelectedRawOutcome P input outcome}
            distribution) =
        distribution.toOuterMeasure
          {outcome | SelectedRawOutcome P input outcome}
      symm
      exact PMF.toOuterMeasure_apply_fintype distribution _



end Probability
end Canonical
end FiniteCyclicDLP

end

end QuantumAlg

end
