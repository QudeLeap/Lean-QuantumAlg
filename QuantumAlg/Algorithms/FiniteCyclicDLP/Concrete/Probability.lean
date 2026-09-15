/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.BornBridge.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected

/-!
# Born success floor for concrete finite-cyclic DLP

The selected hidden-line amplitudes are reconstructed at canonical clean-tail
basis states of the actual concrete program. Their lower bound is then summed
inside that program's terminal Born distribution. No probability model or
success-floor field is accepted.
-/

section

namespace QuantumAlg

open scoped BigOperators

noncomputable section

namespace FiniteCyclicDLP
namespace Concrete
namespace Probability

universe u

variable {G : Type u} [Group G]
variable {P : KnownOrderProblem G}

/-- Canonical clean-tail basis state for one generator-power fiber. -/
def selectedTail (A : ConcreteCircuitAccess P) (k : Fin P.order) :
    Fin (2 ^ A.tailEncoding.width) :=
  A.tailEncoding.encode (A.cleanTail (P.generator ^ k.val))

/-- Distinct generator powers in the declared order occupy distinct clean-tail
basis states. -/
theorem selectedTail_injective (A : ConcreteCircuitAccess P) :
    Function.Injective (selectedTail A) := by
  intro left right h
  have htail := A.tailEncoding.encode_injective h
  have hpower := A.cleanTail_injective htail
  have hmod := (pow_inj_mod).mp hpower
  apply Fin.ext
  simpa [P.order_eq_orderOf.symm, Nat.mod_eq_of_lt left.isLt,
    Nat.mod_eq_of_lt right.isLt] using hmod

/-- On one selected clean-tail fiber, the concrete post-oracle state has one
contributing left exponent for each source-range right exponent. -/
theorem postOracleVec_apply_selectedTail
    (input : FiniteCyclicDLP.Input P) (A : ConcreteCircuitAccess P)
    (left : Fin (2 ^ orderWidth P)) (right k : Fin P.order) :
    Concrete.BornBridge.postOracleVec A
        (Concrete.BornBridge.fullIndex A left
          ⟨right.val, right.isLt.trans_le (order_le_fourierModulus P)⟩
          (selectedTail A k)) =
      if left.val =
          (FiniteCyclicDLP.Probability.fiberLeft P input k right).val then
        invSqrtOrder P.order * invSqrtOrder P.order
      else 0 := by
  rw [Concrete.BornBridge.postOracleVec_apply]
  simp only [right.isLt, if_true]
  by_cases hleft : left.val < P.order
  · simp only [hleft, if_true]
    have htail :
        selectedTail A k =
            A.tailEncoding.encode
              (A.cleanTail
                (P.toSourceScope.oracleMultiplier left.val right.val)) ↔
          left.val =
            (FiniteCyclicDLP.Probability.fiberLeft P input k right).val := by
      constructor
      · intro h
        have hclean :
            A.cleanTail (P.generator ^ k.val) =
              A.cleanTail (P.toSourceScope.oracleMultiplier left.val right.val) :=
          A.tailEncoding.encode_injective h
        have hgroup :
            P.generator ^ k.val =
              P.toSourceScope.oracleMultiplier left.val right.val :=
          A.cleanTail_injective hclean
        have hiff :=
          (FiniteCyclicDLP.Probability.oracleMultiplier_eq_generator_pow_iff
            P input ⟨left.val, hleft⟩ right k).mp hgroup.symm
        exact congrArg Fin.val hiff
      · intro h
        have hfin :
            (⟨left.val, hleft⟩ : Fin P.order) =
              FiniteCyclicDLP.Probability.fiberLeft P input k right :=
          Fin.ext h
        have hgroup :
            P.toSourceScope.oracleMultiplier left.val right.val =
              P.generator ^ k.val := by
          rw [congrArg Fin.val hfin]
          exact FiniteCyclicDLP.Probability.oracleMultiplier_fiber P input k right
        simp [selectedTail, hgroup]
    rw [if_congr htail rfl rfl]
  · have hne :
        left.val ≠
          (FiniteCyclicDLP.Probability.fiberLeft P input k right).val := by
      intro h
      exact hleft
        (h ▸ (FiniteCyclicDLP.Probability.fiberLeft P input k right).isLt)
    simp [hleft, hne]

/-- Zero-extended selected-tail formula for an arbitrary raw right label. -/
theorem postOracleVec_apply_selectedTail_raw
    (input : FiniteCyclicDLP.Input P) (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P)) (k : Fin P.order) :
    Concrete.BornBridge.postOracleVec A
        (Concrete.BornBridge.fullIndex A left right (selectedTail A k)) =
      if hright : right.val < P.order then
        if left.val =
            (FiniteCyclicDLP.Probability.fiberLeft P input k
              ⟨right.val, hright⟩).val then
          invSqrtOrder P.order * invSqrtOrder P.order
        else 0
      else 0 := by
  by_cases hright : right.val < P.order
  · have h := postOracleVec_apply_selectedTail input A left
      (⟨right.val, hright⟩ : Fin P.order) k
    have hlift :
        (⟨(⟨right.val, hright⟩ : Fin P.order).val,
          (⟨right.val, hright⟩ : Fin P.order).isLt.trans_le
            (order_le_fourierModulus P)⟩ :
          Fin (2 ^ orderWidth P)) = right :=
      Fin.ext rfl
    rw [hlift] at h
    simpa [hright] using h
  · rw [Concrete.BornBridge.postOracleVec_apply]
    simp [hright]

/-- At a selected clean tail, the concrete-circuit amplitude is the same exact
hidden-line sum used by the finite-cyclic DLP analysis. -/
theorem circuitAmplitude_selectedTail_eq_sum
    (input : FiniteCyclicDLP.Input P) (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P)) (k : Fin P.order) :
    Concrete.BornBridge.circuitAmplitude A left right (selectedTail A k) =
      ∑ sourceRight : Fin P.order,
        FiniteCyclicDLP.Probability.selectedFiberTerm
          input left right k sourceRight := by
  classical
  unfold Concrete.BornBridge.circuitAmplitude
  rw [Finset.sum_comm]
  calc
    (∑ sourceRight : Fin (2 ^ orderWidth P),
        ∑ sourceLeft : Fin (2 ^ orderWidth P),
          star (invSqrtN (orderWidth P) *
              ω (orderWidth P) ^ (sourceLeft.val * left.val)) *
            star (invSqrtN (orderWidth P) *
              ω (orderWidth P) ^ (sourceRight.val * right.val)) *
            Concrete.BornBridge.postOracleVec A
              (Concrete.BornBridge.fullIndex A sourceLeft sourceRight
                (selectedTail A k))) =
      ∑ sourceRight : Fin (2 ^ orderWidth P),
        if hright : sourceRight.val < P.order then
          FiniteCyclicDLP.Probability.selectedFiberTerm input left right k
            ⟨sourceRight.val, hright⟩
        else 0 := by
      apply Finset.sum_congr rfl
      intro sourceRight _
      simp_rw [postOracleVec_apply_selectedTail_raw input A]
      by_cases hright : sourceRight.val < P.order
      · simp only [hright, dite_true]
        simp_rw [mul_ite, mul_zero]
        let selected : Fin (2 ^ orderWidth P) :=
          ⟨(FiniteCyclicDLP.Probability.fiberLeft P input k
              ⟨sourceRight.val, hright⟩).val,
            (FiniteCyclicDLP.Probability.fiberLeft P input k
              ⟨sourceRight.val, hright⟩).isLt.trans_le
                (order_le_fourierModulus P)⟩
        rw [Fintype.sum_eq_single selected]
        · simp [selected, FiniteCyclicDLP.Probability.selectedFiberTerm,
            Canonical.Probability.selectedFiberTerm]
        · intro other hne
          have hval :
              other.val ≠
                (FiniteCyclicDLP.Probability.fiberLeft P input k
                  ⟨sourceRight.val, hright⟩).val := by
            intro h
            exact hne (Fin.ext h)
          simp [hval]
      · simp [hright]
    _ = ∑ sourceRight : Fin P.order,
        FiniteCyclicDLP.Probability.selectedFiberTerm
          input left right k sourceRight :=
      FiniteCyclicDLP.Probability.sum_fin_fourierModulus_if_sourceRange P
        (FiniteCyclicDLP.Probability.selectedFiberTerm input left right k)

/-- The selected concrete amplitude has norm at least `1/(2q)`. -/
theorem one_div_two_fourierModulus_le_norm_circuitAmplitude_selected
    (input : FiniteCyclicDLP.Input P) (A : ConcreteCircuitAccess P)
    (unit : (ZMod P.order)ˣ) (tail : Fin P.order) :
    1 / (2 * (fourierModulus P : ℝ)) ≤
      ‖Concrete.BornBridge.circuitAmplitude A
        (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
        (FiniteCyclicDLP.Probability.selectedIndex P
          (-input.secret * (unit : ZMod P.order)))
        (selectedTail A tail)‖ := by
  rw [circuitAmplitude_selectedTail_eq_sum]
  rw [show
    (∑ sourceRight : Fin P.order,
      FiniteCyclicDLP.Probability.selectedFiberTerm input
        (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
        (FiniteCyclicDLP.Probability.selectedIndex P
          (-input.secret * (unit : ZMod P.order)))
        tail sourceRight) =
      ∑ sourceRight : Fin P.order,
        FiniteCyclicDLP.Probability.amplitudeScale P *
          FiniteCyclicDLP.Probability.selectedFiberPhase P input unit tail
            sourceRight by
    apply Finset.sum_congr rfl
    intro sourceRight _
    exact FiniteCyclicDLP.Probability.selectedFiberTerm_eq_scale_mul_phase
      P input unit tail sourceRight]
  rw [← Finset.mul_sum, norm_mul]
  have hmodulus : (0 : ℝ) < fourierModulus P := by
    unfold fourierModulus
    positivity
  have hscale :
      ‖FiniteCyclicDLP.Probability.amplitudeScale P‖ =
        (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) := by
    have hpow :
        ‖(((2 : ℝ) ^ orderWidth P : ℂ))‖ =
          (2 : ℝ) ^ orderWidth P := by
      rw [norm_pow]
      norm_num
    have horderNorm : ‖((P.order : ℝ) : ℂ)‖ = (P.order : ℝ) := by
      norm_num
    unfold FiniteCyclicDLP.Probability.amplitudeScale
    unfold Canonical.Probability.amplitudeScale
    rw [norm_mul, norm_inv, norm_inv, hpow, horderNorm, ← mul_inv]
    congr 2
    norm_num [fourierModulus, Nat.cast_pow]
  rw [hscale]
  calc
    1 / (2 * (fourierModulus P : ℝ)) =
        (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) *
          ((P.order : ℝ) / 2) := by
      have horder : (0 : ℝ) < P.order := by exact_mod_cast P.order_pos
      field_simp
    _ ≤ (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) *
        ‖∑ sourceRight : Fin P.order,
          FiniteCyclicDLP.Probability.selectedFiberPhase P input unit tail
            sourceRight‖ := by
      exact mul_le_mul_of_nonneg_left
        (FiniteCyclicDLP.Probability.half_order_le_norm_sum_selectedFiberPhase
          P input unit tail)
        (by positivity)

/-- Every selected recoverable outcome has the existing pointwise floor in
the actual concrete terminal Born distribution. -/
theorem selectedOutcomePointwiseLowerBound_le_bornProbability
    (input : FiniteCyclicDLP.Input P) (A : ConcreteCircuitAccess P)
    (unit : (ZMod P.order)ˣ) :
    FiniteCyclicDLP.Probability.selectedOutcomePointwiseLowerBound P ≤
      (Concrete.BornBridge.outcomePMF A)
        (FiniteCyclicDLP.Probability.selectedOutcome P input unit) := by
  classical
  have htail (tail : Fin P.order) :
      FiniteCyclicDLP.Probability.selectedTailPointwiseLowerBound P ≤
        ENNReal.ofReal
          (‖Concrete.BornBridge.circuitAmplitude A
            (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
            (FiniteCyclicDLP.Probability.selectedIndex P
              (-input.secret * (unit : ZMod P.order)))
            (selectedTail A tail)‖ ^ 2) := by
    have hamp :=
      one_div_two_fourierModulus_le_norm_circuitAmplitude_selected
        input A unit tail
    have hsquare :
        1 / (4 * (fourierModulus P : ℝ) ^ 2) ≤
          ‖Concrete.BornBridge.circuitAmplitude A
            (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
            (FiniteCyclicDLP.Probability.selectedIndex P
              (-input.secret * (unit : ZMod P.order)))
            (selectedTail A tail)‖ ^ 2 := by
      calc
        1 / (4 * (fourierModulus P : ℝ) ^ 2) =
            (1 / (2 * (fourierModulus P : ℝ))) ^ 2 := by
          field_simp
          ring
        _ ≤ ‖Concrete.BornBridge.circuitAmplitude A
            (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
            (FiniteCyclicDLP.Probability.selectedIndex P
              (-input.secret * (unit : ZMod P.order)))
            (selectedTail A tail)‖ ^ 2 :=
          (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hamp
    unfold FiniteCyclicDLP.Probability.selectedTailPointwiseLowerBound
      Canonical.Probability.selectedTailPointwiseLowerBound
    exact ENNReal.ofReal_le_ofReal hsquare
  unfold FiniteCyclicDLP.Probability.selectedOutcomePointwiseLowerBound
    Canonical.Probability.selectedRawOutcomePointwiseLowerBound
    FiniteCyclicDLP.Probability.selectedOutcome
  change
    P.order • Canonical.Probability.selectedTailPointwiseLowerBound P ≤
      (Concrete.BornBridge.outcomePMF A)
        (Concrete.BornBridge.measurementOutcome P
          (prodEquiv
            (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order),
              FiniteCyclicDLP.Probability.selectedIndex P
                (-input.secret * (unit : ZMod P.order)))))
  rw [Concrete.BornBridge.bornOutcomeProbability_eq_sourceMarginal]
  calc
    -- [E23, arxiv-v5.tex:233-255] sums the probability over every tail.
    P.order • FiniteCyclicDLP.Probability.selectedTailPointwiseLowerBound P =
        ∑ tail : Fin P.order,
          FiniteCyclicDLP.Probability.selectedTailPointwiseLowerBound P := by simp
    _ ≤ ∑ tail : Fin P.order,
        ENNReal.ofReal
          (‖Concrete.BornBridge.circuitAmplitude A
            (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
            (FiniteCyclicDLP.Probability.selectedIndex P
              (-input.secret * (unit : ZMod P.order)))
            (selectedTail A tail)‖ ^ 2) :=
      Finset.sum_le_sum fun tail _ => htail tail
    _ = (Finset.univ.image (selectedTail A)).sum
        (fun tail =>
          ENNReal.ofReal
            (‖Concrete.BornBridge.circuitAmplitude A
              (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
              (FiniteCyclicDLP.Probability.selectedIndex P
                (-input.secret * (unit : ZMod P.order))) tail‖ ^ 2)) := by
      rw [Finset.sum_image (selectedTail_injective A).injOn]
    _ ≤ ∑ tail : Fin (2 ^ A.tailEncoding.width),
        ENNReal.ofReal
          (‖Concrete.BornBridge.circuitAmplitude A
            (FiniteCyclicDLP.Probability.selectedIndex P (unit : ZMod P.order))
            (FiniteCyclicDLP.Probability.selectedIndex P
              (-input.secret * (unit : ZMod P.order))) tail‖ ^ 2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (by intro tail _; simp) ?_
      intro tail _ _
      exact bot_le

/-- The summed selected-family floor lies below the mass of that exact finite
family in the actual concrete terminal Born distribution. -/
theorem selectedOutcomeFamilyLowerBound_le_bornSelectedProbability
    (input : FiniteCyclicDLP.Input P) (A : ConcreteCircuitAccess P) :
    FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound P ≤
      (Concrete.BornBridge.outcomePMF A).toOuterMeasure
        {outcome |
          outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily P input} := by
  classical
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  let distribution := (Concrete.BornBridge.outcomePMF A)
  calc
    FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound P =
        ∑ _unit : (ZMod P.order)ˣ,
          FiniteCyclicDLP.Probability.selectedOutcomePointwiseLowerBound P := by
      simp [FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound,
        Canonical.Probability.selectedRawOutcomeFamilyLowerBound]
    _ ≤ ∑ unit : (ZMod P.order)ˣ,
        distribution (FiniteCyclicDLP.Probability.selectedOutcome P input unit) := by
      exact Finset.sum_le_sum fun unit _ =>
        selectedOutcomePointwiseLowerBound_le_bornProbability input A unit
    _ = (FiniteCyclicDLP.Probability.selectedOutcomeFamily P input).sum
        distribution := by
      change (∑ unit : (ZMod P.order)ˣ,
          distribution
            (Canonical.Probability.selectedRawOutcome P input unit)) =
        (Finset.univ.image
          (Canonical.Probability.selectedRawOutcome P input)).sum distribution
      rw [Finset.sum_image
        (FiniteCyclicDLP.Probability.selectedOutcome_injective P input).injOn]
    _ = (FiniteCyclicDLP.Probability.selectedOutcomeFamily P input).sum
        (Set.indicator
          {outcome |
            outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily P input}
          distribution) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      simp [houtcome]
    _ ≤ Finset.univ.sum
        (Set.indicator
          {outcome |
            outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily P input}
          distribution) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (by intro outcome _; simp) ?_
      intro outcome _ _
      by_cases hselected :
          outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily P input <;>
        simp [hselected]
    _ = (Concrete.BornBridge.outcomePMF A).toOuterMeasure
        {outcome |
          outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily P input} := by
      change Finset.univ.sum
          (Set.indicator
            {outcome |
              outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily P input}
            distribution) =
        distribution.toOuterMeasure
          {outcome |
            outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily P input}
      symm
      exact PMF.toOuterMeasure_apply_fintype distribution _

end Probability
end Concrete
end FiniteCyclicDLP

end

end QuantumAlg

end
